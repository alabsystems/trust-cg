// trust-cg-opt - The one loop-state contract for rewrites that skip scalar iterations
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! # The loop-state contract
//!
//! Many passes here run new code INSTEAD OF some of a scalar loop's
//! iterations. A vectorizer or unroller splices a main loop in front of the
//! scalar loop and keeps the scalar loop as the remainder. An idiom rewrite
//! replaces the whole loop with a closed form. Each such rewrite states once
//! that the memory it writes is the memory the skipped iterations would have
//! written. Control and registers need a second rule, and this module is the
//! only place it is stated:
//!
//! > A rewrite that runs new code instead of a scalar loop's iterations is a
//! > refinement only if
//! >
//! > 1. **control**: every way the scalar loop can leave is one the new code
//! >    reproduces, or one the pass proves no replaced iteration takes;
//! > 2. **registers**: every register the scalar loop carries across its back
//! >    edge, or leaves live at an exit, is one the new code reproduces; and
//! > 3. **iterations**: the new code and the scalar remainder together run
//! >    exactly the iterations the scalar loop runs.
//!
//! [`loop_state_escapes`] decides the first two, once, for both machine IRs,
//! through [`LoopStateView`], on the loop before the rewrite.
//! [`coverage::check_coverage`] decides the third on the rewritten code
//! before it is published ([`publish_covered`]); see "Iterations". A rewrite
//! that keeps every iteration but deletes register work it judges dead (a full
//! unroll's trip test) asks [`DeadWork::check`]; see "Deleted register work".
//!
//! ## Control
//!
//! The loop's exits are enumerated here, not by the pass ([`loop_exits`]):
//! every transfer from a loop block to a block outside the loop (a branch, a
//! fall-through, a conditional trap that names its target block) and every
//! instruction that can end the loop with no successor block (a return, a
//! trap, a conditional trap carrier, an indirect branch). The plan accounts
//! for each one in an [`ExitPlan`]:
//!
//! * **The loop test** whose bound the new code's trip count is computed from
//!   ([`ExitPlan::loop_test`]). The new code runs only iterations in which the
//!   test continues, and gives control back before the first in which it
//!   leaves.
//! * **A reproduced exit** ([`ExitPlan::and_reproduces`]): the new code
//!   evaluates the exit's own condition for every iteration it replaces, and
//!   leaves through it, or gives control back to the scalar loop before the
//!   first iteration that would take it (an early-exit search's match).
//! * **An exit proved not taken** ([`ExitPlan::and_proved_not_taken`]): the
//!   pass proves that no iteration its new code replaces takes it (a bounds
//!   check against the loop test's own bound, or a pre-guard on the new code's
//!   entry). That proof is a premise of the pass, like the memory obligation,
//!   and is claimed only beside a test in which the same loop with the proof's
//!   premise broken is refused.
//!
//! Any other exit is refused ([`LoopStateEscape::Exit`]). The iterations the
//! new code replaces never reach a `break`, a `return`, a bounds-check panic
//! or a trap the plan does not account for, so the new code would run past
//! it. Measured before this clause existed (aarch64, O2 and O3): `neon_fill`
//! vectorized `while i < n { if i == stop { break } a[i] = 7; i += 1 }` and
//! returned `n` instead of `stop`, and over a 64-byte slice with `n = 1000`
//! stored about 900 bytes past the slice before the scalar remainder reached
//! the bounds-check panic. A diverging exit is not exempt: the panic message,
//! the panic hook and the memory written before it are all observable.
//!
//! A claim that is not an exit of the loop, or an edge that two transfers
//! share (so a claim could not tell them apart), is refused too
//! ([`LoopStateEscape::NotAnExit`], [`LoopStateEscape::Exit`]).
//!
//! ## Registers
//!
//! The new code reproduces a small declared set, `carried`: the induction
//! variable, and the accumulators the rewrite folds its partial results into.
//! Any other register the loop writes is left stale, holding the value it had
//! before the skipped iterations. That is harmless only if nothing reads the
//! stale value. Every register an instruction of the loop may write, other
//! than `carried`, must be dead on entry to the loop header and dead on entry
//! to every block control can leave the loop to.
//!
//! * **The header half.** After the new code skips iterations it hands control
//!   back to the scalar header. A register live into the header is either
//!   carried across the back edge (a second accumulator: `if a[i] == 0 {
//!   count += 1; sum += i }` loses every skipped `sum` update), or read on a
//!   path from the header to an exit before the loop writes it again (a
//!   live-out value such as `last = i`, which is wrong whenever the scalar
//!   remainder runs zero iterations).
//! * **The exit half.** New code may hand off straight to an exit. A rotated
//!   loop's remainder guard jumps to the true exit when nothing remains,
//!   without running the header. A register live into an exit is then read
//!   stale even when the header or the body would have recomputed it.
//!
//! Both halves are one question: is any stale register live where the new
//! code hands control back? [`Handoff`] names where that is.
//!
//! * [`Handoff::HeaderOrExit`], the default, checks the header AND every
//!   block control can leave the loop to. It over-approximates the hand-off
//!   set of any rewrite that resumes at the header or an exit, so the verdict
//!   does not depend on the pass describing its own splice. A hand-off into
//!   any other block of the loop is outside it: the coverage clause refuses
//!   one into a kept scalar remainder; a rewrite not routed through that
//!   clause is taken on its word. The cost is refusing a loop whose exit
//!   reads a value the header recomputes on every path there. It fails
//!   closed.
//! * [`Handoff::Header`] checks only the header. That is exact for a rewrite
//!   whose new code resumes ONLY at the scalar header, because every path from
//!   there, to every exit, runs the scalar code on correct state. It is a
//!   premise about the pass's splice, so a pass may claim it only with a test
//!   that its rewritten CFG leaves the new blocks for the header alone
//!   ([`hands_off_only_to`]).
//! * [`Handoff::Only`] checks exactly the blocks a whole-loop replacement
//!   leaves to (the matmul nest's one exit, never its abort paths). The same
//!   premise, the same test.
//! * [`Handoff::Exits`] checks every exit and not the header: a rewrite that
//!   runs its new code AS the loop (the in-place vectorizer), whose back-edge
//!   state is its own, is observed only once control leaves.
//!
//! A register the new code leaves untouched is also reproduced when the scalar
//! loop provably leaves it holding its entry value too (a value the loop only
//! copies out and back). A pass that proves that may list it in `carried`; the
//! proof is the pass's, stated where it lists it.
//!
//! A register can be reproduced at the header and not at an exit. The
//! rotated loop clang emits is the case: its test leaves from the header
//! BEFORE the latch writes the loop's values back, so the scalar loop exits
//! holding each written-back register's value from its last iteration, while
//! new code that runs that iteration whole and then branches straight to the
//! exit holds the written-back one. [`LoopLocality::check_rotated`] finds
//! those registers itself (`written_after_the_test`): every carried
//! register a loop instruction may write after its test transfers out,
//! which a pass cannot leave off a list. Measured (aarch64, O2 and O3):
//!
//! * `neon_map` vectorized `i = 20; loop { y[i] += 5; if i + 1 >= n {
//!   return i } i += 1 }` and returned 36 for `n = 36` (want 35);
//! * `neon_array`, which named only `i` stale, vectorized `i = 0; acc = 0;
//!   loop { sum = acc + a[i]; if i + 1 >= n { *out = acc; return }
//!   acc = sum; i += 1 }` over `a[x] = 3x + 1` and stored 376 for `n = 16`,
//!   the full sum, where the scalar loop stores 330, the sum without `a[15]`.
//!
//! **Condition flags** are a register. They are always tracked, because no
//! rewrite reproduces them. A loop whose flags are live into its header or an
//! exit is refused.
//!
//! **Unmodeled register effects.** An instruction of the loop that names a
//! physical register, or has register effects its operands do not show (a
//! call, a `Phi`, x86 `RDX:RAX` division, a `CL`-count shift, `PBLENDVB`'s
//! `XMM0` mask), makes the loop's state impossible to enumerate. Such a loop
//! is refused outright.
//!
//! **Register identity.** A read observes a tracked virtual register when it
//! names the same register number in any class, so a narrower view counts as
//! a read. A write ends a path only when it defines exactly the tracked
//! register, same number and same class, and the IR's own def model says the
//! write replaces the value (AArch64 operand roles; the x86 def model the
//! register allocator shares). Both choices fail closed. An x86 value
//! producer reads its destination only in a tied form (`x86_dce`'s per-form
//! `redef_reads_operand0`).
//!
//! ## Iterations
//!
//! The first two clauses read the loop; they cannot see what the new code
//! computes. `vectorize` passed both and still divided its own induction's trip
//! bound (16 of 64 lanes, fixed privately in `4b1fb93c7`), left remainder lanes
//! in blocks nothing branched to, and ran an undivided bound past an odd trip
//! count, a nonzero start and an inclusive test (`a0603f3bc`). The third
//! clause runs the rewritten code: [`LoopLocality::check_covered`] records the
//! loop, its preheader, its loop test and its reproduced registers in a
//! [`CoveredLoop`], and [`publish_covered`] rewrites a copy of the function and
//! publishes it only when [`coverage::check_coverage`] finds, for every input
//! it runs, that the new code (each entry into a block the rewrite names
//! counting the iterations it claims, [`Lanes`]) plus the scalar remainder run
//! as many iterations as the scalar loop, leave the same way, and leave the
//! reproduced registers equal. How it runs both functions, which inputs, and
//! what that decides are the [`coverage`] module's docs.
//!
//! ## Deleted register work
//!
//! A full unroll runs every iteration and replaces none, so the first two
//! clauses do not apply to it; but it deletes each copy's trip test, and
//! `loop_unroll`'s bounded-early-exit tier deleted one an exit still read and
//! folded away an address a store at the exit used (`e6dbb93df`, which checked
//! it privately). [`DeadWork::check`] states the rule once: every register a
//! deleted instruction may write, the flags included, is unread on every path
//! from just after it until an instruction the rewrite keeps replaces it,
//! deleted instructions reading and replacing nothing, and a read the rewrite
//! removes from an instruction it keeps (a re-pointed operand) named by the
//! pass. An instruction with register effects the model cannot name, other
//! than a call, counts as a reader of the flags (unless it is a return: no
//! AArch64 or x86-64 return convention carries them) and of every virtual
//! register it names; it cannot read one it does not name, since a virtual
//! register appears only in operands ([`LoopStateView::names_virtual`]). An
//! indirect branch, or a block that ends with no successor other than by a
//! return or a trap, also counts as a reader.
//!
//! ## What the contract does not decide
//!
//! Memory: each pass states that the memory its new code writes and reads is
//! what the replaced iterations write and read, and what each counted block
//! does with the iterations it claims. The proof behind an
//! [`ExitPlan::and_proved_not_taken`] claim, and that the loop test a plan
//! names is the one its trip count really comes from, are the pass's
//! recognizer premises; the contract only refuses an exit nobody accounts
//! for. A value a deletion re-points (a full unroll's per-copy constant) is
//! the pass's to prove equal.
//!
//! **Token.** [`LoopLocality`] is minted only by [`LoopLocality::check`]
//! (and [`LoopLocality::check_in`], its verdicts over a shared
//! [`LoopStateIndex`]) and [`LoopLocality::check_rotated`]; [`CoveredLoop`]
//! only by [`LoopLocality::check_covered`] (and
//! [`LoopLocality::check_covered_in`]); [`DeadWork`] only by
//! [`DeadWork::check`]. Each rewrite's plan holds one, so its apply step
//! cannot run on a loop that did not pass the check. A pass that holds a
//! [`CoveredLoop`] publishes through [`publish_covered`]; which passes do is
//! listed in `coverage_routes.txt` and checked by a test.
//!
//! **Evidence rung.** Tests. The table test in this module runs every row over
//! both [`LoopStateView`] impls; the coverage clause's rows are in
//! `coverage/tests.rs`. Whole-program runs against LLVM live in the bridge's
//! `tests/opt_loop_state_run.rs`. Nothing here is a proof. The token is a
//! type-level guarantee that the check ran, not that the check is right; the
//! coverage clause runs the rewritten code on sampled inputs, a decision only
//! for the inputs it runs.

use std::fmt::Debug;
use std::hash::Hash;

use crate::fast_hash::{FxHashMap as HashMap, FxHashSet as HashSet};
use trust_cg_ir::{AArch64Opcode, MachFunction, MachOperand, VReg, X86CondCode, X86Opcode};
use trust_cg_lower::{X86ISelFunction, X86ISelInst, X86ISelOperand};

use crate::effects::{
    FlagOverwrite, condition_flag_overwrite, for_each_inst_def, for_each_inst_use, nzcv_unknown,
    reads_nzcv, writes_flags, x86_may_defined_vregs, x86_produces_value, x86_reads_flags,
};
use crate::mach_view::MachIrView;

pub(crate) mod coverage;
mod trip_aarch64;
mod trip_x86;

pub(crate) use coverage::{
    CoverageEscape, CoverageFrame, Lanes, Remainder, TripEffect, check_coverage, check_coverage_in,
};

/// A register the loop-state rule tracks.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum StateReg {
    /// A virtual register.
    Virtual(VReg),
    /// The condition flags (AArch64 NZCV, x86 RFLAGS).
    Flags,
}

impl StateReg {
    /// Whether a read of `self` may observe the value of `tracked`. A virtual
    /// register read observes every class with the same number.
    fn observes(self, tracked: StateReg) -> bool {
        match (self, tracked) {
            (StateReg::Virtual(read), StateReg::Virtual(tracked)) => read.id == tracked.id,
            (StateReg::Flags, StateReg::Flags) => true,
            _ => false,
        }
    }
}

/// How one instruction writes a register.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum StateWrite {
    /// The register's whole value is replaced. A path that reaches this write
    /// no longer observes the earlier value.
    Replaces,
    /// Part of the register may change. The earlier value may still be
    /// observed after this write.
    MayModify,
}

/// The register reads and writes of one machine IR, as the loop-state rule
/// needs them.
///
/// The CFG queries come from [`MachIrView`].
pub(crate) trait LoopStateView: MachIrView {
    /// Visit every register instruction `index` of `block` may read.
    fn visit_state_reads(&self, block: Self::Block, index: usize, visit: &mut dyn FnMut(StateReg));

    /// Visit every register instruction `index` of `block` may write.
    fn visit_state_writes(
        &self,
        block: Self::Block,
        index: usize,
        visit: &mut dyn FnMut(StateReg, StateWrite),
    );

    /// Whether the instruction has register effects the two visitors cannot
    /// name: a physical register operand, or an implicit register read or
    /// write.
    fn has_unmodeled_register_effect(&self, block: Self::Block, index: usize) -> bool;

    /// Whether the instruction names virtual register `reg` (by number) in any
    /// operand, or is a phi. A virtual register appears nowhere else: a
    /// physical register operand or an implicit register effect never reads
    /// one, so an instruction with unmodeled register effects that does not
    /// name `reg` cannot read it.
    fn names_virtual(&self, block: Self::Block, index: usize, reg: VReg) -> bool;

    /// Whether the instruction can end the loop with no successor block the
    /// CFG names: a return, a trap, a conditional trap carrier that names no
    /// target block, or an indirect branch (whose targets cannot be named).
    fn ends_without_successor(&self, block: Self::Block, index: usize) -> bool;

    /// Whether the instruction is a call (it reads only its operands, writes
    /// the flags, and returns to the next instruction).
    fn is_call(&self, block: Self::Block, index: usize) -> bool;

    /// Whether the instruction is an indirect branch (its targets cannot be
    /// named).
    fn is_indirect_branch(&self, block: Self::Block, index: usize) -> bool;

    /// Append the effects of instruction `index` of `block` on what the
    /// iteration-coverage clause tracks ([`coverage::TripEffect`]): the values
    /// it writes, the flags, and where control goes. An instruction the model
    /// does not compute writes unknown values to what it defines.
    fn trip_effects(
        &self,
        block: Self::Block,
        index: usize,
        out: &mut Vec<coverage::TripEffect<Self::Block>>,
    );

    /// Whether instruction `index` of `block` is instruction `other_index` of
    /// `other_block` in `other`: the same opcode, operands, implicit register
    /// effects, flags and proof facts, each block operand of this one read
    /// through `blocks` first. Source locations and lowering provenance,
    /// which no instruction's semantics reads, are not compared.
    fn same_inst(
        &self,
        block: Self::Block,
        index: usize,
        other: &Self,
        other_block: Self::Block,
        other_index: usize,
        blocks: &dyn Fn(Self::Block) -> Self::Block,
    ) -> bool;

    /// The bounds check `exit` is, if it is one: control takes `exit` only when
    /// `index >=u bound`, as decided by the compare or trap carrier at
    /// instruction `at` of `block`. `fall_through` is the block `exit.from`
    /// falls through to, if any. `None` for any other shape.
    fn unsigned_guard(
        &self,
        exit: LoopExit<Self::Block>,
        fall_through: Option<Self::Block>,
    ) -> Option<UnsignedGuard<Self::Block>>;
}

/// The bound side of a bounds check: an immediate or a register.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum GuardBound {
    Imm(i64),
    Reg(VReg),
}

/// A bounds-check exit: control leaves through it only when `index >=u
/// bound`, decided at instruction `at` of `block`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct UnsignedGuard<B> {
    pub(crate) block: B,
    pub(crate) at: usize,
    pub(crate) index: VReg,
    pub(crate) bound: GuardBound,
}

/// The premise under which a pass asks the contract to admit the loop's
/// bounds checks against its own bound ([`ExitPlan::and_induction_guards`]).
pub(crate) struct InductionGuards<'a> {
    /// The induction register the new code's trip count is computed over.
    pub(crate) iv: VReg,
    /// Whether a compared register holds, where it is compared, a value no
    /// greater (unsigned) than the iteration's induction: a copy of `iv`, or a
    /// value the pass proves smaller. The pass's premise, from its own def
    /// chains.
    pub(crate) at_most_iv: &'a dyn Fn(VReg) -> bool,
    /// Whether a bound is at least the loop test's bound, so that `iv <u
    /// loop bound` implies `iv <u bound`. The pass's premise.
    pub(crate) covers_loop_bound: &'a dyn Fn(GuardBound) -> bool,
}

/// A way control can leave the scalar loop other than its back edge.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum LoopExit<B> {
    /// A transfer from loop block `from` to `to`, a block outside the loop: a
    /// branch, a fall-through, or a conditional trap that names its target.
    Edge { from: B, to: B },
    /// Instruction `index` of loop block `block` can end the loop with no
    /// successor block (see [`LoopStateView::ends_without_successor`]).
    Stop { block: B, index: usize },
}

/// How a rewrite accounts for every way the scalar loop can leave. See the
/// module docs, "Control".
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ExitPlan<B> {
    /// The loop test, and any exit the new code evaluates and leaves through
    /// itself.
    reproduced: Vec<LoopExit<B>>,
    /// Exits the pass proves no replaced iteration takes.
    proved_not_taken: Vec<LoopExit<B>>,
}

impl<B: Copy + Eq> ExitPlan<B> {
    /// The loop test `from -> to` bounds the new code: it runs only iterations
    /// in which the test continues, and gives control back before the first
    /// one in which it leaves. With no further claim, this edge is the only
    /// way the loop may leave.
    pub(crate) fn loop_test(from: B, to: B) -> Self {
        ExitPlan {
            reproduced: vec![LoopExit::Edge { from, to }],
            proved_not_taken: Vec::new(),
        }
    }

    /// [`ExitPlan::loop_test`] for a loop test the pass knows by its operands
    /// only: block `test` must have exactly one exit, and that exit must be
    /// taken exactly when a register `is_iv` accepts is `>=u` a bound
    /// `is_loop_bound` accepts ([`LoopStateView::unsigned_guard`]). `None`
    /// otherwise, so a pass that cannot name its test this way refuses the
    /// loop.
    pub(crate) fn unsigned_loop_test<G: LoopStateView<Block = B>>(
        ir: &G,
        blocks: impl IntoIterator<Item = B>,
        test: B,
        is_iv: &dyn Fn(VReg) -> bool,
        is_loop_bound: &dyn Fn(GuardBound) -> bool,
    ) -> Option<Self>
    where
        B: Hash,
    {
        let to = exit_of_test(ir, blocks, test)?;
        let walker = Walker::new(ir);
        let guard =
            ir.unsigned_guard(LoopExit::Edge { from: test, to }, walker.fall_through(test))?;
        (is_iv(guard.index) && is_loop_bound(guard.bound)).then(|| Self::loop_test(test, to))
    }

    /// A further exit the new code reproduces: for every iteration it replaces
    /// it evaluates the exit's own condition, and leaves through `exit`, or
    /// gives control back to the scalar loop before the first iteration that
    /// would take it.
    pub(crate) fn and_reproduces(mut self, exit: LoopExit<B>) -> Self {
        self.reproduced.push(exit);
        self
    }

    /// An exit the pass proves no iteration its new code replaces can take. A
    /// premise of the pass, claimed only beside a test in which the same loop,
    /// with the proof's premise broken, is refused.
    pub(crate) fn and_proved_not_taken(mut self, exit: LoopExit<B>) -> Self {
        self.proved_not_taken.push(exit);
        self
    }

    /// Admit, as proved not taken, every bounds check of the loop that leaves
    /// only when the iteration's induction is `>=u` a bound at least the loop
    /// test's own. Every iteration the new code replaces is one the scalar
    /// loop runs with `iv <u` its bound, so none of them takes such a check.
    ///
    /// The contract, not the pass, decides which exits qualify. An exit is
    /// admitted only when all of these hold:
    ///
    /// 1. it is an unsigned bounds check on a register and a bound
    ///    ([`LoopStateView::unsigned_guard`]): a `cmp` feeding the branch that
    ///    leaves on `>=u` (or stays on `<u`), or a bounds trap carrier;
    /// 2. the pass's premise accepts both operands (`guards`);
    /// 3. the check runs only in iterations the loop test admitted. With the
    ///    test in the header, the check is outside the header and every path
    ///    from the header to it passes the test's one in-loop successor. With
    ///    the test in a block that branches back to the header (a
    ///    bottom-tested loop), every iteration was entered past the test, or
    ///    past the entry guard the pass requires. Any other test position is
    ///    refused;
    /// 4. no write of the induction register precedes the check in its
    ///    iteration, so the compared value is the iteration's own induction,
    ///    not the next one.
    ///
    /// Anything else stays unclaimed, so the contract refuses the loop.
    pub(crate) fn and_induction_guards<G: LoopStateView<Block = B>>(
        self,
        ir: &G,
        blocks: impl IntoIterator<Item = B>,
        header: B,
        guards: &InductionGuards<'_>,
    ) -> Self
    where
        B: Hash,
    {
        self.and_induction_guards_in(&LoopStateIndex::literal(ir), blocks, header, guards)
    }

    /// [`ExitPlan::and_induction_guards`] over `index`'s function, sharing its
    /// layout map with the pass's other checks of the same function state.
    pub(crate) fn and_induction_guards_in<G: LoopStateView<Block = B>>(
        mut self,
        index: &LoopStateIndex<'_, G>,
        blocks: impl IntoIterator<Item = B>,
        header: B,
        guards: &InductionGuards<'_>,
    ) -> Self
    where
        B: Hash,
    {
        let Some(LoopExit::Edge { from: test, to: _ }) = self.reproduced.first().copied() else {
            return self;
        };
        let ir = index.walker.ir;
        let mut blocks: Vec<B> = blocks.into_iter().collect();
        blocks.sort_by_key(|&block| ir.block_index(block));
        blocks.dedup();
        let in_loop: HashSet<B> = blocks.iter().copied().collect();
        let walker = &index.walker;
        for (exit, transfers) in exits_of(ir, walker, &blocks, &in_loop) {
            if transfers != 1 || self.accounts_for(exit) {
                continue;
            }
            let fall_through = match exit {
                LoopExit::Edge { from, .. } => walker.fall_through(from),
                LoopExit::Stop { .. } => None,
            };
            let Some(guard) = ir.unsigned_guard(exit, fall_through) else {
                continue;
            };
            if (guards.at_most_iv)(guard.index)
                && (guards.covers_loop_bound)(guard.bound)
                && runs_only_past_the_test(walker, &in_loop, header, test, guard.block)
                && !induction_written_before(ir, walker, &in_loop, header, guards.iv, &guard)
            {
                self.proved_not_taken.push(exit);
            }
        }
        self
    }

    /// Does any `proved_not_taken` claim name `target` as its destination?
    /// Diagnostics only: a pass reporting WHY a locality check refused needs
    /// to distinguish "the plan never claimed this edge" from "the block has a
    /// predecessor outside the loop".
    pub(crate) fn proved_not_taken_contains_target(&self, target: B) -> bool {
        self.proved_not_taken
            .iter()
            .any(|claim| matches!(claim, LoopExit::Edge { to, .. } if *to == target))
    }

    fn accounts_for(&self, exit: LoopExit<B>) -> bool {
        self.reproduced.contains(&exit) || self.proved_not_taken.contains(&exit)
    }

    fn claims(&self) -> impl Iterator<Item = LoopExit<B>> + '_ {
        self.reproduced
            .iter()
            .chain(self.proved_not_taken.iter())
            .copied()
    }
}

/// Where a rewrite's new code hands control back to the original program.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Handoff<'a, B> {
    /// Only to the scalar loop header, which then runs at least once.
    Header,
    /// To the header, or straight to an exit (a rotated loop's remainder
    /// guard, a rewrite that replaces the whole loop). Every exit is checked.
    HeaderOrExit,
    /// To every exit and never the header: a rewrite that replaces the
    /// loop's iterations in place (the loop itself now runs the new code), so
    /// the state is observed only once control leaves it.
    Exits,
    /// Only to exactly these blocks: a rewrite that replaces the whole loop
    /// and leaves it through one known exit, never through the header or an
    /// abort path whose check it proved cannot fire. Like [`Handoff::Header`]
    /// this is a premise about the pass's splice, claimed only with a
    /// [`hands_off_only_to`] test.
    Only(&'a [B]),
}

/// Why a loop fails the loop-state rule.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum LoopStateEscape<B> {
    /// The loop can leave by `exit`, which the plan neither reproduces nor
    /// proves untaken, or which two transfers share so no claim can name it
    /// alone: the new code would run past it.
    Exit(LoopExit<B>),
    /// The plan claims `claim`, which is not a way this loop leaves.
    NotAnExit(LoopExit<B>),
    /// `reg`, written in the loop and not reproduced by the rewrite, is live on
    /// entry to `into`: the header, or a block control leaves the loop to.
    Live { reg: StateReg, into: B },
    /// Instruction `index` of `block` has register effects the model cannot
    /// name, so the loop's state cannot be enumerated.
    Unmodeled { block: B, index: usize },
}

/// Evidence that a loop passed the loop-state rule for the register set the
/// rewrite reproduces.
///
/// Minted only by [`LoopLocality::check`]. A rewrite's plan holds one, so a
/// pass cannot build the plan, and so cannot apply it, without running the
/// check on the loop it transforms.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct LoopLocality {
    _sealed: (),
}

impl LoopLocality {
    /// Check the loop `blocks` (header included) against the rule, for a
    /// rewrite that accounts for the loop's exits as `exits` says, reproduces
    /// exactly the registers in `carried`, and hands control back as `handoff`
    /// says.
    pub(crate) fn check<G: LoopStateView>(
        ir: &G,
        blocks: impl IntoIterator<Item = G::Block>,
        header: G::Block,
        exits: &ExitPlan<G::Block>,
        handoff: Handoff<'_, G::Block>,
        carried: &[VReg],
    ) -> Result<Self, LoopStateEscape<G::Block>> {
        Self::check_in(
            &LoopStateIndex::literal(ir),
            blocks,
            header,
            exits,
            handoff,
            carried,
        )
    }

    /// [`LoopLocality::check`] over `index`'s function. A pass that checks
    /// many loops of one function state before it changes the function builds
    /// one [`LoopStateIndex::amortized`] for all of them; the verdicts are
    /// those of [`LoopLocality::check`].
    pub(crate) fn check_in<G: LoopStateView>(
        index: &LoopStateIndex<'_, G>,
        blocks: impl IntoIterator<Item = G::Block>,
        header: G::Block,
        exits: &ExitPlan<G::Block>,
        handoff: Handoff<'_, G::Block>,
        carried: &[VReg],
    ) -> Result<Self, LoopStateEscape<G::Block>> {
        let blocks: Vec<G::Block> = blocks.into_iter().collect();
        match loop_state_escapes(index, &blocks, header, exits, handoff, carried) {
            None => Ok(LoopLocality { _sealed: () }),
            Some(escape) => Err(escape),
        }
    }

    /// [`LoopLocality::check`] with [`Handoff::HeaderOrExit`] for a rewrite
    /// that reproduces `carried` where it hands control back to the header,
    /// and that may also leave straight to the exit of the plan's loop test
    /// (the first claim of `exits`) once it has run every iteration, holding
    /// the state the scalar loop would carry back into its header. The
    /// scalar loop leaves through its test instead, before the writes that
    /// follow the test in its last iteration: a rotated loop's latch
    /// writeback. At that exit every carried register such a write may change
    /// (`written_after_the_test`) is checked like any other register the
    /// loop writes, so a loop whose exit reads one is refused. See the module
    /// docs.
    ///
    /// The contract finds those registers from the loop, so a pass cannot
    /// leave one off: a carried register is reproduced at the exit only when
    /// every write of it in the loop runs in the test's block, before the
    /// test transfers out.
    pub(crate) fn check_rotated<G: LoopStateView>(
        ir: &G,
        blocks: impl IntoIterator<Item = G::Block>,
        header: G::Block,
        exits: &ExitPlan<G::Block>,
        carried: &[VReg],
    ) -> Result<Self, LoopStateEscape<G::Block>> {
        let blocks: Vec<G::Block> = blocks.into_iter().collect();
        let index = LoopStateIndex::literal(ir);
        if let Some(escape) = loop_state_escapes(
            &index,
            &blocks,
            header,
            exits,
            Handoff::HeaderOrExit,
            carried,
        ) {
            return Err(escape);
        }
        // `ExitPlan::loop_test` makes the test the first claim, and always an
        // edge; anything else is a malformed request: refuse.
        let Some(LoopExit::Edge {
            from: test,
            to: exit,
        }) = exits.reproduced.first().copied()
        else {
            return Err(LoopStateEscape::Unmodeled {
                block: header,
                index: 0,
            });
        };
        // A second check of `exit` alone, with fewer registers reproduced: it
        // adds to the first and narrows nothing.
        let at_exit: Vec<VReg> = carried
            .iter()
            .copied()
            .filter(|&reg| !written_after_the_test(ir, &blocks, test, exit, reg))
            .collect();
        match loop_state_escapes(
            &index,
            &blocks,
            header,
            exits,
            Handoff::Only(&[exit]),
            &at_exit,
        ) {
            None => Ok(LoopLocality { _sealed: () }),
            Some(escape) => Err(escape),
        }
    }
}

/// A loop that passed the loop-state rule, with what the iteration-coverage
/// clause needs to check a rewrite of it: its blocks, header, preheader, the
/// loop test its plan named, and the registers the rewrite reproduces.
///
/// Minted only by [`LoopLocality::check_covered`] (or its
/// [`LoopLocality::check_covered_in`] twin), so a coverage check runs on
/// exactly the loop and plan the control and register clauses admitted, or,
/// for a full unroll, by [`CoveredLoop::unrolled`] beside a [`DeadWork`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CoveredLoop<B> {
    blocks: Vec<B>,
    header: B,
    preheader: B,
    test: (B, B),
    carried: Vec<VReg>,
}

impl LoopLocality {
    /// [`LoopLocality::check`], for a rewrite that will also go through the
    /// iteration-coverage clause: `preheader` is the block outside the loop
    /// whose edge enters the header, where both the scalar and the rewritten
    /// runs start. The plan's first claim must be its loop test
    /// ([`ExitPlan::loop_test`]).
    pub(crate) fn check_covered<G: LoopStateView>(
        ir: &G,
        blocks: impl IntoIterator<Item = G::Block>,
        header: G::Block,
        preheader: G::Block,
        exits: &ExitPlan<G::Block>,
        handoff: Handoff<'_, G::Block>,
        carried: &[VReg],
    ) -> Result<CoveredLoop<G::Block>, LoopStateEscape<G::Block>> {
        Self::check_covered_in(
            &LoopStateIndex::literal(ir),
            blocks,
            header,
            preheader,
            exits,
            handoff,
            carried,
        )
    }

    /// [`LoopLocality::check_covered`] over `index`'s function, as
    /// [`LoopLocality::check_in`] is [`LoopLocality::check`]: the verdicts are
    /// those of [`LoopLocality::check_covered`].
    pub(crate) fn check_covered_in<G: LoopStateView>(
        index: &LoopStateIndex<'_, G>,
        blocks: impl IntoIterator<Item = G::Block>,
        header: G::Block,
        preheader: G::Block,
        exits: &ExitPlan<G::Block>,
        handoff: Handoff<'_, G::Block>,
        carried: &[VReg],
    ) -> Result<CoveredLoop<G::Block>, LoopStateEscape<G::Block>> {
        let blocks: Vec<G::Block> = blocks.into_iter().collect();
        Self::check_in(
            index,
            blocks.iter().copied(),
            header,
            exits,
            handoff,
            carried,
        )?;
        let Some(LoopExit::Edge { from, to }) = exits.reproduced.first().copied() else {
            return Err(LoopStateEscape::Unmodeled {
                block: header,
                index: 0,
            });
        };
        if blocks.contains(&preheader) {
            return Err(LoopStateEscape::Unmodeled {
                block: preheader,
                index: 0,
            });
        }
        Ok(CoveredLoop {
            blocks,
            header,
            preheader,
            test: (from, to),
            carried: carried.to_vec(),
        })
    }
}

impl<B: Copy + Eq> CoveredLoop<B> {
    /// The scope of a full unroll, which replaces every iteration with copies
    /// and deletes work it judges dead: the deletion rule must have admitted
    /// that work (`_work`). `test` is the loop test `(from, to)` the trip
    /// count comes from. `None` for a malformed request.
    pub(crate) fn unrolled(
        _work: &DeadWork,
        blocks: impl IntoIterator<Item = B>,
        header: B,
        preheader: B,
        test: (B, B),
    ) -> Option<Self> {
        let blocks: Vec<B> = blocks.into_iter().collect();
        (blocks.contains(&header)
            && !blocks.contains(&preheader)
            && blocks.contains(&test.0)
            && !blocks.contains(&test.1))
        .then_some(CoveredLoop {
            blocks,
            header,
            preheader,
            test,
            carried: Vec::new(),
        })
    }
}

/// Rewrite a copy of `func` (and of `side`, state the rewrite records beside
/// it, such as a provenance map) with `rewrite`, and publish both only when
/// the iteration-coverage clause admits the rewritten function for the loop
/// `scope` names. `rewrite` returns how the new code counts ([`Lanes`]) and
/// its own result, or `None` to decline. On any refusal neither `func` nor
/// `side` changes.
pub(crate) fn publish_covered<G, S, T>(
    func: &mut G,
    side: Option<&mut S>,
    scope: &CoveredLoop<G::Block>,
    rewrite: impl FnOnce(&mut G, Option<&mut S>) -> Option<(Lanes<G::Block>, T)>,
) -> Result<T, CoverageRefusal<G::Block>>
where
    G: LoopStateView + Clone,
    S: Clone,
{
    let mut candidate = func.clone();
    let mut candidate_side = side.as_deref().cloned();
    let (lanes, result) =
        rewrite(&mut candidate, candidate_side.as_mut()).ok_or(CoverageRefusal::Declined)?;
    check_coverage(func, &candidate, scope, &lanes).map_err(CoverageRefusal::Escape)?;
    *func = candidate;
    if let (Some(side), Some(candidate_side)) = (side, candidate_side) {
        *side = candidate_side;
    }
    Ok(result)
}

/// Why [`publish_covered`] left the function unchanged.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum CoverageRefusal<B> {
    /// The rewrite declined.
    Declined,
    /// The iteration-coverage clause refused the rewrite.
    Escape(CoverageEscape<B>),
}

/// Evidence that the register work a rewrite deletes is unobserved: the
/// REGISTER clause, deletion form (see the module docs, "Deleted register
/// work"). Minted only by [`DeadWork::check`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct DeadWork {
    _sealed: (),
}

/// Why deleted register work is observed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum DeadWorkEscape<B> {
    /// `reg`, written by the deleted instruction `deleted`, is read by the
    /// kept instruction `reader` before anything the rewrite keeps replaces
    /// it.
    Read {
        deleted: (B, usize),
        reg: StateReg,
        reader: (B, usize),
    },
    /// A position names no instruction.
    Malformed((B, usize)),
}

impl DeadWork {
    /// Check that a rewrite may delete the instructions at `deleted` (block,
    /// index) without stranding a reader. Every register each one may write,
    /// the flags included, must be unread on every path from just after it,
    /// through the function, until an instruction the rewrite keeps replaces
    /// it. A deleted instruction neither reads nor replaces anything; a read
    /// the rewrite removes from an instruction it keeps (re-pointing an
    /// operand) is listed in `removed_reads` and not counted.
    pub(crate) fn check<G: LoopStateView>(
        ir: &G,
        deleted: &[(G::Block, usize)],
        removed_reads: &[((G::Block, usize), StateReg)],
    ) -> Result<Self, DeadWorkEscape<G::Block>> {
        let walker = Walker::new(ir);
        let gone: HashSet<(G::Block, usize)> = deleted.iter().copied().collect();
        for &(block, index) in deleted {
            if index >= ir.inst_count(block) {
                return Err(DeadWorkEscape::Malformed((block, index)));
            }
            let mut written: Vec<StateReg> = Vec::new();
            ir.visit_state_writes(block, index, &mut |reg, _| {
                if !written.contains(&reg) {
                    written.push(reg);
                }
            });
            for reg in written {
                if let Some(reader) =
                    first_reader(ir, &walker, &gone, removed_reads, (block, index + 1), reg)
                {
                    return Err(DeadWorkEscape::Read {
                        deleted: (block, index),
                        reg,
                        reader,
                    });
                }
            }
        }
        Ok(DeadWork { _sealed: () })
    }
}

/// The first kept instruction that reads `reg` on a path from position
/// `from`, before a kept instruction replaces it.
fn first_reader<G: LoopStateView>(
    ir: &G,
    walker: &Walker<'_, G>,
    gone: &HashSet<(G::Block, usize)>,
    removed_reads: &[((G::Block, usize), StateReg)],
    from: (G::Block, usize),
    reg: StateReg,
) -> Option<(G::Block, usize)> {
    // Scan a block from `start`: `Some(Ok(pos))` a reader, `Some(Err(()))`
    // replaced, `None` falls off the end.
    let scan = |block: G::Block, start: usize| -> Option<Result<usize, ()>> {
        for index in start..ir.inst_count(block) {
            if gone.contains(&(block, index)) {
                continue;
            }
            // An instruction whose register effects the model cannot name
            // (other than a call, which reads only its operands and no flags)
            // may read any virtual register it names, and the flags unless it
            // is a return: no AArch64 or x86-64 return convention carries the
            // flags (`effects::block_terminates_flag_liveness`). A virtual
            // register it does not name it cannot read, so `ret x30` reads
            // neither the trip test nor the flags an unroll deletes; a flags
            // read an opcode really makes is `visit_state_reads`'s below.
            let mut read = ir.has_unmodeled_register_effect(block, index)
                && !ir.is_call(block, index)
                && match reg {
                    StateReg::Virtual(virtual_reg) => ir.names_virtual(block, index, virtual_reg),
                    StateReg::Flags => !ir.is_return(block, index),
                };
            ir.visit_state_reads(block, index, &mut |used| read |= used.observes(reg));
            if read
                && !removed_reads
                    .iter()
                    .any(|&(at, removed)| at == (block, index) && removed == reg)
            {
                return Some(Ok(index));
            }
            let mut replaced = false;
            ir.visit_state_writes(block, index, &mut |written, how| {
                replaced |= written == reg && how == StateWrite::Replaces;
            });
            if replaced {
                return Some(Err(()));
            }
        }
        None
    };
    // A block control can leave with no successor block keeps the value
    // only past a return or a trap; an indirect branch goes somewhere the
    // walk cannot follow, so it counts as a reader.
    let dead_end = |block: G::Block| -> Option<(G::Block, usize)> {
        let count = ir.inst_count(block);
        let last = count.checked_sub(1)?;
        (ir.is_indirect_branch(block, last)
            || (!ir.ends_without_successor(block, last)
                && !ir.is_unconditional_branch(block, last)))
        .then_some((block, last))
    };
    let (block, start) = from;
    match scan(block, start) {
        Some(Ok(index)) => return Some((block, index)),
        Some(Err(())) => return None,
        None => {}
    }
    let mut seen: HashSet<G::Block> = HashSet::default();
    let mut work: Vec<G::Block> = walker.successors(block);
    if work.is_empty() {
        return dead_end(block).or_else(|| (ir.inst_count(block) == 0).then_some((block, 0)));
    }
    while let Some(next) = work.pop() {
        if !seen.insert(next) {
            continue;
        }
        match scan(next, 0) {
            Some(Ok(index)) => return Some((next, index)),
            Some(Err(())) => {}
            None => {
                let successors = walker.successors(next);
                if successors.is_empty() {
                    if let Some(reader) = dead_end(next) {
                        return Some(reader);
                    }
                    if ir.inst_count(next) == 0 {
                        return Some((next, 0));
                    }
                }
                work.extend(successors);
            }
        }
    }
    None
}

/// The first violation of the loop-state rule, or `None` when `exits`
/// accounts for every way the loop can leave and the loop's only carried or
/// live-out state is `carried`. See the module docs.
///
/// `blocks` is the loop, header included, and `index` indexes its function.
/// Blocks are examined in
/// [`MachIrView::block_index`] order so the reported escape is deterministic:
/// an unmodeled instruction first, then an exit, then a live register.
/// Is `target` — a block control can leave the loop to — provably never
/// entered once the rewrite is in place?
///
/// This closes an inconsistency in the rule rather than widening it:
/// [`ExitPlan::accounts_for`] already treats a `proved_not_taken` edge as
/// settled for the CONTROL check, but the register check used to add that
/// edge's target to `starts` anyway and then refuse the loop for any tracked
/// register live into it.
///
/// That is what blocked every bounds-checked loop once the bridge began
/// lowering a failed check to the faithful `panic_bounds_check` raise
/// (`assert_panic::emit`). The raise block READS the index, so a copy of the
/// IV is live into it, and the loop was refused — `Live { reg, into }` — even
/// though the plan had already proved that edge cannot be taken. The older
/// `[Ud2]` trap read nothing, so the same loops passed.
///
/// # Both conditions are required
///
/// `LoopStateIndex::live_into` is path-INSENSITIVE: it answers "is this
/// register live on entry to this block", not "along this edge". So skipping
/// `target` is sound only when the block cannot be entered AT ALL after the
/// rewrite, which needs
///
/// * **every** loop-exit edge into `target` to be in `proved_not_taken` — one
///   unproven edge leaves it reachable from this loop; and
/// * `target` to have **no predecessor outside the loop** — an outside
///   predecessor keeps the block live independently of this rewrite, and the
///   liveness answer would then describe a path the plan says nothing about.
///
/// Neither alone is enough, and a block with no loop edge into it at all is
/// not this function's business (`false`).
fn unreachable_after_rewrite<G: LoopStateView>(
    ir: &G,
    walker: &Walker<'_, G>,
    in_loop: &HashSet<G::Block>,
    exits: &ExitPlan<G::Block>,
    leaves: &[(LoopExit<G::Block>, usize)],
    target: G::Block,
) -> bool {
    // `leaves` is the SAME enumeration the control check above consulted
    // (`exits_of`), deliberately rather than a fresh walk of the successors:
    // `Walker::successors` is an OVER-approximation that folds in the layout
    // fall-through, so re-deriving the edge set here demanded claims for
    // "edges" the plan was never asked about, and refused loops whose every
    // real exit the control check had already accepted.
    let mut saw_loop_edge = false;
    for &(exit, _) in leaves {
        let LoopExit::Edge { to, .. } = exit else {
            continue;
        };
        if to != target {
            continue;
        }
        saw_loop_edge = true;
        if !exits.proved_not_taken.contains(&exit) {
            return false;
        }
    }
    if !saw_loop_edge {
        return false;
    }
    for block in ir.layout_order() {
        if in_loop.contains(&block) {
            continue;
        }
        // An EXPLICIT edge — a recorded successor or a block a branch names —
        // always counts.
        let mut explicit = ir.successors(block);
        for index in 0..ir.inst_count(block) {
            explicit.extend(ir.branch_targets(block, index));
        }
        if explicit.contains(&target) {
            return false;
        }
        // A LAYOUT FALL-THROUGH counts only if control can actually reach the
        // end of `block`. `Walker::fall_through` excludes only an unconditional
        // branch or a return, so a block that DIVERGES — the faithful panic
        // raise is `Call panic_bounds_check` then `Ud2`, and `Ud2` is neither —
        // looks like it falls into whatever follows it in layout. Without this
        // test one raise block is read as a predecessor of the next, and a loop
        // with two bounds checks can never satisfy the rule.
        let diverges =
            (0..ir.inst_count(block)).any(|index| ir.ends_without_successor(block, index));
        if !diverges && walker.fall_through(block) == Some(target) {
            return false;
        }
    }
    true
}

fn loop_state_escapes<G: LoopStateView>(
    index: &LoopStateIndex<'_, G>,
    blocks: &[G::Block],
    header: G::Block,
    exits: &ExitPlan<G::Block>,
    handoff: Handoff<'_, G::Block>,
    carried: &[VReg],
) -> Option<LoopStateEscape<G::Block>> {
    let ir = index.walker.ir;
    let mut blocks: Vec<G::Block> = blocks.to_vec();
    blocks.sort_by_key(|&block| ir.block_index(block));
    blocks.dedup();
    let in_loop: HashSet<G::Block> = blocks.iter().copied().collect();
    if !in_loop.contains(&header) {
        // A header outside the block set is a malformed request: refuse.
        return Some(LoopStateEscape::Unmodeled {
            block: header,
            index: 0,
        });
    }

    // Every register the loop may write, other than the reproduced ones. The
    // flags are tracked unconditionally: no rewrite reproduces them.
    let mut tracked: Vec<StateReg> = vec![StateReg::Flags];
    for &block in &blocks {
        for index in 0..ir.inst_count(block) {
            if ir.has_unmodeled_register_effect(block, index) {
                return Some(LoopStateEscape::Unmodeled { block, index });
            }
            ir.visit_state_writes(block, index, &mut |reg, _| {
                let reproduced = matches!(reg, StateReg::Virtual(v) if carried.contains(&v));
                if !reproduced && !tracked.contains(&reg) {
                    tracked.push(reg);
                }
            });
        }
    }

    let walker = &index.walker;

    // Control: every way the loop can leave is accounted for, by one claim.
    let leaves = exits_of(ir, walker, &blocks, &in_loop);
    for &(exit, transfers) in &leaves {
        if transfers != 1 || !exits.accounts_for(exit) {
            return Some(LoopStateEscape::Exit(exit));
        }
    }
    if let Some(claim) = exits
        .claims()
        .find(|claim| !leaves.iter().any(|&(exit, _)| exit == *claim))
    {
        return Some(LoopStateEscape::NotAnExit(claim));
    }

    // Where the stale state could be observed: the header, the header and
    // every block control can leave the loop to, or the named blocks.
    let mut starts: Vec<G::Block> = Vec::new();
    match handoff {
        Handoff::Header => starts.push(header),
        Handoff::HeaderOrExit => {
            starts.push(header);
            for &block in &blocks {
                for successor in walker.successors(block) {
                    if !in_loop.contains(&successor)
                        && !starts.contains(&successor)
                        && !unreachable_after_rewrite(
                            ir, walker, &in_loop, exits, &leaves, successor,
                        )
                    {
                        starts.push(successor);
                    }
                }
            }
        }
        Handoff::Exits => {
            for &block in &blocks {
                for successor in walker.successors(block) {
                    if !in_loop.contains(&successor)
                        && !starts.contains(&successor)
                        && !unreachable_after_rewrite(
                            ir, walker, &in_loop, exits, &leaves, successor,
                        )
                    {
                        starts.push(successor);
                    }
                }
            }
        }
        Handoff::Only(targets) => {
            for &target in targets {
                if !starts.contains(&target) {
                    starts.push(target);
                }
            }
        }
    }
    for reg in tracked {
        for &start in &starts {
            if index.live_into(start, reg) {
                return Some(LoopStateEscape::Live { reg, into: start });
            }
        }
    }
    None
}

/// The loop-state rule's view of ONE function state: the layout map every
/// check reads, and the answers to "is `reg` live into `start`" (see
/// [`Walker::live_into`]).
///
/// A pass that recognizes many loops of a function before it changes it (a
/// recognition sweep) asked each question with a fresh forward walk. A
/// register that is dead past its loop is dead along every path to the end of
/// the function, so each such walk visits the rest of the function: one long
/// function of N loops cost O(N^2) (neon-fill, 120 fill loops in one `main`:
/// 53 ms of a 350 ms compile, measured 2026-10-01). An
/// [`LoopStateIndex::amortized`] index answers the first questions with those
/// walks, and once they have visited as many blocks as the function has, it
/// builds the block predecessors and register readers once and answers each
/// register's question by propagating liveness backward from the blocks that
/// read it: the same least fixpoint the forward walk searches, so every
/// answer, and so every verdict, is the literal walk's
/// (`an_amortized_index_answers_what_the_walks_answer`).
///
/// It borrows the function, so the function cannot change while an index of
/// it lives.
pub(crate) struct LoopStateIndex<'a, G: LoopStateView> {
    walker: Walker<'a, G>,
    /// Whether liveness may be answered from [`LivenessIndex`] once the
    /// literal walks have paid for building it.
    amortize: bool,
    /// Blocks the literal walks have visited so far.
    walked: std::cell::Cell<usize>,
    /// Blocks in layout order: the walks' break-even point.
    layout_blocks: usize,
    liveness: std::cell::OnceCell<LivenessIndex<G::Block>>,
    /// Per register, every indexed block it is live into.
    live_in: std::cell::RefCell<HashMap<StateReg, HashSet<G::Block>>>,
}

impl<'a, G: LoopStateView> LoopStateIndex<'a, G> {
    /// Every liveness answer is a literal forward walk: one check.
    pub(crate) fn literal(ir: &'a G) -> Self {
        Self::with(ir, false)
    }

    /// Answers from a whole-function index once the walks have cost as much
    /// as building it: many checks of one function state.
    pub(crate) fn amortized(ir: &'a G) -> Self {
        Self::with(ir, true)
    }

    /// An amortized index that answers from the whole-function index from
    /// the first question on (the differential tests).
    #[cfg(test)]
    pub(crate) fn indexed_from_the_start(ir: &'a G) -> Self {
        let index = Self::with(ir, true);
        index.walked.set(index.layout_blocks);
        index
    }

    fn with(ir: &'a G, amortize: bool) -> Self {
        let walker = Walker::new(ir);
        let layout_blocks = walker.layout_len;
        LoopStateIndex {
            walker,
            amortize,
            walked: std::cell::Cell::new(0),
            layout_blocks,
            liveness: std::cell::OnceCell::new(),
            live_in: std::cell::RefCell::new(HashMap::default()),
        }
    }

    /// Whether some path from the top of `start` reads `reg` before an
    /// instruction replaces it ([`Walker::live_into`]).
    fn live_into(&self, start: G::Block, reg: StateReg) -> bool {
        if self.amortize && self.walked.get() >= self.layout_blocks {
            let liveness = self
                .liveness
                .get_or_init(|| LivenessIndex::build(&self.walker));
            if liveness.indexed.contains(&start) {
                if let Some(live) = self.live_in.borrow().get(&reg) {
                    return live.contains(&start);
                }
                let live = liveness.live_in(self.walker.ir, reg);
                let answer = live.contains(&start);
                self.live_in.borrow_mut().insert(reg, live);
                return answer;
            }
        }
        let mut visited = 0;
        let live = self.walker.live_into_counted(start, reg, &mut visited);
        self.walked.set(self.walked.get().saturating_add(visited));
        charge_liveness_work(visited);
        live
    }
}

#[cfg(test)]
thread_local! {
    /// Blocks the liveness questions of this thread have visited: literal walk
    /// visits, blocks indexed, and blocks the backward propagation entered.
    /// The deterministic work count the growth tests bound.
    static LIVENESS_WORK: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}

/// Charge `blocks` to [`LIVENESS_WORK`] (tests only).
#[inline]
fn charge_liveness_work(blocks: usize) {
    #[cfg(test)]
    LIVENESS_WORK.with(|work| work.set(work.get() + blocks as u64));
    #[cfg(not(test))]
    let _ = blocks;
}

/// The liveness work this thread has done so far (tests only).
#[cfg(test)]
pub(crate) fn liveness_work() -> u64 {
    LIVENESS_WORK.with(std::cell::Cell::get)
}

/// The function-wide facts [`LoopStateIndex`] answers liveness from, over
/// every block reachable from a block in layout order through
/// [`Walker::successors`] (a set closed under those successors).
struct LivenessIndex<B> {
    indexed: HashSet<B>,
    /// The blocks whose [`Walker::successors`] name each indexed block.
    predecessors: HashMap<B, Vec<B>>,
    /// The blocks with an instruction that may read a virtual register of
    /// each number (in any class: [`StateReg::observes`]).
    virtual_readers: HashMap<u32, Vec<B>>,
    /// The blocks with an instruction that may read the flags.
    flag_readers: Vec<B>,
}

impl<B: Copy + Eq + Hash> LivenessIndex<B> {
    fn build<G: LoopStateView<Block = B>>(walker: &Walker<'_, G>) -> Self {
        let ir = walker.ir;
        let mut indexed: HashSet<B> = HashSet::default();
        let mut order: Vec<B> = Vec::new();
        let mut work: Vec<B> = ir.layout_order();
        work.reverse();
        while let Some(block) = work.pop() {
            if !indexed.insert(block) {
                continue;
            }
            order.push(block);
            for successor in walker.successors(block) {
                if !indexed.contains(&successor) {
                    work.push(successor);
                }
            }
        }
        let mut predecessors: HashMap<B, Vec<B>> = HashMap::default();
        let mut virtual_readers: HashMap<u32, Vec<B>> = HashMap::default();
        let mut flag_readers: Vec<B> = Vec::new();
        for &block in &order {
            for successor in walker.successors(block) {
                let preds = predecessors.entry(successor).or_default();
                if preds.last() != Some(&block) {
                    preds.push(block);
                }
            }
            for index in 0..ir.inst_count(block) {
                ir.visit_state_reads(block, index, &mut |read| match read {
                    StateReg::Virtual(vreg) => {
                        let readers = virtual_readers.entry(vreg.id).or_default();
                        if readers.last() != Some(&block) {
                            readers.push(block);
                        }
                    }
                    StateReg::Flags => {
                        if flag_readers.last() != Some(&block) {
                            flag_readers.push(block);
                        }
                    }
                });
            }
        }
        charge_liveness_work(order.len());
        LivenessIndex {
            indexed,
            predecessors,
            virtual_readers,
            flag_readers,
        }
    }

    /// Every indexed block `reg` is live into: the blocks that read it before
    /// replacing it, and, backward through the predecessors, every block that
    /// does not replace it and has a successor `reg` is live into. That least
    /// fixpoint is the set of blocks from which [`Walker::live_into`]'s forward
    /// walk reaches such a read.
    fn live_in<G: LoopStateView<Block = B>>(&self, ir: &G, reg: StateReg) -> HashSet<B> {
        let readers: &[B] = match reg {
            StateReg::Virtual(vreg) => self
                .virtual_readers
                .get(&vreg.id)
                .map(Vec::as_slice)
                .unwrap_or(&[]),
            StateReg::Flags => &self.flag_readers,
        };
        let mut live: HashSet<B> = HashSet::default();
        let mut work: Vec<B> = Vec::new();
        for &block in readers {
            if read_before_replaced(ir, block, reg) == Some(true) && live.insert(block) {
                work.push(block);
            }
        }
        let mut replacing: HashSet<B> = HashSet::default();
        while let Some(block) = work.pop() {
            let Some(preds) = self.predecessors.get(&block) else {
                continue;
            };
            for &pred in preds {
                if live.contains(&pred) || replacing.contains(&pred) {
                    continue;
                }
                // A block that replaces `reg` before reading it stops the
                // walk; one that reads it first (already a seed) or neither
                // reads nor replaces it has `reg` live on entry.
                if read_before_replaced(ir, pred, reg) == Some(false) {
                    replacing.insert(pred);
                    continue;
                }
                live.insert(pred);
                work.push(pred);
            }
        }
        charge_liveness_work(live.len() + replacing.len());
        live
    }
}

/// How the first instruction of `block` that reads or replaces `reg` treats
/// it, in [`Walker::live_into`]'s order (an instruction's read before its
/// write): `Some(true)` a read, `Some(false)` a replacement, `None` neither.
fn read_before_replaced<G: LoopStateView>(ir: &G, block: G::Block, reg: StateReg) -> Option<bool> {
    for index in 0..ir.inst_count(block) {
        let mut read = false;
        ir.visit_state_reads(block, index, &mut |used| read |= used.observes(reg));
        if read {
            return Some(true);
        }
        let mut replaced = false;
        ir.visit_state_writes(block, index, &mut |written, how| {
            replaced |= written == reg && how == StateWrite::Replaces;
        });
        if replaced {
            return Some(false);
        }
    }
    None
}

/// Whether a write of `reg` (any class of its number) in the loop `blocks`
/// may run where an iteration that leaves through the loop test `test ->
/// exit` does not run it: in `test` at or after the first instruction that
/// transfers to `exit` (none of `test` when it leaves by falling through), or
/// in any other loop block. An iteration that leaves through the test then
/// holds `reg`'s value from before that write. Counting every other block
/// over-approximates when the test is not the header, since blocks between
/// the header and the test also run before it leaves; that fails closed.
fn written_after_the_test<G: LoopStateView>(
    ir: &G,
    blocks: &[G::Block],
    test: G::Block,
    exit: G::Block,
    reg: VReg,
) -> bool {
    let count = ir.inst_count(test);
    let leaves_at = (0..count)
        .find(|&index| ir.branch_targets(test, index).contains(&exit))
        .unwrap_or(count);
    blocks.iter().any(|&block| {
        let first = if block == test { leaves_at } else { 0 };
        (first..ir.inst_count(block)).any(|index| {
            let mut writes = false;
            ir.visit_state_writes(block, index, &mut |written, _| {
                writes |= matches!(written, StateReg::Virtual(v) if v.id == reg.id);
            });
            writes
        })
    })
}

/// Rule 3 of [`ExitPlan::and_induction_guards`]: `guard` runs only in
/// iterations the loop test in block `test` admitted.
fn runs_only_past_the_test<G: LoopStateView>(
    walker: &Walker<'_, G>,
    in_loop: &HashSet<G::Block>,
    header: G::Block,
    test: G::Block,
    guard: G::Block,
) -> bool {
    let in_loop_successors = |block: G::Block| -> Vec<G::Block> {
        let mut successors: Vec<G::Block> = walker
            .successors(block)
            .into_iter()
            .filter(|successor| in_loop.contains(successor))
            .collect();
        successors.dedup();
        successors
    };
    if test == header {
        // Top-tested: the header runs once more than the body, with the test
        // failing, so a check in it can fire on that last visit.
        if guard == header {
            return false;
        }
        let continues = in_loop_successors(header);
        let [past] = continues.as_slice() else {
            return false;
        };
        // Every header-to-guard path passes `past`.
        let mut seen: HashSet<G::Block> = HashSet::default();
        let mut work: Vec<G::Block> = Vec::new();
        for successor in in_loop_successors(header) {
            if successor != *past {
                work.push(successor);
            }
        }
        while let Some(block) = work.pop() {
            if block == header || block == *past || !seen.insert(block) {
                continue;
            }
            if block == guard {
                return false;
            }
            work.extend(in_loop_successors(block));
        }
        true
    } else {
        // Bottom-tested: the test block branches back to the header, so every
        // iteration was entered past it (or past the pass's entry guard).
        in_loop_successors(test).contains(&header)
    }
}

/// Rule 4 of [`ExitPlan::and_induction_guards`]: whether some write of `iv`
/// (any class of its number) can run before `guard`'s compare in the same
/// iteration, on a path that does not go back through the header.
fn induction_written_before<G: LoopStateView>(
    ir: &G,
    walker: &Walker<'_, G>,
    in_loop: &HashSet<G::Block>,
    header: G::Block,
    iv: VReg,
    guard: &UnsignedGuard<G::Block>,
) -> bool {
    let writes_iv = |block: G::Block, index: usize| {
        let mut writes = false;
        ir.visit_state_writes(block, index, &mut |written, _| {
            writes |= matches!(written, StateReg::Virtual(v) if v.id == iv.id);
        });
        writes
    };
    if (0..guard.at).any(|index| writes_iv(guard.block, index)) {
        return true;
    }
    // Blocks reachable from a write without passing the header.
    let mut work: Vec<G::Block> = Vec::new();
    for &block in in_loop {
        if (0..ir.inst_count(block)).any(|index| writes_iv(block, index)) {
            work.extend(walker.successors(block));
        }
    }
    let mut seen: HashSet<G::Block> = HashSet::default();
    while let Some(block) = work.pop() {
        if block == header || !in_loop.contains(&block) || !seen.insert(block) {
            continue;
        }
        if block == guard.block {
            return true;
        }
        work.extend(walker.successors(block));
    }
    false
}

/// The block outside the loop `blocks` that block `from` transfers to, when
/// there is exactly one: the exit of a loop test the pass found in `from`.
pub(crate) fn exit_of_test<G: LoopStateView>(
    ir: &G,
    blocks: impl IntoIterator<Item = G::Block>,
    from: G::Block,
) -> Option<G::Block> {
    let targets: Vec<G::Block> = loop_exits(ir, blocks)
        .into_iter()
        .filter_map(|(exit, _)| match exit {
            LoopExit::Edge { from: source, to } if source == from => Some(to),
            _ => None,
        })
        .collect();
    match targets.as_slice() {
        [to] => Some(*to),
        _ => None,
    }
}

/// Every way control can leave the loop `blocks`, in block order, with the
/// number of transfers that take it. See [`LoopExit`].
///
/// A transfer is an instruction that names a block outside the loop, the
/// fall-through of a block that does not end in an unconditional transfer
/// (unless an instruction of the same block names that block: control reaches
/// it either way), or a CFG successor outside the loop that neither names. An
/// instruction that ends the loop with no successor block is one
/// [`LoopExit::Stop`].
pub(crate) fn loop_exits<G: LoopStateView>(
    ir: &G,
    blocks: impl IntoIterator<Item = G::Block>,
) -> Vec<(LoopExit<G::Block>, usize)> {
    let mut blocks: Vec<G::Block> = blocks.into_iter().collect();
    blocks.sort_by_key(|&block| ir.block_index(block));
    blocks.dedup();
    let in_loop: HashSet<G::Block> = blocks.iter().copied().collect();
    exits_of(ir, &Walker::new(ir), &blocks, &in_loop)
}

fn exits_of<G: LoopStateView>(
    ir: &G,
    walker: &Walker<'_, G>,
    blocks: &[G::Block],
    in_loop: &HashSet<G::Block>,
) -> Vec<(LoopExit<G::Block>, usize)> {
    let mut exits: Vec<(LoopExit<G::Block>, usize)> = Vec::new();
    let mut take = |exit: LoopExit<G::Block>| match exits.iter_mut().find(|(e, _)| *e == exit) {
        Some((_, transfers)) => *transfers += 1,
        None => exits.push((exit, 1)),
    };
    for &block in blocks {
        let count = ir.inst_count(block);
        let mut named: Vec<G::Block> = Vec::new();
        for index in 0..count {
            if ir.ends_without_successor(block, index) {
                take(LoopExit::Stop { block, index });
            }
            for target in ir.branch_targets(block, index) {
                named.push(target);
                if !in_loop.contains(&target) {
                    take(LoopExit::Edge {
                        from: block,
                        to: target,
                    });
                }
            }
        }
        let fall_through = walker.fall_through(block);
        if let Some(next) = fall_through
            && !in_loop.contains(&next)
            && !named.contains(&next)
        {
            take(LoopExit::Edge {
                from: block,
                to: next,
            });
        }
        for successor in ir.successors(block) {
            if !in_loop.contains(&successor)
                && !named.contains(&successor)
                && fall_through != Some(successor)
            {
                take(LoopExit::Edge {
                    from: block,
                    to: successor,
                });
            }
        }
    }
    exits
}

/// Whether control leaves the `new_blocks` of a rewrite only for `target`:
/// every successor of a new block is another new block or `target`. This is
/// the premise of [`Handoff::Header`], checked on the rewritten CFG.
#[cfg(test)]
pub(crate) fn hands_off_only_to<G: LoopStateView>(
    ir: &G,
    new_blocks: &[G::Block],
    target: G::Block,
) -> bool {
    let walker = Walker::new(ir);
    new_blocks.iter().all(|&block| {
        walker
            .successors(block)
            .into_iter()
            .all(|successor| successor == target || new_blocks.contains(&successor))
    })
}

/// Forward liveness over one function's CFG, with the layout fall-through
/// successor of every block computed once.
struct Walker<'a, G: LoopStateView> {
    ir: &'a G,
    layout_next: HashMap<G::Block, G::Block>,
    /// Blocks in layout order.
    layout_len: usize,
}

impl<'a, G: LoopStateView> Walker<'a, G> {
    fn new(ir: &'a G) -> Self {
        let order = ir.layout_order();
        let layout_next = order
            .iter()
            .zip(order.iter().skip(1))
            .map(|(&block, &next)| (block, next))
            .collect();
        Walker {
            ir,
            layout_next,
            layout_len: order.len(),
        }
    }

    /// Every block control can reach directly from the end of `block`: its CFG
    /// successors, every block an instruction in it names, and its layout
    /// successor unless it ends in an unconditional branch or a return. An
    /// extra successor only adds paths, so an over-approximation fails closed.
    fn successors(&self, block: G::Block) -> Vec<G::Block> {
        let mut successors = self.ir.successors(block);
        for index in 0..self.ir.inst_count(block) {
            successors.extend(self.ir.branch_targets(block, index));
        }
        successors.extend(self.fall_through(block));
        successors
    }

    /// The layout successor `block` falls through to, unless it ends in an
    /// unconditional branch or a return.
    fn fall_through(&self, block: G::Block) -> Option<G::Block> {
        let count = self.ir.inst_count(block);
        let ends_in_transfer = count > 0
            && (self.ir.is_unconditional_branch(block, count - 1)
                || self.ir.is_return(block, count - 1));
        if ends_in_transfer {
            None
        } else {
            self.layout_next.get(&block).copied()
        }
    }

    /// Whether some path from the top of `start` reads `reg` before an
    /// instruction replaces it.
    #[cfg(test)]
    fn live_into(&self, start: G::Block, reg: StateReg) -> bool {
        self.live_into_counted(start, reg, &mut 0)
    }

    /// [`Walker::live_into`], adding the number of blocks it visits to
    /// `visited_blocks`.
    fn live_into_counted(
        &self,
        start: G::Block,
        reg: StateReg,
        visited_blocks: &mut usize,
    ) -> bool {
        let mut visited: HashSet<G::Block> = HashSet::default();
        let mut work = vec![start];
        while let Some(block) = work.pop() {
            if !visited.insert(block) {
                continue;
            }
            *visited_blocks += 1;
            let mut replaced = false;
            for index in 0..self.ir.inst_count(block) {
                let mut read = false;
                self.ir
                    .visit_state_reads(block, index, &mut |used| read |= used.observes(reg));
                if read {
                    return true;
                }
                self.ir
                    .visit_state_writes(block, index, &mut |written, how| {
                        replaced |= written == reg && how == StateWrite::Replaces;
                    });
                if replaced {
                    break;
                }
            }
            if !replaced {
                work.extend(self.successors(block));
            }
        }
        false
    }
}

// ---------------------------------------------------------------------------
// AArch64: MachFunction
// ---------------------------------------------------------------------------

/// Whether an AArch64 flag write replaces every flag. The LL/SC pseudos write
/// flags inside their expansion and are only a may-write.
fn aarch64_replaces_flags(opcode: AArch64Opcode) -> bool {
    use AArch64Opcode::*;
    writes_flags(opcode)
        && !matches!(
            opcode,
            LlscRmw8
                | LlscRmw16
                | LlscRmw32
                | LlscRmw64
                | LlscCmpSwap8
                | LlscCmpSwap16
                | LlscCmpSwap32
                | LlscCmpSwap64
                | LlscLoad128
                | LlscStore128
                | LlscRmw128
                | LlscCmpSwap128
        )
}

const AARCH64_EQ: i64 = 0;
const AARCH64_NE: i64 = 1;
const AARCH64_HS: i64 = 2;
const AARCH64_LO: i64 = 3;

/// The AArch64 condition code true exactly when `cc` is false, for the codes
/// the bounds-check view reads.
fn aarch64_negate(cc: i64) -> Option<i64> {
    match cc {
        AARCH64_EQ => Some(AARCH64_NE),
        AARCH64_NE => Some(AARCH64_EQ),
        AARCH64_HS => Some(AARCH64_LO),
        AARCH64_LO => Some(AARCH64_HS),
        _ => None,
    }
}

/// The guard a `cmp index, bound` at instruction `at` of `block` decides.
fn unsigned_compare(
    compare: &trust_cg_ir::MachInst,
    block: trust_cg_ir::BlockId,
    at: usize,
) -> Option<UnsignedGuard<trust_cg_ir::BlockId>> {
    let bound = match compare.operands.get(1)? {
        MachOperand::Imm(value) => GuardBound::Imm(*value),
        MachOperand::VReg(value) => GuardBound::Reg(*value),
        _ => return None,
    };
    match (compare.opcode, compare.operands.first()?) {
        (AArch64Opcode::CmpRR | AArch64Opcode::CmpRI, MachOperand::VReg(index)) => {
            Some(UnsignedGuard {
                block,
                at,
                index: *index,
                bound,
            })
        }
        _ => None,
    }
}

/// When `flag` holds, at instruction `before` of the block `insts`, the 0/1
/// result of a `cset` in the same block: the `cset`'s position and condition.
/// The value may pass through copies, zero-extensions and `and #1` (each
/// preserves a 0/1 value; `cset` writes the whole register).
fn aarch64_materialized_condition(
    func: &MachFunction,
    insts: &[trust_cg_ir::InstId],
    before: usize,
    flag: VReg,
) -> Option<(usize, i64)> {
    use AArch64Opcode::*;
    let mut value = flag;
    let mut position = before;
    loop {
        // The nearest write of `value`'s number before `position`.
        let def_at = (0..position).rev().find(|&index| {
            let mut defines = false;
            for_each_inst_def(func.inst(insts[index]), |defined| {
                defines |= defined.id == value.id;
            });
            defines
        })?;
        let def = func.inst(insts[def_at]);
        match (def.opcode, def.operands.as_slice()) {
            (CSet, [MachOperand::VReg(d), MachOperand::Imm(cc)]) if d.id == value.id => {
                return Some((def_at, *cc));
            }
            (MovR | Copy | Uxtb | Uxth | Uxtw, [MachOperand::VReg(d), MachOperand::VReg(s)])
                if d.id == value.id =>
            {
                value = *s;
            }
            (
                AndRI,
                [
                    MachOperand::VReg(d),
                    MachOperand::VReg(s),
                    MachOperand::Imm(1),
                ],
            ) if d.id == value.id => {
                value = *s;
            }
            _ => return None,
        }
        position = def_at;
    }
}

impl LoopStateView for MachFunction {
    fn trip_effects(
        &self,
        block: Self::Block,
        index: usize,
        out: &mut Vec<TripEffect<Self::Block>>,
    ) {
        trip_aarch64::block_trip_effects(self, block, index, out);
    }

    fn same_inst(
        &self,
        block: Self::Block,
        index: usize,
        other: &Self,
        other_block: Self::Block,
        other_index: usize,
        blocks: &dyn Fn(Self::Block) -> Self::Block,
    ) -> bool {
        let a = self.inst(self.block(block).insts[index]);
        let b = other.inst(other.block(other_block).insts[other_index]);
        a.opcode == b.opcode
            && a.implicit_defs == b.implicit_defs
            && a.implicit_uses == b.implicit_uses
            && a.flags == b.flags
            && a.proof == b.proof
            && a.operands.len() == b.operands.len()
            && a.operands.iter().zip(&b.operands).all(|pair| match pair {
                (MachOperand::Block(x), MachOperand::Block(y)) => blocks(*x) == *y,
                (MachOperand::FImm(x), MachOperand::FImm(y)) => x.to_bits() == y.to_bits(),
                (x, y) => x == y,
            })
    }

    fn visit_state_reads(&self, block: Self::Block, index: usize, visit: &mut dyn FnMut(StateReg)) {
        let inst = self.inst(self.block(block).insts[index]);
        for_each_inst_use(inst, |used| visit(StateReg::Virtual(used)));
        // The flag-liveness walk's own readers (`reads_nzcv`: the select and
        // carry family, `BCond`, the `Bcc` alias, an implicit NZCV use) and
        // every instruction it cannot account for (`nzcv_unknown`: an `Mrs`,
        // which may select NZCV, LL/SC carriers and opaque pseudos).
        if reads_nzcv(inst) || nzcv_unknown(inst) {
            visit(StateReg::Flags);
        }
    }

    fn visit_state_writes(
        &self,
        block: Self::Block,
        index: usize,
        visit: &mut dyn FnMut(StateReg, StateWrite),
    ) {
        let inst = self.inst(self.block(block).insts[index]);
        // A partial or conditional AArch64 write (`Movk`, the bitfield
        // inserts) is also modeled as a use of its destination, so the read
        // is seen before this write can end a path.
        for_each_inst_def(inst, |defined| {
            visit(StateReg::Virtual(defined), StateWrite::Replaces)
        });
        if writes_flags(inst.opcode) {
            let how = if aarch64_replaces_flags(inst.opcode) {
                StateWrite::Replaces
            } else {
                StateWrite::MayModify
            };
            visit(StateReg::Flags, how);
        }
    }

    fn names_virtual(&self, block: Self::Block, index: usize, reg: VReg) -> bool {
        let inst = self.inst(self.block(block).insts[index]);
        inst.opcode.is_phi()
            || inst
                .operands
                .iter()
                .any(|operand| matches!(operand, MachOperand::VReg(named) if named.id == reg.id))
    }

    fn has_unmodeled_register_effect(&self, block: Self::Block, index: usize) -> bool {
        let inst = self.inst(self.block(block).insts[index]);
        inst.is_call()
            || inst.opcode.is_phi()
            || !inst.implicit_defs.is_empty()
            || !inst.implicit_uses.is_empty()
            || inst
                .operands
                .iter()
                .any(|operand| matches!(operand, MachOperand::PReg(_) | MachOperand::MemOp { .. }))
    }

    fn unsigned_guard(
        &self,
        exit: LoopExit<Self::Block>,
        fall_through: Option<Self::Block>,
    ) -> Option<UnsignedGuard<Self::Block>> {
        use AArch64Opcode::*;
        let bound_of = |operand: &MachOperand| match operand {
            MachOperand::Imm(value) => Some(GuardBound::Imm(*value)),
            MachOperand::VReg(value) => Some(GuardBound::Reg(*value)),
            _ => None,
        };
        match exit {
            LoopExit::Stop { block, index } => {
                // `TrapBoundsCheckExact [base, index, bound]` traps iff
                // `index >=u bound`.
                let inst = self.inst(self.block(block).insts[index]);
                match (inst.opcode, inst.operands.as_slice()) {
                    (TrapBoundsCheckExact, [_, MachOperand::VReg(checked), bound]) => {
                        Some(UnsignedGuard {
                            block,
                            at: index,
                            index: *checked,
                            bound: bound_of(bound)?,
                        })
                    }
                    _ => None,
                }
            }
            LoopExit::Edge { from, to } => {
                let insts = &self.block(from).insts;
                let inst_at = |position: usize| self.inst(insts[position]);
                let target_of = |inst: &trust_cg_ir::MachInst| {
                    inst.operands.iter().find_map(|operand| match operand {
                        MachOperand::Block(target) => Some(*target),
                        _ => None,
                    })
                };
                // The block's last instruction other than one trailing `B`
                // must be the conditional branch that decides the edge.
                let mut position = insts.len().checked_sub(1)?;
                let trailing_jump = inst_at(position).opcode == B;
                if trailing_jump {
                    position = position.checked_sub(1)?;
                }
                let branch = inst_at(position);
                let taken = target_of(branch)?;
                let otherwise = if trailing_jump {
                    target_of(inst_at(position + 1))
                } else {
                    fall_through
                };
                // Whether control takes this edge when the branch is taken,
                // or when it is not.
                let leaves_when_taken = if taken == to {
                    true
                } else if otherwise == Some(to) {
                    false
                } else {
                    return None;
                };
                let flags_before = |before: usize| {
                    (0..before).rev().find(|&index| {
                        let inst = inst_at(index);
                        writes_flags(inst.opcode) || inst.is_call()
                    })
                };
                // A register `flag` holding a `cset` result, tested for zero:
                // control leaves exactly when `flag == 0` (`zero`) or `!= 0`.
                let boolean_guard = |flag: VReg, before: usize, zero: bool| {
                    let (set_at, set_cc) =
                        aarch64_materialized_condition(self, insts, before, flag)?;
                    let leaves_on = if zero {
                        aarch64_negate(set_cc)?
                    } else {
                        set_cc
                    };
                    if leaves_on != AARCH64_HS {
                        return None;
                    }
                    let compare_at = flags_before(set_at)?;
                    unsigned_compare(inst_at(compare_at), from, compare_at)
                };
                match (branch.opcode, branch.operands.as_slice()) {
                    (BCond, [MachOperand::Imm(cc), _]) => {
                        let leaves_on = if leaves_when_taken {
                            *cc
                        } else {
                            aarch64_negate(*cc)?
                        };
                        let flags_from = flags_before(position)?;
                        let compare = inst_at(flags_from);
                        match (compare.opcode, compare.operands.as_slice()) {
                            // `cmp index, bound; b.hs out` (or `b.lo in; b out`).
                            (CmpRR | CmpRI, _) if leaves_on == AARCH64_HS => {
                                unsigned_compare(compare, from, flags_from)
                            }
                            // `cset f, lo; cmp f, #0; b.ne in; b out`.
                            (CmpRI, [MachOperand::VReg(flag), MachOperand::Imm(0)])
                                if leaves_on == AARCH64_EQ || leaves_on == AARCH64_NE =>
                            {
                                boolean_guard(*flag, flags_from, leaves_on == AARCH64_EQ)
                            }
                            _ => None,
                        }
                    }
                    // `cset f, lo; cbnz f, in; b out`, and the `cbz` spelling.
                    (Cbz | Cbnz, [MachOperand::VReg(flag), _]) => {
                        let taken_on_zero = branch.opcode == Cbz;
                        boolean_guard(*flag, position, taken_on_zero == leaves_when_taken)
                    }
                    _ => None,
                }
            }
        }
    }

    fn is_call(&self, block: Self::Block, index: usize) -> bool {
        self.inst(self.block(block).insts[index]).is_call()
    }

    fn is_indirect_branch(&self, block: Self::Block, index: usize) -> bool {
        self.inst(self.block(block).insts[index]).opcode == AArch64Opcode::Br
    }

    fn ends_without_successor(&self, block: Self::Block, index: usize) -> bool {
        let inst = self.inst(self.block(block).insts[index]);
        let names_block = inst
            .operands
            .iter()
            .any(|operand| matches!(operand, MachOperand::Block(_)));
        inst.is_return()
            || matches!(inst.opcode, AArch64Opcode::Brk | AArch64Opcode::Br)
            || (inst.opcode.is_trap_pseudo() && !names_block)
    }
}

// ---------------------------------------------------------------------------
// x86-64: X86ISelFunction
// ---------------------------------------------------------------------------

/// x86 opcodes that read or write a fixed register their operands do not
/// name: the `RDX:RAX` divide and multiply family, the `CL`-count shifts, the
/// compare-exchange family's accumulator, the stack, `PBLENDVB`'s `XMM0` mask,
/// and the pseudo-`Phi`.
fn x86_has_implicit_register_effect(opcode: X86Opcode) -> bool {
    use X86Opcode::*;
    matches!(
        opcode,
        Idiv | Div
            | Mul
            | Cdq
            | Cqo
            | ShlRR
            | ShrRR
            | SarRR
            | RolRCl
            | Cmpxchg
            | Cmpxchg8
            | Cmpxchg16
            | AtomicLoadCmpxchg16b
            | AtomicRmwCasLoop
            | AtomicRmwCasLoop8
            | AtomicRmwCasLoop16
            | Push
            | Pop
            | StackAlloc
            | Pblendvb
            | Phi
            | Call
            | CallR
            | CallM
            | Ret
    )
}

fn x86_operand_names_physical(operand: &X86ISelOperand) -> bool {
    match operand {
        X86ISelOperand::PReg(_) => true,
        X86ISelOperand::MemAddr { base, .. } => x86_operand_names_physical(base),
        X86ISelOperand::SibMemAddr { base, index, .. } => {
            x86_operand_names_physical(base) || x86_operand_names_physical(index)
        }
        _ => false,
    }
}

/// The condition code true exactly when `cc` is false, for the codes the
/// bounds-check view reads.
fn x86_negate(cc: X86CondCode) -> Option<X86CondCode> {
    match cc {
        X86CondCode::B => Some(X86CondCode::AE),
        X86CondCode::AE => Some(X86CondCode::B),
        X86CondCode::E => Some(X86CondCode::NE),
        X86CondCode::NE => Some(X86CondCode::E),
        _ => None,
    }
}

/// The nearest instruction before `before` that writes the flags (fully or
/// partly) or calls: the one whose flags an instruction at `before` reads.
fn x86_flag_writer_before(insts: &[X86ISelInst], before: usize) -> Option<usize> {
    (0..before).rev().find(|&index| {
        condition_flag_overwrite(&insts[index]) != FlagOverwrite::None
            || insts[index].flags.is_call()
    })
}

/// When `flag` holds, at instruction `before`, the 0/1 result of a `setcc`
/// in the same block: the `setcc`'s position and condition. The value may
/// pass through copies (`mov`), zero-extensions (`movzx`) and `and 1`, and at
/// least one `movzx` or `and 1` must clear the bits `setcc` leaves untouched.
fn x86_materialized_condition(
    insts: &[X86ISelInst],
    before: usize,
    flag: VReg,
) -> Option<(usize, X86CondCode)> {
    let mut value = flag;
    let mut position = before;
    let mut normalized = false;
    loop {
        // The nearest write of `value` before `position`.
        let def_at = (0..position)
            .rev()
            .find(|&index| x86_may_defined_vregs(&insts[index]).any(|d| d.id == value.id))?;
        let def = &insts[def_at];
        match (def.opcode, def.operands.as_slice()) {
            (X86Opcode::Setcc, [X86ISelOperand::VReg(d), X86ISelOperand::CondCode(cc)])
                if *d == value =>
            {
                return normalized.then_some((def_at, *cc));
            }
            (X86Opcode::Movzx, [X86ISelOperand::VReg(d), X86ISelOperand::VReg(s)])
                if *d == value =>
            {
                normalized = true;
                value = *s;
            }
            (X86Opcode::MovRR, [X86ISelOperand::VReg(d), X86ISelOperand::VReg(s)])
                if *d == value =>
            {
                value = *s;
            }
            (
                X86Opcode::AndRI,
                [
                    X86ISelOperand::VReg(d),
                    X86ISelOperand::VReg(s),
                    X86ISelOperand::Imm(1),
                ],
            ) if *d == value => {
                normalized = true;
                value = *s;
            }
            (X86Opcode::AndRI, [X86ISelOperand::VReg(d), X86ISelOperand::Imm(1)])
                if *d == value =>
            {
                normalized = true;
            }
            _ => return None,
        }
        position = def_at;
    }
}

fn x86_inst(
    func: &X86ISelFunction,
    block: trust_cg_lower::instructions::Block,
    index: usize,
) -> &X86ISelInst {
    &func.blocks[&block].insts[index]
}

impl LoopStateView for X86ISelFunction {
    fn trip_effects(
        &self,
        block: Self::Block,
        index: usize,
        out: &mut Vec<TripEffect<Self::Block>>,
    ) {
        trip_x86::trip_effects(x86_inst(self, block, index), out);
    }

    fn same_inst(
        &self,
        block: Self::Block,
        index: usize,
        other: &Self,
        other_block: Self::Block,
        other_index: usize,
        blocks: &dyn Fn(Self::Block) -> Self::Block,
    ) -> bool {
        let a = x86_inst(self, block, index);
        let b = x86_inst(other, other_block, other_index);
        a.opcode == b.opcode
            && a.flags == b.flags
            && a.proof_origin == b.proof_origin
            && a.call_arg_regs == b.call_arg_regs
            && a.call_result_regs == b.call_result_regs
            && a.internal_return_regs == b.internal_return_regs
            && a.operands.len() == b.operands.len()
            && a.operands.iter().zip(&b.operands).all(|pair| match pair {
                (X86ISelOperand::Block(x), X86ISelOperand::Block(y)) => blocks(*x) == *y,
                (X86ISelOperand::FImm(x), X86ISelOperand::FImm(y)) => x.to_bits() == y.to_bits(),
                (x, y) => x == y,
            })
    }

    fn visit_state_reads(&self, block: Self::Block, index: usize, visit: &mut dyn FnMut(StateReg)) {
        let inst = x86_inst(self, block, index);
        // Operand 0 of a value producer is a read only when the form ties it
        // (`[d, s]`, `[d, imm]`, a read-modify-write or a conditional write):
        // the precise per-form tie `x86_dce` uses for its own kill decisions,
        // not the over-approximation its liveness shares, which would count
        // `ShlRI d, s, #1` as reading `d` and refuse sound rewrites. A memory
        // operand in that slot still reads its address registers.
        let operand0_is_pure_def =
            x86_produces_value(inst.opcode) && !crate::x86_dce::redef_reads_operand0(inst);
        // A register several operands name is visited once per naming.
        let mut visit_virtual = |register: VReg| visit(StateReg::Virtual(register));
        for (position, operand) in inst.operands.iter().enumerate() {
            if position == 0 && operand0_is_pure_def {
                crate::x86_dce::for_each_address_vreg(operand, &mut visit_virtual);
            } else {
                crate::x86_dce::for_each_operand_vreg(operand, &mut visit_virtual);
            }
        }
        if x86_reads_flags(inst.opcode) {
            visit(StateReg::Flags);
        }
    }

    fn visit_state_writes(
        &self,
        block: Self::Block,
        index: usize,
        visit: &mut dyn FnMut(StateReg, StateWrite),
    ) {
        let inst = x86_inst(self, block, index);
        // The shared x86 def model. A tied, read-modify-write or conditional
        // write also reads its destination, so the read is seen first.
        for defined in x86_may_defined_vregs(inst) {
            visit(StateReg::Virtual(defined), StateWrite::Replaces);
        }
        match condition_flag_overwrite(inst) {
            FlagOverwrite::Full => visit(StateReg::Flags, StateWrite::Replaces),
            FlagOverwrite::Partial => visit(StateReg::Flags, StateWrite::MayModify),
            FlagOverwrite::None => {}
        }
    }

    fn names_virtual(&self, block: Self::Block, index: usize, reg: VReg) -> bool {
        let inst = x86_inst(self, block, index);
        if inst.opcode == X86Opcode::Phi {
            return true;
        }
        let mut names = false;
        for operand in &inst.operands {
            crate::x86_dce::for_each_operand_vreg(operand, &mut |named| {
                names |= named.id == reg.id;
            });
        }
        names
    }

    fn has_unmodeled_register_effect(&self, block: Self::Block, index: usize) -> bool {
        let inst = x86_inst(self, block, index);
        inst.flags.is_call()
            || !inst.call_arg_regs.is_empty()
            || x86_has_implicit_register_effect(inst.opcode)
            || inst.operands.iter().any(x86_operand_names_physical)
    }

    fn unsigned_guard(
        &self,
        exit: LoopExit<Self::Block>,
        fall_through: Option<Self::Block>,
    ) -> Option<UnsignedGuard<Self::Block>> {
        use X86Opcode::*;
        let bound_of = |operand: &X86ISelOperand| match operand {
            X86ISelOperand::Imm(value) => Some(GuardBound::Imm(*value)),
            X86ISelOperand::VReg(value) => Some(GuardBound::Reg(*value)),
            _ => None,
        };
        let target_of = |inst: &X86ISelInst| {
            inst.operands.iter().find_map(|operand| match operand {
                X86ISelOperand::Block(target) => Some(*target),
                _ => None,
            })
        };
        match exit {
            LoopExit::Stop { block, index } => {
                // `TrapBoundsCheckExact [base, index, bound]` expands to
                // `CMP index, bound; JAE -> UD2`.
                let inst = x86_inst(self, block, index);
                match (inst.opcode, inst.operands.as_slice()) {
                    (TrapBoundsCheckExact, [_, X86ISelOperand::VReg(checked), bound]) => {
                        Some(UnsignedGuard {
                            block,
                            at: index,
                            index: *checked,
                            bound: bound_of(bound)?,
                        })
                    }
                    _ => None,
                }
            }
            LoopExit::Edge { from, to } => {
                let insts = &self.blocks.get(&from)?.insts;
                let mut position = insts.len().checked_sub(1)?;
                let trailing_jump = insts[position].opcode == Jmp;
                if trailing_jump {
                    position = position.checked_sub(1)?;
                }
                let branch = &insts[position];
                if branch.opcode != Jcc {
                    return None;
                }
                let X86ISelOperand::CondCode(cc) = *branch.operands.first()? else {
                    return None;
                };
                let taken = target_of(branch)?;
                let otherwise = if trailing_jump {
                    target_of(&insts[position + 1])
                } else {
                    fall_through
                };
                // The condition, on the flags the branch reads, under which
                // control takes this edge.
                let leaves_on = if taken == to {
                    cc
                } else if otherwise == Some(to) {
                    x86_negate(cc)?
                } else {
                    return None;
                };
                let flags_from = x86_flag_writer_before(insts, position)?;
                let compare = &insts[flags_from];
                match (compare.opcode, compare.operands.as_slice()) {
                    // `cmp index, bound; jae out` (or `jb in; jmp out`).
                    (CmpRR | CmpRI | CmpRI8, [X86ISelOperand::VReg(checked), bound])
                        if leaves_on == X86CondCode::AE =>
                    {
                        Some(UnsignedGuard {
                            block: from,
                            at: flags_from,
                            index: *checked,
                            bound: bound_of(bound)?,
                        })
                    }
                    // The raw-isel guard diamond: `cmp index, bound; setb s;
                    // movzx/and 1 ..; cmp s, 0; jne in; jmp out`. The branch
                    // tests a 0/1 register the `setcc` materialized from the
                    // index compare.
                    (CmpRI | CmpRI8, [X86ISelOperand::VReg(flag), X86ISelOperand::Imm(0)]) => {
                        let (set_at, set_cc) =
                            x86_materialized_condition(insts, flags_from, *flag)?;
                        // `flag == 0` exactly when the `setcc` condition fails.
                        let leaves_on_compare = match leaves_on {
                            X86CondCode::E => x86_negate(set_cc)?,
                            X86CondCode::NE => set_cc,
                            _ => return None,
                        };
                        if leaves_on_compare != X86CondCode::AE {
                            return None;
                        }
                        let compare_at = x86_flag_writer_before(insts, set_at)?;
                        let compare = &insts[compare_at];
                        match (compare.opcode, compare.operands.as_slice()) {
                            (CmpRR | CmpRI | CmpRI8, [X86ISelOperand::VReg(checked), bound]) => {
                                Some(UnsignedGuard {
                                    block: from,
                                    at: compare_at,
                                    index: *checked,
                                    bound: bound_of(bound)?,
                                })
                            }
                            _ => None,
                        }
                    }
                    _ => None,
                }
            }
        }
    }

    fn is_call(&self, block: Self::Block, index: usize) -> bool {
        x86_inst(self, block, index).flags.is_call()
    }

    fn is_indirect_branch(&self, block: Self::Block, index: usize) -> bool {
        x86_inst(self, block, index).opcode == X86Opcode::JmpR
    }

    fn ends_without_successor(&self, block: Self::Block, index: usize) -> bool {
        use X86Opcode::*;
        let inst = x86_inst(self, block, index);
        inst.flags.is_return()
            || matches!(
                inst.opcode,
                Ret | Ud2
                    | JmpR
                    | TrapBoundsCheckExact
                    | TrapNullIfZeroExact
                    | TrapDivZeroExact
                    | TrapShiftRangeExact
            )
    }
}

#[cfg(test)]
pub(crate) mod test_support;
#[cfg(test)]
mod tests;
