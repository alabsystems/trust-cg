// trust-cg-opt - x86-64 loop-top selection (latch above the header)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Place a two-arm in-loop diamond's LATCH immediately before its HEADER, so
//! the backedge becomes a fall-through and the loop costs ONE taken branch per
//! iteration instead of two.
//!
//! # 🛑 MEASURED AND REFUTED on the program it was built for (2026-09-30)
//!
//! The pass does exactly what it claims and what LLVM does. It is still a
//! 4.7% LOSS, so it is DEFAULT OFF on a measurement, not on a guess:
//!
//! ```text
//!   b1_mispredict, 90 interleaved rounds, taskset -c 2, min statistic,
//!   both arms carried twice as byte-identical copies:
//!
//!     llvm   190.276 ms   1.0000
//!     off    208.201 ms   1.0942      <- default
//!     off2   208.254 ms   1.0945      <- noise floor 0.0003
//!     on     217.930 ms   1.1453      <- this pass
//!     on2    217.936 ms   1.1454      <- noise floor 0.0001
//! ```
//!
//! The transform's own claim VERIFIED in the emitted binary: the loop went from
//! two taken branches per iteration on both paths to ONE, LLVM's count, with
//! the latch's backedge an elided fall-through.
//!
//! It loses anyway, because the reorder also cost 2 instructions (38 -> 40 in
//! the loop body): the orientation flips changed which values are live across
//! the new fall-throughs and the allocator paid for it. On a loop whose branch
//! is UNPREDICTABLE by construction, a saved *taken* branch on the perfectly
//! predicted backedge is worth less than two instructions.
//!
//! So the taken-branch count is NOT b1's gap. The gap is instruction count —
//! 38 against LLVM's 33 — and the five instructions decompose (see
//! `reports/perf/2026-09-30-loop-top-refuted/`) into:
//!
//!   * 3 — commutative two-address operand selection. `s ^= s >> 7` lowers to
//!     `mov t,s ; shr t ; mov d,s ; xor d,t` where LLVM emits
//!     `mov t,s ; shr t ; xor t,s`: XOR is commutative and `t` dies, so the
//!     dying operand can be the tied destination and the copy of the LIVE
//!     operand disappears. Twice in the xorshift, once in the odd arm.
//!   * 1 — one reusable copy of `s`. LLVM makes it once in the header and
//!     consumes it destructively in whichever arm runs; this backend re-copies
//!     `s` in each arm.
//!   * 1 — demanded bits through `x ^ (x << k)`. The low `k` bits are
//!     unchanged, so LLVM tests `s & 6` on the *earlier*, dead value
//!     (`and $0x6,%r8d`) where this backend must copy the live one first.
//!
//! Keep this pass REACHABLE rather than deleted: it is the only way to re-run
//! the experiment if b1's shape or the allocator changes, and a default-off
//! lever with a measurement attached is a different thing from a parked guess.
//!
//! # The deficit it was built to close (real, just not the cause)
//!
//! `b1_mispredict`'s hot loop, every branch counted from the disassembly of
//! both compilers:
//!
//! ```text
//!   trust-cg  0x2095b..0x209ee, 38 insns
//!     0x20984  jb  -> 0x209ad   forward   header picks an arm
//!     0x209a8  jmp -> 0x209cd   forward   arm B must JUMP to the latch
//!     0x209ee  jb  -> 0x2095b   BACK      latch JUMPS back to the header
//!     => path A: jb taken + backedge taken           = 2 taken
//!        path B: jmp taken + backedge taken          = 2 taken
//!
//!   LLVM      0x20880..0x208eb, 33 insns, [even-arm, latch, header, odd-arm]
//!     0x208ad  je  -> 0x208ed   EXIT, not taken in steady state
//!     0x208d4  je  -> 0x20880   BACK      header -> even-arm
//!     0x208eb  jmp -> 0x20894   BACK      odd-arm -> latch
//!     => either path                                 = 1 taken
//! ```
//!
//! LLVM's order makes `arm -> latch` and `latch -> header` BOTH fall-throughs.
//!
//! # Provenance
//!
//! LLVM's rule is `MachineBlockPlacement::findBestLoopTopHelper`
//! (`llvm/lib/CodeGen/MachineBlockPlacement.cpp:2167`), pattern 2 of its own doc
//! comment at :2155-2166:
//!
//! > "a block has two successors, one is old top, another is exit and it has
//! > more than one predecessors ... If it is moved before loop header, all its
//! > predecessors jump to it, then fall through to loop header. So all its
//! > predecessors except P can reduce one taken branch."
//!
//! Iteration 1 promotes the LATCH above the header (two successors = header +
//! exit, two predecessors = the arms); iteration 2 promotes an arm above the
//! latch by pattern 1 ("only one successor, the old loop top").
//! `ComputedEdges[NewTop] = {OldTop, false}` (:2254) then forces the chain.
//!
//! ⚑ This is NOT tail duplication. `llc -O3`, `-tail-dup-placement=false` and
//! `-disable-tail-duplicate` emit BYTE-IDENTICAL assembly for b1, and b1's latch
//! sequence appears exactly ONCE in that output. An earlier pass in this repo
//! (`x86_latch_dup`) was built on reading b1's two backedges as a duplication
//! signature; they are a LAYOUT artifact of this transform, because the header
//! ends up in the middle of the laid-out loop.
//!
//! # ⚑ The tension with the latch rule, and where it actually bit
//!
//! `x86_branch_layout`'s LATCH RULE (default ON, credited `b1_mispredict -13%`)
//! puts the backedge on the CONDITIONAL branch, so a latch ends `jcc header`
//! and falls through to the exit. That is the best arrangement while the latch
//! sits AFTER the header, and the exact inverse of what this transform needs.
//!
//! Registering this pass after `X86BranchLayout` is NOT enough, and that is the
//! part worth remembering: at O3 the pass manager runs `run_to_fixpoint`, so
//! branch layout runs AGAIN on the reordered function and swaps the pair back.
//! The first build of this pass measured with the reorder applied and the latch
//! re-inverted — the worst of both — and the emitted orientation depended on
//! the parity of the iteration budget.
//!
//! The fix is in the latch rule itself, where it belongs: its premise is that a
//! backedge riding the unconditional `jmp` costs a taken branch, and that is
//! false when the `jmp` target is the layout successor, because the encoder
//! elides it. `latch_rule && !exit.jump_is_layout_next` — the same guard the
//! generic fall-through rule already carried, for the same reason.
//!
//! # Correctness
//!
//! The transform PERMUTES `block_order` and rewrites two branch pairs in place.
//! No instruction is added, removed or moved between blocks, and no operand
//! other than a branch target or condition code changes.
//!
//! * `block_order` stays a permutation of itself: the four blocks occupy the
//!   same four slots, reordered. So it still begins at the entry block, still
//!   contains no duplicate, and is still closed under the CFG — the invariants
//!   `validate_x86_function_layout` enforces.
//! * Every edge is preserved. The reorder changes only which edges are
//!   fall-throughs; `resolve_x86_branches` elides a `Jmp` to the layout
//!   successor, which is where the saving comes from.
//! * A branch-pair inversion `Jcc cc,T ; Jmp F` -> `Jcc cc.invert(),F ; Jmp T`
//!   preserves the successor SET and the instruction count, and is gated by the
//!   caller's `admit_inversion` so a condition code whose inversion is not
//!   proof-admissible declines the whole candidate.
//! * The loop is entered through the HEADER, which is now mid-run. The
//!   preheader's branch names the header explicitly and is untouched, so entry
//!   still lands there — exactly as LLVM's preheader does `jmp 208af` into the
//!   middle of its loop. The entry cost is one taken branch ONCE, against a
//!   per-iteration saving.
//!
//! # What is deliberately NOT done
//!
//! Only the single shape above: one header, one latch, exactly two arms, all
//! four contiguous in layout. LLVM's version iterates over an arbitrary chain
//! and consults block frequencies; this takes the one shape whose benefit is
//! countable without a profile, because every taken-branch count above is a
//! fact about the CFG rather than an estimate.

use std::collections::BTreeSet;

use trust_cg_ir::x86_64_ops::{X86CondCode, X86Opcode};
use trust_cg_lower::instructions::Block;
use trust_cg_lower::{X86ISelFunction, X86ISelOperand};

use crate::mach_view::{compute_idom, compute_rpo, find_natural_loops, predecessor_map};
use crate::x86_branch_layout::CcInversionAdmit;

static LOOP_TOP: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
static LOOP_TOP_TRACE: std::sync::OnceLock<bool> = std::sync::OnceLock::new();

/// Install this pass from a TRACKED compiler option
/// (`-Ztrust-ir-cg-args=x86-loop-top`). DEFAULT OFF.
pub fn set_x86_loop_top_enabled(enabled: bool) -> bool {
    match LOOP_TOP.set(enabled) {
        Ok(()) => true,
        Err(requested) => LOOP_TOP.get() == Some(&requested),
    }
}

fn loop_top_enabled() -> bool {
    LOOP_TOP.get().copied().unwrap_or(false) || crate::tcg_env_flag("TCG_X86_LOOP_TOP")
}

/// Install the trace (`-Ztrust-ir-cg-args=trace-x86-loop-top`).
pub fn set_x86_loop_top_trace_enabled(enabled: bool) -> bool {
    match LOOP_TOP_TRACE.set(enabled) {
        Ok(()) => true,
        Err(requested) => LOOP_TOP_TRACE.get() == Some(&requested),
    }
}

/// Should the pipeline REGISTER this pass at all? Same gate as `loop_top_enabled`:
/// the pass is a no-op when off, but registering it anyway would change the
/// default pass schedule, which `default_x86_pass_manager_runs_*` and
/// `x86_branch_layout_kill_switch_removes_only_that_pass` pin on purpose. An
/// opt-in pass must leave the default schedule byte-identical.
pub fn x86_loop_top_registered() -> bool {
    loop_top_enabled()
}

fn trace_enabled() -> bool {
    LOOP_TOP_TRACE.get().copied().unwrap_or(false) || crate::tcg_env_flag("TCG_X86_LOOP_TOP_TRACE")
}

/// The terminal `Jcc cc, T ; Jmp F` pair of a block, as (cond index, cc, T, F).
fn terminal_pair(func: &X86ISelFunction, b: Block) -> Option<(usize, X86CondCode, Block, Block)> {
    let block = func.blocks.get(&b)?;
    let n = block.insts.len();
    if n < 2 {
        return None;
    }
    let jmp = &block.insts[n - 1];
    let jcc = &block.insts[n - 2];
    if jmp.opcode != X86Opcode::Jmp || jcc.opcode != X86Opcode::Jcc {
        return None;
    }
    if jmp.proof_origin.is_some() || jcc.proof_origin.is_some() {
        return None;
    }
    let [X86ISelOperand::CondCode(cc), X86ISelOperand::Block(t)] = jcc.operands.as_slice() else {
        return None;
    };
    let [X86ISelOperand::Block(f)] = jmp.operands.as_slice() else {
        return None;
    };
    Some((n - 2, *cc, *t, *f))
}

/// Rewrite a terminal pair so `want_fallthrough` is the trailing `Jmp`'s target
/// (and therefore elidable once it is the layout successor). Operand-only, so
/// flags, provenance and proof origin are untouched; the successor SET is
/// unchanged by construction.
fn orient_pair(
    func: &mut X86ISelFunction,
    b: Block,
    want_fallthrough: Block,
    admit_inversion: &dyn Fn(X86CondCode, X86CondCode) -> bool,
) -> bool {
    let Some((idx, cc, t, f)) = terminal_pair(func, b) else {
        return false;
    };
    if f == want_fallthrough {
        return true; // already oriented
    }
    if t != want_fallthrough {
        return false; // neither edge is the one we want
    }
    let inverted = cc.invert();
    if !admit_inversion(cc, inverted) {
        return false;
    }
    let before: Vec<Block> = func.blocks[&b].successors.clone();
    let count_before = func.blocks[&b].insts.len();
    let block = func.blocks.get_mut(&b).expect("checked above");
    block.insts[idx].operands = vec![X86ISelOperand::CondCode(inverted), X86ISelOperand::Block(f)];
    block.insts[idx + 1].operands = vec![X86ISelOperand::Block(t)];
    // Structural self-check: an inversion must not change the edge set or the
    // instruction count. Both are guaranteed by construction above, so a
    // violation is corruption rather than a policy question.
    assert_eq!(func.blocks[&b].insts.len(), count_before);
    assert_eq!(
        func.blocks[&b].successors.iter().collect::<BTreeSet<_>>(),
        before.iter().collect::<BTreeSet<_>>(),
        "pair inversion changed the successor set"
    );
    true
}

/// Can [`orient_pair`] succeed on `b`, without mutating anything? Both pairs
/// are probed before either is rewritten: a candidate that orients the latch
/// and then declines the header would leave the latch inverted with NO reorder,
/// which undoes `x86_branch_layout`'s latch rule for no benefit at all.
fn can_orient(
    func: &X86ISelFunction,
    b: Block,
    want_fallthrough: Block,
    admit_inversion: &dyn Fn(X86CondCode, X86CondCode) -> bool,
) -> bool {
    match terminal_pair(func, b) {
        Some((_, _, _, f)) if f == want_fallthrough => true,
        Some((_, cc, t, _)) if t == want_fallthrough => admit_inversion(cc, cc.invert()),
        _ => false,
    }
}

/// A candidate: the four blocks and the contiguous layout slot they occupy.
struct Candidate {
    header: Block,
    latch: Block,
    arm_first: Block,
    arm_second: Block,
    exit: Block,
    start: usize,
}

/// Move the latch above the header for two-arm in-loop diamonds. Returns true
/// if the function changed.
pub fn run_on_function(
    func: &mut X86ISelFunction,
    admit_inversion: &dyn Fn(X86CondCode, X86CondCode) -> bool,
) -> bool {
    if !loop_top_enabled() {
        return false;
    }
    run_scoped(func, admit_inversion, trace_enabled())
}

fn run_scoped(
    func: &mut X86ISelFunction,
    admit_inversion: &dyn Fn(X86CondCode, X86CondCode) -> bool,
    trace: bool,
) -> bool {
    let preds = predecessor_map(func);
    let rpo = compute_rpo(func);
    let idom = compute_idom(func, &preds, &rpo);
    let loops = find_natural_loops(func, &preds, &idom);
    let index = |b: Block| func.block_order.iter().position(|x| *x == b);

    let mut plans: Vec<Candidate> = Vec::new();
    for lp in &loops {
        let decline = |why: &str| {
            if trace {
                eprintln!(
                    "x86-loop-top[{}/hdr={:?}]: declined — {why}",
                    func.name, lp.header
                );
            }
        };
        if lp.latches.len() != 1 {
            decline(&format!("{} latches, need exactly 1", lp.latches.len()));
            continue;
        }
        let (h, l) = (lp.header, lp.latches[0]);
        if h == l {
            decline("single-block loop");
            continue;
        }
        let Some(hb) = func.blocks.get(&h) else {
            continue;
        };
        if hb.successors.len() != 2 {
            decline(&format!("header has {} successors", hb.successors.len()));
            continue;
        }
        let (a1, a2) = (hb.successors[0], hb.successors[1]);
        if !lp.body.contains(&a1) || !lp.body.contains(&a2) {
            decline("a header successor leaves the loop (not a diamond)");
            continue;
        }
        // Each arm: exactly one successor, the latch.
        if [a1, a2].iter().any(|arm| {
            func.blocks
                .get(arm)
                .is_none_or(|b| b.successors.as_slice() != [l])
        }) {
            decline("an arm is not a single-successor block targeting the latch");
            continue;
        }
        // The latch: exactly two successors, the header and one exit.
        let Some(lb) = func.blocks.get(&l) else {
            continue;
        };
        if lb.successors.len() != 2 || !lb.successors.contains(&h) {
            decline("latch is not a two-successor block targeting the header");
            continue;
        }
        let exit = lb.successors.iter().copied().find(|s| *s != h).unwrap();
        if lp.body.contains(&exit) {
            decline("the latch's other successor is inside the loop");
            continue;
        }
        // Predecessor sets must be exactly as the shape requires, so nothing
        // else can enter mid-loop and observe the new fall-throughs.
        let empty = Vec::new();
        let lpreds: BTreeSet<Block> = preds.get(&l).unwrap_or(&empty).iter().copied().collect();
        if lpreds != [a1, a2].into_iter().collect() {
            decline("the latch has predecessors other than the two arms");
            continue;
        }
        let hpreds: BTreeSet<Block> = preds.get(&h).unwrap_or(&empty).iter().copied().collect();
        let outside: Vec<Block> = hpreds.iter().copied().filter(|p| *p != l).collect();
        if outside.len() != 1 {
            decline(&format!(
                "header has {} out-of-loop predecessors, need exactly 1 (a preheader)",
                outside.len()
            ));
            continue;
        }
        // All four contiguous in layout, with the header FIRST (the frontend's
        // top-tested shape). Anything else is a layout this pass did not
        // predict, and reordering it blind is how an edge gets lost.
        let (Some(ih), Some(il), Some(i1), Some(i2)) = (index(h), index(l), index(a1), index(a2))
        else {
            continue;
        };
        let mut slots = [ih, il, i1, i2];
        slots.sort_unstable();
        if slots[3] - slots[0] != 3 || slots[0] != ih {
            decline(&format!(
                "the four blocks are not contiguous with the header first \
                 (header={ih}, latch={il}, arms={i1}/{i2})"
            ));
            continue;
        }
        // Keep the arms in their existing relative order; the FIRST one becomes
        // the new loop top and falls through into the latch.
        let (arm_first, arm_second) = if i1 < i2 { (a1, a2) } else { (a2, a1) };
        plans.push(Candidate {
            header: h,
            latch: l,
            arm_first,
            arm_second,
            exit,
            start: ih,
        });
    }

    // Overlapping windows: a stale `start` after an earlier permutation would
    // scramble `block_order`, which is a MISCOMPILE, not a missed optimization.
    // Rather than argue from the CFG that two candidate windows cannot overlap,
    // sort by slot and keep only a disjoint set.
    plans.sort_unstable_by_key(|c| c.start);
    let mut disjoint: Vec<Candidate> = Vec::new();
    for c in plans {
        if disjoint.last().is_some_and(|prev| prev.start + 4 > c.start) {
            if trace {
                eprintln!(
                    "x86-loop-top[{}/hdr={:?}]: declined — its layout window overlaps an \
                     accepted candidate's",
                    func.name, c.header
                );
            }
            continue;
        }
        disjoint.push(c);
    }

    let mut changed = false;
    for c in &disjoint {
        // Probe BOTH orientations before rewriting either: the latch must fall
        // through to the HEADER (the inverse of the latch rule's arrangement)
        // and the header to its SECOND arm, so the header's conditional edge is
        // the backward one to the new loop top.
        let latch_ok = can_orient(func, c.latch, c.header, admit_inversion);
        let header_ok = can_orient(func, c.header, c.arm_second, admit_inversion);
        if !latch_ok || !header_ok {
            if trace {
                eprintln!(
                    "x86-loop-top[{}/hdr={:?}]: declined — cannot orient the {} as a \
                     `Jcc ; Jmp` pair falling through to {:?} (exit={:?})",
                    func.name,
                    c.header,
                    if latch_ok { "header" } else { "latch" },
                    if latch_ok { c.arm_second } else { c.header },
                    c.exit
                );
            }
            continue;
        }
        // Both probed admissible, so neither of these can fail now.
        assert!(
            orient_pair(func, c.latch, c.header, admit_inversion),
            "probed admissible"
        );
        assert!(
            orient_pair(func, c.header, c.arm_second, admit_inversion),
            "probed admissible"
        );
        // Permute the four contiguous slots into [arm_first, latch, header, arm_second].
        let order = [c.arm_first, c.latch, c.header, c.arm_second];
        let window = &mut func.block_order[c.start..c.start + 4];
        let mut expected = [c.header, c.latch, c.arm_first, c.arm_second];
        expected.sort_unstable_by_key(|b| b.0);
        let mut found = window.to_vec();
        found.sort_unstable_by_key(|b| b.0);
        assert_eq!(
            found, expected,
            "the candidate's layout window no longer holds its four blocks"
        );
        window.copy_from_slice(&order);
        changed = true;
        if trace {
            eprintln!(
                "x86-loop-top[{}/hdr={:?}]: laid out [{:?}, {:?}, {:?}, {:?}] — latch now falls \
                 through to the header, {:?} falls through to the latch",
                func.name, c.header, order[0], order[1], order[2], order[3], c.arm_first
            );
        }
    }
    changed
}

/// x86-64 loop-top selection pass. See the module docs.
///
/// MUST be registered AFTER `X86BranchLayout`: it reads the layout that pass
/// chose and re-inverts the latch pair that pass's latch rule produced, so
/// running it first would let the latch rule undo the reorder's fall-through.
pub struct X86LoopTop {
    admit_inversion: CcInversionAdmit,
}

impl X86LoopTop {
    /// Build the pass with the embedder's condition-code inversion policy.
    pub fn new(admit_inversion: CcInversionAdmit) -> Self {
        Self { admit_inversion }
    }
}

impl crate::x86_pass_manager::X86MachinePass for X86LoopTop {
    fn name(&self) -> &str {
        "x86-loop-top"
    }

    fn run(&mut self, func: &mut X86ISelFunction) -> bool {
        let admit = self.admit_inversion;
        run_on_function(func, &admit)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_cg_lower::X86ISelInst;
    use trust_cg_lower::function::Signature;

    const ENTRY: Block = Block(0);
    const HEADER: Block = Block(1);
    const ARM_A: Block = Block(2);
    const ARM_B: Block = Block(3);
    const LATCH: Block = Block(4);
    const EXIT: Block = Block(5);

    fn admit_all(_: X86CondCode, _: X86CondCode) -> bool {
        true
    }
    fn jmp(to: Block) -> X86ISelInst {
        X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(to)])
    }
    fn jcc(cc: X86CondCode, to: Block) -> X86ISelInst {
        X86ISelInst::new(
            X86Opcode::Jcc,
            vec![X86ISelOperand::CondCode(cc), X86ISelOperand::Block(to)],
        )
    }

    /// The top-tested two-arm diamond the frontend emits, laid out
    /// [entry, header, arm_a, arm_b, latch, exit]. The latch carries the
    /// backedge on its CONDITIONAL branch, which is what the latch rule
    /// produces and the inverse of what this pass needs.
    fn build() -> X86ISelFunction {
        let sig = Signature {
            params: vec![],
            returns: vec![],
        };
        let mut func = X86ISelFunction::new("loop_top_test".to_string(), sig);
        for b in [ENTRY, HEADER, ARM_A, ARM_B, LATCH, EXIT] {
            func.ensure_block(b);
        }
        {
            let e = func.blocks.get_mut(&ENTRY).unwrap();
            e.insts.push(jmp(HEADER));
            e.successors = vec![HEADER];
        }
        {
            let h = func.blocks.get_mut(&HEADER).unwrap();
            h.insts.push(jcc(X86CondCode::B, ARM_A));
            h.insts.push(jmp(ARM_B));
            h.successors = vec![ARM_A, ARM_B];
        }
        for arm in [ARM_A, ARM_B] {
            let a = func.blocks.get_mut(&arm).unwrap();
            a.insts.push(jmp(LATCH));
            a.successors = vec![LATCH];
        }
        {
            // `jcc header ; jmp exit` — the latch rule's arrangement.
            let l = func.blocks.get_mut(&LATCH).unwrap();
            l.insts.push(jcc(X86CondCode::B, HEADER));
            l.insts.push(jmp(EXIT));
            l.successors = vec![HEADER, EXIT];
        }
        {
            let x = func.blocks.get_mut(&EXIT).unwrap();
            x.insts.push(X86ISelInst::new(X86Opcode::Ret, vec![]));
        }
        func
    }

    /// The trailing `Jmp` target of a block: the edge that becomes a
    /// fall-through once it is the layout successor.
    fn jmp_target(func: &X86ISelFunction, b: Block) -> Option<Block> {
        match func.blocks[&b].insts.last()?.operands.first()? {
            X86ISelOperand::Block(t) => Some(*t),
            _ => None,
        }
    }

    /// Taken branches per iteration on each path, as a pure LAYOUT measure: the
    /// steady-state loop walks `header -> arm -> latch -> header`, and an edge
    /// costs nothing exactly when its target is the layout successor of its
    /// source. Orientation does not enter the count (a taken `jcc` and a taken
    /// `jmp` cost the same); it is asserted separately, because it decides
    /// whether the redundant branch is elided at all.
    fn taken_per_path(func: &X86ISelFunction) -> (usize, usize) {
        let pos = |b: Block| func.block_order.iter().position(|x| *x == b).unwrap();
        let cost = |from: Block, to: Block| usize::from(pos(from) + 1 != pos(to));
        let path = |arm: Block| cost(HEADER, arm) + cost(arm, LATCH) + cost(LATCH, HEADER);
        (path(ARM_A), path(ARM_B))
    }

    #[test]
    fn reorders_the_latch_above_the_header() {
        let mut func = build();
        let (a0, b0) = taken_per_path(&func);
        assert_eq!(
            (a0, b0),
            (2, 2),
            "the fixture must START at two taken branches per path, or the test is vacuous"
        );

        assert!(run_scoped(&mut func, &admit_all, false));

        assert_eq!(
            func.block_order,
            vec![ENTRY, ARM_A, LATCH, HEADER, ARM_B, EXIT],
            "LLVM's order: [arm, latch, header, arm]"
        );
        // The latch now falls through to the HEADER — the inverse of the latch
        // rule's arrangement, which this pass re-inverts itself.
        assert_eq!(jmp_target(&func, LATCH), Some(HEADER));
        // And ARM_A falls through into the latch, and the header into ARM_B, so
        // `resolve_x86_branches` elides all three `Jmp`s rather than leaving a
        // taken branch standing next to a not-taken conditional.
        assert_eq!(jmp_target(&func, ARM_A), Some(LATCH));
        assert_eq!(jmp_target(&func, HEADER), Some(ARM_B));
        // Edge sets are untouched.
        assert_eq!(
            func.blocks[&LATCH]
                .successors
                .iter()
                .copied()
                .collect::<BTreeSet<_>>(),
            [HEADER, EXIT].into_iter().collect::<BTreeSet<_>>()
        );

        let (a1, b1) = taken_per_path(&func);
        assert_eq!(
            (a1, b1),
            (1, 1),
            "ONE taken branch per iteration on either path — LLVM's count"
        );
    }

    #[test]
    fn layout_invariants_hold_after_the_permutation() {
        let mut func = build();
        assert!(run_scoped(&mut func, &admit_all, false));
        assert_eq!(func.block_order.first().copied(), Some(ENTRY));
        let mut seen = BTreeSet::new();
        assert!(
            func.block_order.iter().all(|b| seen.insert(*b)),
            "block_order must stay duplicate-free"
        );
        assert_eq!(func.block_order.len(), 6, "a permutation, not a resize");
        for b in &func.block_order {
            for s in &func.blocks[b].successors {
                assert!(seen.contains(s), "successor {s:?} must be laid out");
            }
        }
    }

    #[test]
    fn declines_when_a_condition_inversion_is_not_admissible() {
        let mut func = build();
        assert!(
            !run_scoped(&mut func, &|_, _| false, false),
            "a refused condition-code inversion must abandon the candidate"
        );
        assert_eq!(
            func.block_order,
            vec![ENTRY, HEADER, ARM_A, ARM_B, LATCH, EXIT],
            "and leave the layout untouched"
        );
    }

    #[test]
    fn declines_an_arm_with_two_successors() {
        let mut func = build();
        {
            let a = func.blocks.get_mut(&ARM_A).unwrap();
            a.insts.pop();
            a.insts.push(jcc(X86CondCode::B, LATCH));
            a.insts.push(jmp(EXIT));
            a.successors = vec![LATCH, EXIT];
        }
        assert!(!run_scoped(&mut func, &admit_all, false));
    }

    #[test]
    fn declines_when_the_latch_has_a_third_predecessor() {
        let mut func = build();
        // A block outside the diamond jumping straight at the latch would
        // observe the new fall-throughs without passing through an arm.
        let side = Block(6);
        func.ensure_block(side);
        {
            let s = func.blocks.get_mut(&side).unwrap();
            s.insts.push(jmp(LATCH));
            s.successors = vec![LATCH];
        }
        {
            let e = func.blocks.get_mut(&ENTRY).unwrap();
            e.insts.pop();
            e.insts.push(jcc(X86CondCode::B, HEADER));
            e.insts.push(jmp(side));
            e.successors = vec![HEADER, side];
        }
        assert!(!run_scoped(&mut func, &admit_all, false));
    }

    #[test]
    fn declines_when_the_four_blocks_are_not_contiguous() {
        let mut func = build();
        // Park an unrelated block between the header and the arms.
        let filler = Block(7);
        func.ensure_block(filler);
        let hpos = func.block_order.iter().position(|b| *b == HEADER).unwrap();
        func.block_order.retain(|b| *b != filler);
        func.block_order.insert(hpos + 1, filler);
        assert!(!run_scoped(&mut func, &admit_all, false));
    }

    #[test]
    fn is_off_by_default() {
        let mut func = build();
        assert!(!run_on_function(&mut func, &admit_all));
        assert_eq!(func.block_order[1], HEADER, "layout untouched");
    }

    #[test]
    fn a_declined_header_leaves_the_latch_pair_untouched() {
        // The regression this guards: orienting the latch and THEN declining the
        // header would undo `x86_branch_layout`'s latch rule (backedge on the
        // conditional) while delivering none of the reorder's saving — strictly
        // worse than not running at all.
        let mut func = build();
        // Make the header need an inversion too, on a DIFFERENT condition code,
        // and admit only the latch's.
        {
            let h = func.blocks.get_mut(&HEADER).unwrap();
            h.insts.clear();
            h.insts.push(jcc(X86CondCode::E, ARM_B));
            h.insts.push(jmp(ARM_A));
        }
        let before = func.blocks[&LATCH].insts.clone();
        let admit_b_only = |original: X86CondCode, _: X86CondCode| original == X86CondCode::B;

        assert!(!run_scoped(&mut func, &admit_b_only, false));

        assert_eq!(
            func.block_order,
            vec![ENTRY, HEADER, ARM_A, ARM_B, LATCH, EXIT],
            "layout untouched"
        );
        let after = &func.blocks[&LATCH].insts;
        assert_eq!(after.len(), before.len());
        for (a, b) in after.iter().zip(before.iter()) {
            assert_eq!(a.opcode, b.opcode);
            assert_eq!(
                a.operands, b.operands,
                "the latch pair must be byte-for-byte as it was"
            );
        }
    }
}
