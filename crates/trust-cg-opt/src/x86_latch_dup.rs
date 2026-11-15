// trust-cg-opt - x86-64 loop-latch duplication into diamond arms
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Clone a small loop LATCH into each arm of an in-loop two-way diamond, so
//! every arm carries its own copy of the counter update and its own backedge.
//!
//! # The shape, and why this pass exists
//!
//! ```text
//!   header:  s = xorshift(s) ; test s,1 ; jcc arm_a ; jmp arm_b
//!   arm_a:   t[j] += acc     ; jmp latch
//!   arm_b:   t[j] ^= acc     ; jmp latch
//!   latch:   j = j + 1 ; cmp j,K ; jb header ; jmp exit
//! ```
//!
//! becomes
//!
//! ```text
//!   header:  s = xorshift(s) ; test s,1 ; jcc arm_a ; jmp arm_b
//!   arm_a:   t[j] += acc     ; j = j + 1 ; cmp j,K ; jb header ; jmp exit
//!   arm_b:   t[j] ^= acc     ; jmp latch
//!   latch:   j = j + 1 ; cmp j,K ; jb header ; jmp exit
//! ```
//!
//! i.e. the arm that is NOT the latch's layout predecessor gets a verbatim copy
//! of the latch and stops branching to it. The result has one backedge per arm.
//!
//! This is what LLVM does to `b1_mispredict`, established by DISASSEMBLING both
//! compilers' output rather than by reading either one's intent: LLVM's `main`
//! has TWO backward branches, to two DIFFERENT targets (0x20880 and 0x20894, in
//! loop copies of 86 and 89 bytes); trust-cg's has ONE (0x2095b, a 149-byte
//! loop). Two backedges to two targets is the signature of a duplicated latch.
//!
//! # Provenance of every rule below
//!
//! Read out of LLVM 22.1.2 (`cmake/Modules/LLVMVersion.cmake:4-11`, commit
//! `ceb94fe99cbc7db4bbe617b53fd04a61acbd4467`) at
//! `$HOME/trust/src/llvm-project`, and written up with citations in
//! `reports/perf/2026-09-30-llvm-latch-duplication/`. The transform there is
//! MachineBlockPlacement's *integrated* tail duplication, not the standalone
//! `TailDuplication` pass — confirmed by pass attribution, not inference: on a
//! synthetic xorshift loop the duplicated latch instruction appears twice by
//! default, twice with `-disable-tail-duplicate`, twice with
//! `-disable-early-taildup`, and ONCE with `-tail-dup-placement=false`.
//!
//! ⚑ What LLVM's model does NOT contain: any notion of branch-prediction
//! accuracy. Greps for mispredict / predictor / branch history across
//! `MachineBlockPlacement.cpp` and `TailDuplicator.cpp` find only two
//! incidental comments. LLVM's entire model is taken-branch/fall-through
//! counting plus a 2% icache penalty, and its `MisfetchCost`/`JumpInstCost`
//! are used only in `rotateLoopWithProfile`, which needs profile data. So this
//! pass is NOT justified here by a prediction-accuracy argument; it reproduces
//! a fall-through-motivated transform whose effect on this corpus is a
//! measurement, and it stays DEFAULT OFF until that measurement exists.
//!
//! # Why the shape is structurally what LLVM targets
//!
//! `hasBetterLayoutPredecessor` (`MachineBlockPlacement.cpp:1636`) refuses the
//! latch as a plain fall-through candidate when
//! `freq(armB->latch) * HotProb >= freq(armA->latch) * (1 - HotProb)`, with
//! `HotProb = StaticLikelyProb = 80/100` in the absence of a profile
//! (`:1445-1447`). For a 50/50 data-dependent branch that is `0.4 >= 0.1` —
//! ALWAYS true — so the latch is pushed into `DupCandidates` (`:1711-1712`).
//! Duplication is the intended answer for exactly this CFG.
//!
//! # Correctness
//!
//! The transform is a pure CFG rewrite that MOVES no instruction and CHANGES
//! no operand. Cloning block `T` into predecessor `P` is sound because:
//!
//! * `P`'s only successor is `T` and `P` ends in an unconditional branch to it
//!   (gate [P1]/[P2]). So every execution that reaches the end of `P` executed
//!   `T` next, and after the rewrite it executes a verbatim copy of `T`
//!   instead. Requiring BOTH conditions is load-bearing rather than belt-and-
//!   braces: LLVM's own transform does `removeSuccessor(succ_begin())` and then
//!   asserts `succ_empty()` (`TailDuplicator.cpp:933-935`), so a predecessor
//!   with two successors would have the WRONG edge dropped and a branch
//!   silently retargeted.
//! * The clone is byte-for-byte the original — same opcodes, same operands,
//!   same flags — so it computes the same values from the same registers. This
//!   IR is non-SSA at this stage, so a vreg defined in `T` becoming defined in
//!   two blocks is the representation's normal state, not a violation: before
//!   the rewrite that def was already reached along both arms.
//! * `P` inherits `T`'s successor LIST, and the cloned terminators carry `T`'s
//!   own `Block` operands, so the branch-operand/successor agreement that
//!   `validate_x86_function_layout` enforces is preserved by construction. No
//!   terminator has to be re-derived and no condition reversed — unlike LLVM,
//!   which must call `updateTerminator` because its layout implies the
//!   fall-through edge, whereas this IR names both edges explicitly.
//! * Duplication keeps the block order and creates no blocks. A remaining
//!   unconditional predecessor can absorb the original latch; the splice then
//!   removes that latch from both `blocks` and `block_order`. Its predecessor
//!   must contain no earlier terminator that could still target the latch.
//!
//! # The splice is NOT optional (corrected 2026-09-30)
//!
//! An earlier version KEPT the original `T` when it dropped to a single
//! predecessor, reasoning that it "costs one block of code" and lets branch
//! resolution elide the redundant jump. Measured, that version made
//! `b1_mispredict` 3% SLOWER, and the conclusion drawn was that the transform
//! does not suit this target.
//!
//! That conclusion was wrong, and the reasoning was the mistake: LLVM performs
//! this transform and LLVM is faster, so a slower result is evidence about the
//! IMPLEMENTATION, not about the transform. LLVM does NOT keep `T` —
//! `TailDuplicator.cpp:955` splices it into its remaining predecessor and
//! deletes it, guarded by `!TailBB->hasAddressTaken()`. Keeping it leaves an
//! extra block and an extra taken branch on a path LLVM does not have, which is
//! precisely the fall-through the transform exists to create. The instruction
//! budget of 4 is calibrated against the SPLICED result.
//!
//! A second difference remains and is NOT yet addressed: LLVM duplicates from
//! INSIDE `MachineBlockPlacement`, so the block chain is rebuilt and blocks
//! re-merged afterwards. This pass runs after layout is fixed, so it pays for
//! the duplication without the layout re-optimisation that follows it there.
//!
//! # What is deliberately NOT ported
//!
//! * The profile-driven paths. `isProfitableToTailDup` is reachable from
//!   exactly ONE site (`MachineBlockPlacement.cpp:1747-1748`); the path this
//!   shape takes (`:1939-1941`) sets the duplication flag with NO profitability
//!   call at all, so legality plus size IS the gate with no PGO.
//! * The trellis escape hatch (`:1233-1268`) that lets a non-duplicable
//!   predecessor be skipped without disqualifying the others, and the
//!   `Succ->succ_empty()` early return (`:1287-1288`). Both make LLVM LESS
//!   restrictive; omitting them is conservative.
//! * `MaxDuplicateCount = max(K, 10)` for computed-goto terminators
//!   (`TailDuplicator.cpp:618-619`). No such terminator reaches this pass.
//!
//! # MEASURED VERDICT: correct, and a 3% LOSS on the program it was built for
//!
//! At LLVM's budget of 4 this pass declines every loop in the `beat-llvm` corpus
//! (18 of 18 binaries byte-identical), because `b1_mispredict`'s latch is NINE
//! instructions post-RA — so LLVM would decline it too. Raising the budget via
//! `x86-latch-dup-max-insts` makes it fire on b1 and nothing else, and it then
//! reproduces LLVM's signature exactly: two backedges where this backend had
//! one, with `main` shrinking from 130 instructions to 100.
//!
//! b1 nonetheless goes **1.0943 -> 1.1267 vs LLVM -O3 (3.0% SLOWER)** against a
//! 0.0005 byte-identical-copy floor, identically at budgets 9, 12 and 16.
//!
//! So b1's gap is NOT this transform. The two-backedge layout is reproducible,
//! cheaper in instructions, and slower — the eighth item on that program to be
//! priced at zero or worse. LLVM's constant of 4 was not conservatism: it
//! declines this block and is right to. DEFAULT OFF, kept because it is a
//! correct gated implementation that will fire under LLVM's own policy if a
//! genuinely small diamond latch ever appears.
//! `reports/perf/2026-09-30-llvm-latch-duplication/`.

use std::collections::{BTreeMap, BTreeSet};

use trust_cg_ir::x86_64_ops::X86Opcode;
use trust_cg_lower::instructions::Block;
use trust_cg_lower::{X86ISelFunction, X86ISelOperand};

/// Non-PHI non-meta instruction budget for the cloned block.
///
/// LLVM's value for x86-64 through MachineBlockPlacement is **4** at `-O3` and
/// 2 below it: `TailDupPlacementAggressiveThreshold`
/// (`MachineBlockPlacement.cpp:178-183`) selected by
/// `TargetInstrInfo::getTailDuplicateSize` (`TargetInstrInfo.h:2344-2345`). The
/// inequality is `InstrCount > MaxDuplicateCount -> refuse`
/// (`TailDuplicator.cpp:661-667`), terminators INCLUDED. A threshold sweep
/// against the in-tree `llc` put the boundary exactly here: a 3-instruction
/// latch duplicates at `-tail-dup-placement-threshold=3` and above, not at 1
/// or 2.
///
/// `b1_mispredict`'s latch is `lea 0x1(%rdi),%rax ; mov %rax,%rdi ;
/// cmp $K,%rax ; jb` — four instructions, exactly at the limit.
const LATCH_DUP_MAX_INSTS: usize = 4;

static LATCH_DUP_MAX: std::sync::OnceLock<usize> = std::sync::OnceLock::new();

/// Override the instruction budget from a TRACKED compiler option
/// (`-Ztrust-ir-cg-args=x86-latch-dup-max-insts=<n>`). DEFAULT
/// [`LATCH_DUP_MAX_INSTS`] = 4, which is LLVM's own value at its own position.
///
/// ⚑ Why this is a knob rather than a tuned constant. Ported faithfully, the
/// budget of 4 DECLINES `b1_mispredict`: its latch is 9 instructions post-RA
/// (excluding the fall-through `Jmp`), so LLVM would not duplicate it either.
/// Raising the budget past LLVM's is therefore not a port, it is a new policy,
/// and it needs its own measurement rather than a borrowed justification. The
/// knob exists so that measurement is possible without pretending the number
/// came from LLVM.
pub fn set_x86_latch_dup_max_insts(n: usize) -> bool {
    match LATCH_DUP_MAX.set(n) {
        Ok(()) => true,
        Err(requested) => LATCH_DUP_MAX.get() == Some(&requested),
    }
}

fn latch_dup_max_insts() -> usize {
    LATCH_DUP_MAX.get().copied().unwrap_or(LATCH_DUP_MAX_INSTS)
}

static LATCH_DUP: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
static LATCH_DUP_TRACE: std::sync::OnceLock<bool> = std::sync::OnceLock::new();

/// Install this pass from a TRACKED compiler option, once
/// (`-Ztrust-ir-cg-args=x86-latch-dup`). DEFAULT OFF.
///
/// Opt-in on purpose: it is a new CFG transform whose value on this corpus is
/// not yet measured, and an env-only channel would be unreachable through the
/// real driver, which refuses every `TCG_*` variable before the backend loads.
pub fn set_x86_latch_dup_enabled(enabled: bool) -> bool {
    match LATCH_DUP.set(enabled) {
        Ok(()) => true,
        Err(requested) => LATCH_DUP.get() == Some(&requested),
    }
}

fn latch_dup_enabled() -> bool {
    LATCH_DUP.get().copied().unwrap_or(false) || crate::tcg_env_flag("TCG_X86_LATCH_DUP")
}

/// Install the decline trace (`-Ztrust-ir-cg-args=trace-x86-latch-dup`).
pub fn set_x86_latch_dup_trace_enabled(enabled: bool) -> bool {
    match LATCH_DUP_TRACE.set(enabled) {
        Ok(()) => true,
        Err(requested) => LATCH_DUP_TRACE.get() == Some(&requested),
    }
}

fn trace_enabled() -> bool {
    LATCH_DUP_TRACE.get().copied().unwrap_or(false)
        || crate::tcg_env_flag("TCG_X86_LATCH_DUP_TRACE")
}

/// True when `op` is a block terminator in this IR.
fn is_terminator(op: X86Opcode) -> bool {
    matches!(op, X86Opcode::Jmp | X86Opcode::Jcc | X86Opcode::Ret)
}

/// The instruction budget, counted the way LLVM counts it AT ITS OWN POSITION.
///
/// Two adjustments, and both are required for the borrowed constant to mean
/// anything:
///
/// 1. **Position.** LLVM's 4 counts POST-RA machine instructions
///    (`MachineBlockPlacement.cpp:3610` sets `PreRegAlloc = false`). Counting
///    pre-RA against the same number is meaningless: b1's latch holds 16
///    instructions before register allocation and 4 after, so the pre-RA form
///    was declined by a budget that describes the post-RA form. This pass
///    therefore runs from the post-RA region.
/// 2. **The implicit fall-through.** LLVM's count includes ONE terminator for a
///    conditional block whose other edge falls through. This IR names BOTH edges
///    (`Jcc` + `Jmp`), so the identical block counts one higher. A trailing `Jmp`
///    to the block's LAYOUT SUCCESSOR is exactly the edge LLVM leaves implicit,
///    so it is excluded here — and only in that case, because a `Jmp` anywhere
///    else is a real instruction LLVM would also have counted.
fn countable_insts(func: &X86ISelFunction, block: Block, layout_successor: Option<Block>) -> usize {
    let Some(b) = func.blocks.get(&block) else {
        return 0;
    };
    let n = b.insts.len();
    let trailing_fallthrough_jmp = matches!(b.insts.last(), Some(last)
        if last.opcode == X86Opcode::Jmp
            && matches!(last.operands.first(), Some(X86ISelOperand::Block(t))
                if Some(*t) == layout_successor));
    n - usize::from(trailing_fallthrough_jmp)
}

/// Predecessor map over the LAID-OUT blocks only. A block absent from
/// `block_order` is an unreachable construction shell (see
/// `validate_x86_function_layout`'s doc) and must not contribute an edge.
fn predecessors(func: &X86ISelFunction) -> BTreeMap<Block, BTreeSet<Block>> {
    let laid_out: BTreeSet<Block> = func.block_order.iter().copied().collect();
    let mut preds: BTreeMap<Block, BTreeSet<Block>> = BTreeMap::new();
    for &b in &func.block_order {
        let Some(block) = func.blocks.get(&b) else {
            continue;
        };
        for &s in &block.successors {
            if laid_out.contains(&s) {
                preds.entry(s).or_default().insert(b);
            }
        }
    }
    preds
}

/// Is `p` a clonable diamond arm for tail `t`?
///
/// [P1] exactly one successor, and it is `t`; [P2] the terminator is a single
/// unconditional `Jmp` naming `t`. LLVM requires both
/// (`TailDuplicator.cpp:826-847`: `succ_size() > 1 -> refuse`, then
/// `analyzeBranch` must succeed with an EMPTY condition list).
fn is_clonable_arm(func: &X86ISelFunction, p: Block, t: Block) -> bool {
    let Some(pb) = func.blocks.get(&p) else {
        return false;
    };
    if pb.successors.len() != 1 || pb.successors[0] != t {
        return false;
    }
    let Some(last) = pb.insts.last() else {
        return false;
    };
    if last.opcode != X86Opcode::Jmp || last.proof_origin.is_some() {
        return false;
    }
    if !matches!(last.operands.first(), Some(X86ISelOperand::Block(b)) if *b == t) {
        return false;
    }
    // No earlier terminator may bypass the appended copy or keep targeting the
    // original latch after a splice deletes it. A same-target Jcc/Jmp pair can
    // legitimately have only one entry in the CFG successor set.
    !pb.insts[..pb.insts.len() - 1]
        .iter()
        .any(|i| is_terminator(i.opcode))
}

/// Reasons a candidate tail is declined, for the trace.
fn tail_decline_reason(
    func: &X86ISelFunction,
    t: Block,
    layout_index: &BTreeMap<Block, usize>,
) -> Option<String> {
    let block = func.blocks.get(&t)?;
    if block.successors.len() < 2 {
        return Some(format!("succ_size={} < 2", block.successors.len()));
    }
    if block.successors.contains(&t) {
        return Some("tail is its own successor (single-block loop)".to_string());
    }
    let ti = *layout_index.get(&t)?;
    if !block
        .successors
        .iter()
        .any(|s| layout_index.get(s).is_some_and(|&si| si < ti))
    {
        return Some("not a backedge target (no successor earlier in layout)".to_string());
    }
    let layout_successor = func.block_order.get(ti + 1).copied();
    let budget = latch_dup_max_insts();
    let n = countable_insts(func, t, layout_successor);
    if n > budget {
        return Some(format!(
            "instruction count {n} (excluding a fall-through Jmp) > budget {budget}"
        ));
    }
    if let Some(bad) = block.insts.iter().find(|i| {
        i.proof_origin.is_some()
            || matches!(i.opcode, X86Opcode::Call | X86Opcode::CallR)
            || i.flags != i.opcode.default_flags()
    }) {
        return Some(format!(
            "tail contains a non-duplicable instruction ({:?}: proof_origin={} flags_nondefault={})",
            bad.opcode,
            bad.proof_origin.is_some(),
            bad.flags != bad.opcode.default_flags()
        ));
    }
    None
}

/// Clone small loop latches into their non-layout diamond arms. Returns true if
/// the function changed.
pub fn run_on_function(func: &mut X86ISelFunction) -> bool {
    if !latch_dup_enabled() {
        return false;
    }
    run_scoped(func, trace_enabled())
}

/// [`run_on_function`] with the gate already decided, so the tests drive the
/// transform without touching process-global `OnceLock` state (which a single
/// test binary can only set once).
fn run_scoped(func: &mut X86ISelFunction, trace: bool) -> bool {
    let layout_index: BTreeMap<Block, usize> = func
        .block_order
        .iter()
        .enumerate()
        .map(|(i, &b)| (b, i))
        .collect();
    let preds = predecessors(func);
    if trace {
        // The CFG as this pass SEES it. Without this, a decline histogram cannot
        // distinguish "the shape is absent" from "the shape is here and a gate is
        // wrong" — and the pass's position in the schedule decides which.
        eprintln!(
            "x86-latch-dup[{}]: CFG at this pass position ({} laid-out blocks):",
            func.name,
            func.block_order.len()
        );
        for &b in &func.block_order {
            let Some(bl) = func.blocks.get(&b) else {
                continue;
            };
            let term: Vec<X86Opcode> = bl
                .insts
                .iter()
                .filter(|i| is_terminator(i.opcode))
                .map(|i| i.opcode)
                .collect();
            eprintln!(
                "    {b:?} insts={} succs={:?} preds={:?} terms={:?}",
                bl.insts.len(),
                bl.successors,
                preds.get(&b).map(|p| p.iter().copied().collect::<Vec<_>>()),
                term
            );
        }
    }

    // Decide everything against the ENTERING shape, then apply. A candidate's
    // gates mention its predecessors' terminators, and cloning rewrites those,
    // so interleaving decisions with edits would let one rewrite invalidate
    // another's preconditions.
    let mut plans: Vec<(Block, Vec<Block>)> = Vec::new();
    for &t in &func.block_order {
        if let Some(reason) = tail_decline_reason(func, t, &layout_index) {
            if trace {
                eprintln!("x86-latch-dup[{}]: {t:?} declined — {reason}", func.name);
            }
            continue;
        }
        let Some(tpreds) = preds.get(&t) else {
            continue;
        };
        if tpreds.len() < 2 {
            if trace {
                eprintln!(
                    "x86-latch-dup[{}]: {t:?} declined — only {} predecessor(s)",
                    func.name,
                    tpreds.len()
                );
            }
            continue;
        }
        // The layout predecessor keeps falling into `t`, exactly as LLVM leaves
        // one arm doing. It is the block physically before `t`, when that block
        // is in fact a predecessor.
        let ti = layout_index[&t];
        let layout_pred = ti
            .checked_sub(1)
            .and_then(|i| func.block_order.get(i).copied())
            .filter(|p| tpreds.contains(p));

        let dup: Vec<Block> = tpreds
            .iter()
            .copied()
            .filter(|&p| Some(p) != layout_pred)
            .collect();
        // [C2] All-or-nothing over the predecessors we would clone into. LLVM's
        // `Duplicate` flag has a trellis escape this deliberately omits.
        if dup.is_empty() || !dup.iter().all(|&p| is_clonable_arm(func, p, t)) {
            if trace {
                let bad: Vec<Block> = dup
                    .iter()
                    .copied()
                    .filter(|&p| !is_clonable_arm(func, p, t))
                    .collect();
                eprintln!(
                    "x86-latch-dup[{}]: {t:?} declined — {} of {} candidate arm(s) are not \
                     single-successor unconditional-Jmp predecessors: {bad:?}",
                    func.name,
                    bad.len(),
                    dup.len()
                );
            }
            continue;
        }
        // [C3] The no-profile benefit model, verbatim: `NumDup + 1 <=
        // succ_size(T)` (`MachineBlockPlacement.cpp:1291,1311`). For a two-arm
        // diamond latch this is 2 <= 2, exactly at the boundary, and it is what
        // stops the transform firing on a 3- or 4-way join.
        let succs = func.blocks[&t].successors.len();
        if dup.len() + 1 > succs {
            if trace {
                eprintln!(
                    "x86-latch-dup[{}]: {t:?} declined — dup {} + 1 > succ_size {succs} \
                     (the no-profile benefit rule)",
                    func.name,
                    dup.len()
                );
            }
            continue;
        }
        plans.push((t, dup));
    }

    if plans.is_empty() {
        return false;
    }
    for (t, arms) in plans {
        let tail = func.blocks[&t].clone();
        for p in &arms {
            let pb = func
                .blocks
                .get_mut(p)
                .expect("arm existed at decision time");
            pb.insts.pop(); // the unconditional `Jmp t`, proven present by [P2]
            pb.insts.extend(tail.insts.iter().cloned());
            pb.successors = tail.successors.clone();
            if trace {
                eprintln!(
                    "x86-latch-dup[{}]: cloned {t:?} ({} insts) into {p:?}",
                    func.name,
                    tail.insts.len()
                );
            }
        }

        // SPLICE, as LLVM does (`TailDuplicator.cpp:955`). `T` now has at most
        // one predecessor left; if that predecessor falls into it with an
        // unconditional branch, fold `T` into it and delete `T`. Without this
        // the arms each carry a copy AND the original survives, so the remaining
        // arm still pays a taken branch into a block LLVM has already removed.
        let remaining: Vec<Block> = predecessors(func)
            .get(&t)
            .map(|ps| ps.iter().copied().collect())
            .unwrap_or_default();
        if remaining.len() == 1 && !arms.contains(&remaining[0]) {
            let l = remaining[0];
            // The last predecessor needs the same complete terminator proof
            // as a duplicated arm. A same-target `Jcc t; Jmp t` has one CFG
            // successor, but popping only its final jump and deleting `t` would
            // leave the conditional branch naming a deleted block.
            let splice = is_clonable_arm(func, l, t);
            if splice {
                let lb = func.blocks.get_mut(&l).expect("checked just above");
                lb.insts.pop(); // its `Jmp t`
                lb.insts.extend(tail.insts.iter().cloned());
                lb.successors = tail.successors.clone();
                func.blocks.remove(&t);
                func.block_order.retain(|b| *b != t);
                if trace {
                    eprintln!(
                        "x86-latch-dup[{}]: spliced {t:?} into its last predecessor \
                         {l:?} and deleted it",
                        func.name
                    );
                }
            } else if trace {
                eprintln!(
                    "x86-latch-dup[{}]: {t:?} kept — {l:?} does not fall into it \
                     unconditionally",
                    func.name
                );
            }
        }
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_cg_ir::x86_64_ops::X86CondCode;
    use trust_cg_lower::X86ISelInst;
    use trust_cg_lower::function::Signature;

    const ENTRY: Block = Block(0);
    const HEADER: Block = Block(1);
    const ARM_A: Block = Block(2);
    const ARM_B: Block = Block(3);
    const LATCH: Block = Block(4);
    const EXIT: Block = Block(5);

    fn vreg(id: u32) -> X86ISelOperand {
        X86ISelOperand::VReg(trust_cg_ir::regs::VReg {
            id,
            class: trust_cg_ir::regs::RegClass::Gpr64,
        })
    }
    fn inst(op: X86Opcode, operands: Vec<X86ISelOperand>) -> X86ISelInst {
        X86ISelInst::new(op, operands)
    }
    fn jmp(to: Block) -> X86ISelInst {
        inst(X86Opcode::Jmp, vec![X86ISelOperand::Block(to)])
    }
    fn jcc(to: Block) -> X86ISelInst {
        inst(
            X86Opcode::Jcc,
            vec![
                X86ISelOperand::CondCode(X86CondCode::B),
                X86ISelOperand::Block(to),
            ],
        )
    }

    /// The canonical shape: a two-arm in-loop diamond whose arms join at a
    /// four-instruction latch. `block_order` is insertion order, so `ARM_B` is
    /// the latch's layout predecessor and `ARM_A` is the arm to clone into.
    fn build(latch_extra: usize) -> X86ISelFunction {
        let sig = Signature {
            params: vec![],
            returns: vec![],
        };
        let mut func = X86ISelFunction::new("latchdup_test".to_string(), sig);
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
            h.insts.push(inst(
                X86Opcode::CmpRI,
                vec![vreg(1), X86ISelOperand::Imm(1)],
            ));
            h.insts.push(jcc(ARM_A));
            h.insts.push(jmp(ARM_B));
            h.successors = vec![ARM_A, ARM_B];
        }
        for (arm, v) in [(ARM_A, 10u32), (ARM_B, 11u32)] {
            let a = func.blocks.get_mut(&arm).unwrap();
            a.insts.push(inst(
                X86Opcode::MovRI,
                vec![vreg(v), X86ISelOperand::Imm(7)],
            ));
            a.insts.push(jmp(LATCH));
            a.successors = vec![LATCH];
        }
        {
            let l = func.blocks.get_mut(&LATCH).unwrap();
            l.insts.push(inst(
                X86Opcode::AddRI,
                vec![vreg(1), vreg(1), X86ISelOperand::Imm(1)],
            ));
            for i in 0..latch_extra {
                l.insts.push(inst(
                    X86Opcode::MovRI,
                    vec![vreg(90 + i as u32), X86ISelOperand::Imm(0)],
                ));
            }
            l.insts.push(inst(
                X86Opcode::CmpRI,
                vec![vreg(1), X86ISelOperand::Imm(100)],
            ));
            l.insts.push(jcc(HEADER));
            l.insts.push(jmp(EXIT));
            l.successors = vec![HEADER, EXIT];
        }
        {
            let x = func.blocks.get_mut(&EXIT).unwrap();
            x.insts.push(inst(X86Opcode::Ret, vec![]));
        }
        func
    }

    #[test]
    fn duplicates_the_latch_into_the_non_layout_arm() {
        let mut func = build(0);
        assert_eq!(func.blocks[&LATCH].insts.len(), 4, "latch is at the budget");
        assert!(
            run_scoped(&mut func, false),
            "the canonical shape must fire"
        );

        // ARM_A got a verbatim copy and now carries the latch's edges.
        let arm_a = &func.blocks[&ARM_A];
        assert_eq!(arm_a.successors, vec![HEADER, EXIT]);
        assert_eq!(
            arm_a.insts.iter().map(|i| i.opcode).collect::<Vec<_>>(),
            vec![
                X86Opcode::MovRI,
                X86Opcode::AddRI,
                X86Opcode::CmpRI,
                X86Opcode::Jcc,
                X86Opcode::Jmp
            ],
            "the arm's own body, then a verbatim clone of the latch"
        );
        // ARM_B was the latch's last remaining predecessor, so the latch is
        // SPLICED into it and deleted — which is what LLVM does
        // (`TailDuplicator.cpp:955`). Keeping the latch instead left an extra
        // block and an extra taken branch on a path LLVM does not have, and
        // measured 3% SLOWER on b1_mispredict.
        assert_eq!(
            func.blocks[&ARM_B].successors,
            vec![HEADER, EXIT],
            "the layout predecessor absorbed the latch"
        );
        assert!(
            !func.blocks.contains_key(&LATCH),
            "the latch is deleted after the splice"
        );
        assert!(
            !func.block_order.contains(&LATCH),
            "and removed from the layout"
        );
        // EXACTLY one BACKEDGE per arm and no shared latch — LLVM's signature.
        // A backedge is an edge to the header from a block LATER in layout; the
        // entry block's forward edge to the header is not one, which is why this
        // filters on layout position rather than merely on the successor list.
        let hpos = func
            .block_order
            .iter()
            .position(|b| *b == HEADER)
            .expect("header is laid out");
        let backedges = func
            .block_order
            .iter()
            .enumerate()
            .filter(|(i, b)| *i > hpos && func.blocks[b].successors.contains(&HEADER))
            .count();
        assert_eq!(backedges, 2, "one backedge per arm, none shared");
    }

    #[test]
    fn declines_a_latch_over_the_instruction_budget() {
        // SIX instructions, of which five count: the trailing `Jmp EXIT` is the
        // fall-through edge LLVM leaves implicit and this IR materializes, so it
        // is excluded. Five counted is one past LLVM's -O3
        // `TailDupPlacementAggressiveThreshold`.
        let mut func = build(2);
        assert_eq!(func.blocks[&LATCH].insts.len(), 6);
        assert_eq!(
            countable_insts(&func, LATCH, Some(EXIT)),
            5,
            "the fall-through Jmp must not be counted"
        );
        assert!(!run_scoped(&mut func, false));
        assert_eq!(func.blocks[&ARM_A].successors, vec![LATCH]);
    }

    /// The fall-through exclusion is the adjustment that makes LLVM's borrowed
    /// constant mean the same thing here, so it is pinned in both directions.
    /// A five-instruction latch whose last `Jmp` names the LAYOUT SUCCESSOR
    /// counts four and fires; the identical latch whose `Jmp` names any other
    /// block counts five and declines.
    #[test]
    fn excludes_only_a_fall_through_jmp_from_the_budget() {
        let mut func = build(1);
        assert_eq!(func.blocks[&LATCH].insts.len(), 5);
        assert_eq!(countable_insts(&func, LATCH, Some(EXIT)), 4);
        assert!(
            run_scoped(&mut func, false),
            "five instructions ending in a fall-through Jmp is four by LLVM's count"
        );

        // Same block, but its trailing Jmp is NOT the fall-through edge.
        let mut other = build(1);
        {
            let l = other.blocks.get_mut(&LATCH).unwrap();
            let n = l.insts.len();
            l.insts[n - 1] = jmp(HEADER);
            l.insts[n - 2] = jcc(EXIT);
            l.successors = vec![EXIT, HEADER];
        }
        assert_eq!(countable_insts(&other, LATCH, Some(EXIT)), 5);
        assert!(
            !run_scoped(&mut other, false),
            "a Jmp that is not the fall-through edge is a real instruction"
        );
    }

    #[test]
    fn declines_an_arm_with_two_successors() {
        // THE load-bearing gate. LLVM drops `succ_begin()` and asserts
        // `succ_empty()`, so an arm with two successors would have the wrong
        // edge removed and a branch silently retargeted.
        let mut func = build(0);
        {
            let a = func.blocks.get_mut(&ARM_A).unwrap();
            a.insts.pop();
            a.insts.push(jcc(LATCH));
            a.insts.push(jmp(EXIT));
            a.successors = vec![LATCH, EXIT];
        }
        assert!(!run_scoped(&mut func, false));
        assert_eq!(func.blocks[&ARM_A].successors, vec![LATCH, EXIT]);
    }

    #[test]
    fn declines_a_three_way_join() {
        // `dup + 1 <= succ_size` is LLVM's entire no-profile benefit rule: with
        // three arms and two successors it is 3 > 2, so the transform refuses
        // rather than tripling the latch.
        let mut func = build(0);
        let arm_c = Block(6);
        func.ensure_block(arm_c);
        {
            let c = func.blocks.get_mut(&arm_c).unwrap();
            c.insts.push(inst(
                X86Opcode::MovRI,
                vec![vreg(12), X86ISelOperand::Imm(7)],
            ));
            c.insts.push(jmp(LATCH));
            c.successors = vec![LATCH];
        }
        {
            let h = func.blocks.get_mut(&HEADER).unwrap();
            h.successors = vec![ARM_A, ARM_B, arm_c];
        }
        assert!(!run_scoped(&mut func, false));
        assert_eq!(func.blocks[&ARM_A].successors, vec![LATCH]);
    }

    #[test]
    fn retains_a_latch_with_a_same_target_conditional_last_predecessor() {
        let mut func = build(0);
        let last = func.blocks.get_mut(&ARM_B).unwrap();
        last.insts.insert(last.insts.len() - 1, jcc(LATCH));
        // Both branch outcomes reach the latch, so the CFG successor set is
        // still [LATCH]. The conditional must keep its actual target alive.
        assert_eq!(last.successors, vec![LATCH]);
        let predecessor_before = format!("{last:?}");
        let tail_before = format!("{:?}", func.blocks[&LATCH]);
        let order_before = func.block_order.clone();

        assert!(
            run_scoped(&mut func, false),
            "the other arm still duplicates"
        );
        assert_eq!(func.blocks[&ARM_A].successors, vec![HEADER, EXIT]);
        assert!(
            func.blocks.contains_key(&LATCH),
            "the conditional's target stays alive"
        );
        assert_eq!(format!("{:?}", func.blocks[&ARM_B]), predecessor_before);
        assert_eq!(format!("{:?}", func.blocks[&LATCH]), tail_before);
        assert_eq!(
            func.block_order, order_before,
            "declined splice preserves layout"
        );
        for block in func.blocks.values() {
            for inst in &block.insts {
                for operand in &inst.operands {
                    if let X86ISelOperand::Block(target) = operand {
                        assert!(
                            func.blocks.contains_key(target),
                            "no dangling branch target"
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn declines_a_tail_that_is_not_a_backedge_target() {
        // A plain diamond join with no backedge is not a latch. This gate is
        // stricter than LLVM (which would consider any join) and keeps the pass
        // aimed at the measured shape.
        let mut func = build(0);
        {
            let l = func.blocks.get_mut(&LATCH).unwrap();
            l.insts.pop();
            l.insts.pop();
            l.insts.push(jcc(EXIT));
            l.insts.push(jmp(Block(6)));
            l.successors = vec![EXIT, Block(6)];
        }
        func.ensure_block(Block(6));
        assert!(!run_scoped(&mut func, false));
        assert_eq!(func.blocks[&ARM_A].successors, vec![LATCH]);
    }

    #[test]
    fn declines_a_tail_carrying_a_proof_obligation() {
        let mut func = build(0);
        {
            let l = func.blocks.get_mut(&LATCH).unwrap();
            l.insts[0].proof_origin = Some(trust_cg_lower::x86_64_isel::X86ProofOrigin::AtomicLoad);
        }
        assert!(!run_scoped(&mut func, false));
        assert_eq!(func.blocks[&ARM_A].successors, vec![LATCH]);
    }

    #[test]
    fn is_off_by_default() {
        let mut func = build(0);
        // `run_on_function` consults the tracked gate; no knob was installed.
        assert!(!run_on_function(&mut func));
        assert_eq!(func.blocks[&ARM_A].successors, vec![LATCH]);
    }
}
