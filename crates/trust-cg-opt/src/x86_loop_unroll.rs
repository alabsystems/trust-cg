// trust-cg-opt - x86-64 Full Loop Unrolling (X9 slice 1)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Full unrolling of small constant-trip-count loops for x86-64 ISel-output
//! functions — the first x86 scalar unroller (X9 slice 1).
//!
//! # Why (the b05 re-diagnosis)
//!
//! LLVM's 9× lead on the matmul benchmark is NOT vectorization and NOT
//! primarily register allocation: LLVM fully unrolls the trip-24 inner
//! product loop into straight-line code (~3 insts per original iteration)
//! and lets scalar promotion/GVN clean up, while the bridge pays ~30 insts
//! per iteration (loop control + re-computed addressing + bounds checks +
//! spill reloads). Full unrolling plus the EXISTING downstream cleanups
//! (const-fold, copy-prop, CSE, peephole, BCE, DCE — and at O3, the next
//! fixpoint iteration's LICM) recovers the same shape. See
//! `docs/x86-full-unroll-design-2026-07-19.md`.
//!
//! # Recognized shape (everything else is refused, fail-closed)
//!
//! The x86 frontend's TOP-TESTED counted loop, before `X86LoopRotate` runs.
//! The body is a single-entry single-exit straight-line CHAIN of blocks
//! (the importer splits at MIR statement/assert boundaries):
//!
//! ```text
//! preheader:  ... ; MovRI iv, #init ; ... ; Jmp header
//! header:     <pure register-only compare chain> ;
//!             Jcc cc, T ; Jmp F                    ({T,F} = {c1, exit})
//! c1:         <straight-line body> ; [Jmp c2 | fallthrough]
//! ...
//! cm (latch): <straight-line body> ; ... iv := iv + step ... ; Jmp header
//! ```
//!
//! The header compare chain is either the Setcc-materialized idiom
//! (`Cmp** iv,bound ; Setcc cc_set, b ; [Movzx/MovRR/AndRI#1]* ;
//! CmpRI b,#0 | TestRR b,b | TestRI b,#1 | AndRI b,#1 ; Jcc NE/E`) or the
//! direct form (`Cmp** iv,bound ; Jcc cc`). The bound is a literal
//! immediate (`CmpRI`/`CmpRI8`) or a vreg whose UNIQUE whole-function def
//! is `MovRI #c` outside the loop in a block dominating the header
//! (LICM-hoisted constant bounds). Init and step must be constant; the
//! trip count is obtained by DIRECT SIMULATION of the compare at the
//! compare width with wraparound — no closed form, no off-by-one class.
//!
//! # Transform and soundness argument
//!
//! The chain c1..cm is CONCATENATED (dropping the inter-chain `Jmp`s —
//! a no-op on single-pred/single-succ straight-line edges) into one
//! iteration step, replicated verbatim (NO renaming) `trip` times into c1;
//! c1 then jumps to the exit, the header's compare chain is deleted (header
//! falls through to c1), and the emptied c2..cm are deleted.
//!
//! Soundness rests on the importer's SSA-destructed merge-vreg discipline:
//! the chain is a SELF-CONTAINED iteration step — every loop-carried value
//! is re-established within it (in-place tied updates or explicit edge
//! copies), so replaying it verbatim N times executes exactly the N rolled
//! iterations on identical register/memory state. The checks below close
//! every channel through which deleting the header test or concatenating
//! iterations could be observable:
//!
//! * **Header purity + containment.** Every removed header instruction is
//!   pure, register-only (VReg/Imm/CondCode operands only), non-call,
//!   non-branch, NON-SIDE-EFFECTING and NON-PSEUDO (a hoisted
//!   `TrapBoundsCheckExact` is `MemoryEffect::Pure` but is a GUARD — it
//!   must never ride out with the chain), and none of its defs is
//!   referenced ANYWHERE outside the header.
//! * **Flag hygiene.** In the rolled loop, iteration i+1's body executes
//!   after the header chain rewrote RFLAGS; post-unroll it executes after
//!   iteration i's body tail. Therefore every body flag-READER must be
//!   preceded by a body flag-WRITER (each iteration re-establishes the
//!   flags it consumes), and the EXIT block must not read flags before
//!   writing them (it previously observed the header chain's flags).
//! * **Trip exactness.** The simulated trip count executes the compare
//!   semantics (signed/unsigned, at compare width, with wraparound) that
//!   the deleted `Jcc` would have; `trip >= 1` is required so the body
//!   executes at least once on every path, exactly as the rolled loop
//!   (a zero-trip loop is refused, never restructured).
//! * **IV definite value.** `iv`'s defs are exactly: one `MovRI #init` IN
//!   THE PREHEADER BLOCK (so EVERY loop entry re-establishes `init` —
//!   a def merely dominating the header would not survive re-entry from
//!   an enclosing loop) plus chain-internal defs whose NET transfer is
//!   proven `iv := iv + step` by a conservative affine walk (any
//!   unmodeled def refuses). This licenses the const-fold SEED below.
//! * **Bound definite value.** A `CmpRR` bound vreg must have exactly ONE
//!   def in the whole function — `MovRI #c` outside the loop, dominating
//!   the header — so it holds `c` at every compare.
//! * **EH.** Functions carrying any exception-handling structure are
//!   skipped outright (block deletion must not orphan EH block refs).
//!
//! After replication the pass inserts a clone of the preheader's
//! `MovRI iv, #init` at the top of the merged block. This is semantically
//! a no-op (iv provably holds `init` on entry — single entry, straight
//! from the preheader through the emptied header) and it seeds the
//! per-block `x86_const_fold` tracker so the entire unrolled chain — IV
//! updates, index arithmetic, addressing — collapses to constants
//! downstream (the chain-MERGE is what makes the whole unrolled body one
//! block, i.e. one const-fold scope).
//!
//! Bounds checks in the body are `TrapBoundsCheckExact` carrier pseudos at
//! this stage (expanded later in the codegen pipeline); they clone verbatim
//! with unchanged operand fingerprints, so `guard_obligations` bindings
//! keep working. The regalloc validator and TV-5 gate the final stream, as
//! with every pass.
//!
//! # Gating
//!
//! Slice 1 is OPT-IN: the pass is only registered when `TCG_X86_UNROLL=1`
//! (see `x86_64/pipeline.rs`). `TCG_X86_UNROLL_TRACE=1` prints, per
//! candidate loop, the applied trip/body size or the refusal reason plus
//! a structural dump of the loop.

use std::collections::{HashMap, HashSet};

use trust_cg_ir::regs::RegClass;
use trust_cg_ir::{VReg, X86CondCode, X86Opcode};
use trust_cg_lower::instructions::Block;
use trust_cg_lower::{X86ISelFunction, X86ISelInst, X86ISelOperand};

use crate::effects::{
    MemoryEffect, x86_defines_all_cc_flags, x86_inst_effect, x86_produces_value, x86_reads_flags,
    x86_writes_flags,
};
use crate::mach_view::{CfgAnalysis, GenericLoop};
use crate::x86_pass_manager::X86MachinePass;

/// Maximum constant trip count eligible for full unrolling (covers the
/// b05-class N=24 inner loops and b12's trip-8 bit loop).
const MAX_TRIP: u64 = 24;

/// Maximum body-chain blocks (header excluded).
const MAX_CHAIN_BLOCKS: usize = 8;

/// Maximum concatenated body instructions (terminators excluded).
const MAX_BODY_INSTS: usize = 40;

/// Maximum instructions ADDED by one unroll: `(trip - 1) * body_len`.
const MAX_CLONED_INSTS: usize = 920;

/// Maximum instructions ADDED across all unrolls in one function (bounds
/// compile-time growth of the downstream passes and the proof pipeline).
const MAX_FUNC_CLONED_INSTS: usize = 2000;

/// Full loop unrolling for x86-64 ISel-output machine functions.
pub struct X86LoopUnroll;

impl X86LoopUnroll {
    /// Run the unroller directly on an ISel function.
    pub fn run_on_function(&mut self, func: &mut X86ISelFunction) -> bool {
        run_impl(func)
    }
}

impl X86MachinePass for X86LoopUnroll {
    fn name(&self) -> &str {
        "x86-loop-unroll"
    }

    fn run(&mut self, func: &mut X86ISelFunction) -> bool {
        run_impl(func)
    }
}

fn trace_enabled() -> bool {
    std::env::var_os("TCG_X86_UNROLL_TRACE").is_some()
}

macro_rules! utrace {
    ($($arg:tt)*) => {
        if trace_enabled() {
            eprintln!("[x86-unroll] {}", format!($($arg)*));
        }
    };
}

fn run_impl(func: &mut X86ISelFunction) -> bool {
    if !func.eh_info.is_empty() {
        utrace!("skip fn {}: carries EH structure", func.name);
        return false;
    }
    let mut changed = false;
    let mut budget = MAX_FUNC_CLONED_INSTS;
    // Re-analyze after every applied unroll: the transform rewrites edges
    // and deletes merged blocks, so cached CFG facts for the remaining
    // candidates could be stale. An applied unroll removes its back edge,
    // so each loop is applied at most once and the iteration terminates.
    loop {
        let cfg = CfgAnalysis::compute(func);
        let mut applied = false;
        for lp in innermost_loops(&cfg.loops) {
            match analyze_counted_loop(func, &cfg, lp) {
                Ok(plan) => {
                    let added = (plan.trip as usize - 1) * plan.body.len();
                    if added > budget {
                        utrace!(
                            "refuse header={:?}: function clone budget exhausted ({} > {})",
                            lp.header,
                            added,
                            budget
                        );
                        continue;
                    }
                    utrace!(
                        "APPLY header={:?} chain={:?} exit={:?} trip={} body={} (+{} insts)",
                        plan.header,
                        plan.chain,
                        plan.exit,
                        plan.trip,
                        plan.body.len(),
                        added
                    );
                    apply_unroll(func, &plan);
                    budget -= added;
                    changed = true;
                    applied = true;
                    break;
                }
                Err(reason) => {
                    utrace!("refuse header={:?}: {}", lp.header, reason);
                    dump_loop(func, lp);
                }
            }
        }
        if !applied {
            break;
        }
    }
    changed
}

/// Trace helper: one line per loop-body block (+ preheader) with opcodes
/// and successors, so a refused shape is fully diagnosable from the log.
fn dump_loop(func: &X86ISelFunction, lp: &GenericLoop<Block>) {
    if !trace_enabled() {
        return;
    }
    let mut blocks: Vec<Block> = lp.body.iter().copied().collect();
    blocks.sort_by_key(|b| b.0);
    if let Some(ph) = lp.preheader {
        blocks.insert(0, ph);
    }
    for b in blocks {
        if let Some(blk) = func.blocks.get(&b) {
            let tag = if Some(b) == lp.preheader {
                "pre "
            } else if b == lp.header {
                "hdr "
            } else {
                "    "
            };
            if Some(b) == lp.preheader || b == lp.header {
                // Full operand detail where recognition happens.
                eprintln!("[x86-unroll]   {}{:?} -> {:?}", tag, b, blk.successors);
                for i in &blk.insts {
                    eprintln!("[x86-unroll]     {:?} {:?}", i.opcode, i.operands);
                }
            } else {
                let ops: Vec<String> = blk
                    .insts
                    .iter()
                    .map(|i| format!("{:?}", i.opcode))
                    .collect();
                eprintln!(
                    "[x86-unroll]   {}{:?} [{}] -> {:?}",
                    tag,
                    b,
                    ops.join(","),
                    blk.successors
                );
            }
        }
    }
}

/// Innermost loops: no OTHER loop's body is strictly contained in this one's.
fn innermost_loops(loops: &[GenericLoop<Block>]) -> impl Iterator<Item = &GenericLoop<Block>> {
    loops.iter().filter(move |lp| {
        !loops.iter().any(|other| {
            other.header != lp.header
                && other.body.len() < lp.body.len()
                && other.body.is_subset(&lp.body)
        })
    })
}

/// A fully-analyzed unrollable loop.
struct UnrollPlan {
    header: Block,
    /// Body chain c1..cm in control-flow order; c1 receives the merged
    /// unrolled body, c2..cm are deleted.
    chain: Vec<Block>,
    exit: Block,
    trip: u64,
    /// Concatenated iteration step (inter-chain terminators dropped).
    body: Vec<X86ISelInst>,
    /// Semantic no-op `MovRI` seeds prepended to the merged block: the IV's
    /// proven init plus every body-read vreg that provably holds a
    /// loop-invariant constant (LICM-hoisted strides/steps/bounds). They
    /// make those constants visible to the per-block `x86_const_fold`
    /// tracker so the whole unrolled body collapses downstream.
    seeds: Vec<X86ISelInst>,
}

// ---------------------------------------------------------------------------
// Recognition (every deviation refuses with a trace reason)
// ---------------------------------------------------------------------------

fn analyze_counted_loop(
    func: &X86ISelFunction,
    cfg: &CfgAnalysis<Block>,
    lp: &GenericLoop<Block>,
) -> Result<UnrollPlan, &'static str> {
    // ---- CFG shape: header + straight-line chain ----
    if lp.latches.len() != 1 {
        return Err("multi-latch loop");
    }
    let header = lp.header;
    let latch = lp.latches[0];
    if header == latch {
        return Err("single-block self-loop");
    }
    let preheader = lp.preheader.ok_or("no unique preheader")?;

    let hsuccs = &block(func, header)?.successors;
    if hsuccs.len() != 2 {
        return Err("header successor count != 2");
    }
    let in_loop: Vec<Block> = hsuccs
        .iter()
        .copied()
        .filter(|s| lp.body.contains(s))
        .collect();
    if in_loop.len() != 1 {
        return Err("header in-loop successor count != 1");
    }
    let chain_head = in_loop[0];
    if chain_head == header {
        return Err("header self-edge");
    }
    let exit = *hsuccs
        .iter()
        .find(|&&s| s != chain_head)
        .ok_or("no exit successor")?;
    if lp.body.contains(&exit) || exit == header {
        return Err("exit inside loop");
    }
    let empty: Vec<Block> = Vec::new();
    let hpreds = cfg.preds.get(&header).unwrap_or(&empty);
    if hpreds.len() != 2 || !hpreds.contains(&preheader) || !hpreds.contains(&latch) {
        return Err("header preds are not {preheader, latch}");
    }

    // Walk the chain c1..cm (cm == latch): every block single-pred,
    // single-succ, ending back at the header only from the latch.
    let mut chain: Vec<Block> = Vec::new();
    let mut cur = chain_head;
    loop {
        if chain.len() >= MAX_CHAIN_BLOCKS {
            return Err("body chain over block cap");
        }
        if !lp.body.contains(&cur) || cur == header {
            return Err("chain escapes the loop body");
        }
        if chain.contains(&cur) {
            return Err("chain revisits a block");
        }
        let cpreds = cfg.preds.get(&cur).unwrap_or(&empty);
        let expected_pred = if chain.is_empty() {
            header
        } else {
            *chain.last().unwrap()
        };
        if cpreds.as_slice() != [expected_pred] {
            return Err("chain block has extra predecessors");
        }
        chain.push(cur);
        let csuccs = &block(func, cur)?.successors;
        if cur == latch {
            if csuccs.as_slice() != [header] {
                return Err("latch does not branch only to header");
            }
            break;
        }
        if csuccs.len() != 1 {
            return Err("chain block has multiple successors");
        }
        cur = csuccs[0];
        if cur == header {
            return Err("back edge from non-latch chain block");
        }
    }
    // The loop body must be EXACTLY {header} ∪ chain.
    if lp.body.len() != chain.len() + 1 {
        return Err("loop body has blocks outside the chain");
    }

    // ---- Header: pure register-only compute + `Jcc cc,T ; Jmp F` ----
    let hinsts = &block(func, header)?.insts;
    let n = hinsts.len();
    if n < 3 {
        return Err("header too short for a compare chain");
    }
    let jcc = &hinsts[n - 2];
    let jmp = &hinsts[n - 1];
    if jcc.opcode != X86Opcode::Jcc || jmp.opcode != X86Opcode::Jmp {
        return Err("header does not end Jcc;Jmp");
    }
    let (jcc_cc, t_target) = match jcc.operands.as_slice() {
        [X86ISelOperand::CondCode(cc), X86ISelOperand::Block(t)] => (*cc, *t),
        _ => return Err("malformed Jcc operands"),
    };
    let f_target = match jmp.operands.as_slice() {
        [X86ISelOperand::Block(f)] => *f,
        _ => return Err("malformed Jmp operands"),
    };
    {
        let mut tf = [t_target, f_target];
        tf.sort_by_key(|b| b.0);
        let mut ce = [chain_head, exit];
        ce.sort_by_key(|b| b.0);
        if tf != ce {
            return Err("Jcc/Jmp targets are not {chain, exit}");
        }
    }

    let chain_insts = &hinsts[..n - 2];
    for inst in chain_insts {
        if inst.flags.is_branch() || inst.flags.is_terminator() || inst.flags.is_call() {
            return Err("branch/call inside header chain");
        }
        // Trap carriers (TrapBoundsCheckExact & co.) are MemoryEffect::Pure
        // with their guard semantics carried in IS_PSEUDO|HAS_SIDE_EFFECTS —
        // the purity check below does NOT catch them, and deleting one with
        // the chain would delete a guard. Refuse every pseudo outright. The
        // compare family also carries HAS_SIDE_EFFECTS (its flag write IS
        // its effect) but is non-trapping and delete-safe under the flag
        // checks below, so it alone is exempted; anything else that is
        // side-effecting (Div/Mul preg groups, Adc/Sbb, ...) refuses.
        if inst.flags.is_pseudo() {
            return Err("pseudo instruction in header chain");
        }
        if has_hidden_defs(inst.opcode) {
            return Err("hidden-def instruction in header chain");
        }
        let benign_compare = matches!(
            inst.opcode,
            X86Opcode::CmpRR
                | X86Opcode::CmpRI
                | X86Opcode::CmpRI8
                | X86Opcode::TestRR
                | X86Opcode::TestRI
        );
        if inst.flags.has_side_effects() && !benign_compare {
            return Err("side-effecting instruction in header chain");
        }
        if !inst.call_arg_regs.is_empty() {
            return Err("call-arg carrier inside header chain");
        }
        if x86_inst_effect(inst) != MemoryEffect::Pure {
            return Err("non-pure header instruction");
        }
        for op in &inst.operands {
            match op {
                X86ISelOperand::VReg(_) | X86ISelOperand::Imm(_) | X86ISelOperand::CondCode(_) => {}
                _ => return Err("non-register operand in header chain"),
            }
        }
    }
    // Flag hygiene inside the header: a reader must follow a header writer.
    check_local_flag_pairing(chain_insts)
        .map_err(|_| "header flag-reader before header flag-writer")?;

    // Header defs must be invisible outside the header.
    let header_defs: HashSet<VReg> = chain_insts.iter().filter_map(def_vreg).collect();
    if !header_defs.is_empty() {
        for (&b, blk) in &func.blocks {
            if b == header {
                continue;
            }
            for inst in &blk.insts {
                if inst_mentions_any(inst, &header_defs) {
                    return Err("header def escapes the header");
                }
            }
        }
    }

    // ---- Concatenate the chain into the iteration body ----
    let body = concat_chain_body(func, header, &chain)?;
    if body.len() > MAX_BODY_INSTS {
        return Err("body over size cap");
    }
    for inst in &body {
        if inst.flags.is_branch() || inst.flags.is_terminator() || inst.flags.is_call() {
            return Err("branch/terminator/call in body");
        }
        if !inst.call_arg_regs.is_empty() {
            return Err("call-arg carrier in body");
        }
        if has_hidden_defs(inst.opcode) {
            return Err("hidden-def instruction in body");
        }
        for op in &inst.operands {
            if operand_refuses_in_body(op) {
                return Err("PReg/Block/jump-table operand in body");
            }
        }
    }
    // Flag hygiene across the whole iteration step (clone-boundary safety).
    check_local_flag_pairing(&body).map_err(|_| "body flag-reader before body flag-writer")?;

    // ---- Exit block must not observe the deleted chain's flags ----
    check_exit_flag_safety(func, exit)?;

    // ---- Decode the compare chain to (iv, bound, taken-direction) ----
    let chain_set: HashSet<Block> = lp.body.iter().copied().collect();
    let decoded = decode_header_condition(func, cfg, &chain_set, header, chain_insts, jcc_cc)?;

    let iv = decoded.iv;
    let width = match iv.class {
        RegClass::Gpr32 => 32u32,
        RegClass::Gpr64 => 64u32,
        _ => return Err("IV is not a GPR"),
    };

    // The header must not redefine the IV: the compare must read the
    // loop-carried value as it entered the header. (Header-local COPIES of
    // the IV were already resolved away by the reaching-def walk in the
    // decoder; any surviving header def of `iv` itself refuses.)
    if chain_insts.iter().any(|i| def_vreg(i) == Some(iv)) {
        return Err("IV defined in header chain");
    }

    // ---- IV init: the LAST def of `iv` in the preheader must establish a
    // constant — `MovRI #c` or a copy of a proven invariant constant.
    // Being IN the preheader is load-bearing: every loop (re-)entry
    // re-executes it, so `iv == init` holds at the header regardless of
    // any OTHER defs of this vreg id elsewhere in the function (isel
    // reuses ids; far defs are killed by this one on every entry). ----
    let mut preheader_init: Option<i64> = None;
    for inst in &block(func, preheader)?.insts {
        // A hidden second def (Xchg-class) could write `iv` invisibly to
        // the operand-0 def model this scan rests on.
        if has_hidden_defs(inst.opcode) {
            return Err("hidden-def instruction in preheader");
        }
        if def_vreg(inst) != Some(iv) {
            continue;
        }
        // Forward scan: the LAST def wins (earlier ones are dead by here).
        preheader_init =
            if let (X86Opcode::MovRI, [X86ISelOperand::VReg(_), X86ISelOperand::Imm(init)]) =
                (inst.opcode, inst.operands.as_slice())
            {
                Some(*init)
            } else if let Some((_, s)) = exact_copy(inst) {
                Some(
                    resolve_invariant_const(func, cfg, &chain_set, header, s)
                        .ok_or("preheader IV copy source is not an invariant constant")?,
                )
            } else {
                return Err("preheader IV def is neither MovRI nor const copy");
            };
    }
    let init = preheader_init.ok_or("no IV init in preheader")?;
    let step = chain_iv_step(func, cfg, &chain_set, header, &body, iv)
        .ok_or("chain IV transfer is not iv += const")?;
    if step == 0 {
        return Err("zero IV step");
    }

    // ---- Profitability gate (suite-measured 2026-07-19, RE-CONFIRMED
    // 2026-07-21): unrolling pays only when the downstream collapse fires —
    // an IV-derived bounds-check index (guard elimination) or IV-derived
    // addressing (const-fold into immediates). A body whose work is
    // data-dependent ALU (crc32's b12 bit loop) gains only the loop control
    // and LOSES. Directly re-measured under the current default pass set
    // (cold-trap, X10 SIB, all flips on): forcing the b12 bit-loop to unroll
    // 8x grew it 117->204 insts and REGRESSED runtime (0.10->0.11s) — the
    // loop-invariant constants (poly/step) are re-materialized per unrolled
    // copy and partly spilled, outweighing the loop-control savings. The gate
    // stays; b12's real cost is regalloc rematerialization of spilled
    // constants, not the rolled loop control.
    if !body_has_foldable_iv_consumer(&body, iv) {
        return Err("no IV-derived guard/address consumer (unprofitable)");
    }

    // ---- Trip count by direct simulation at compare width ----
    let mask: u64 = if width == 64 {
        u64::MAX
    } else {
        (1u64 << width) - 1
    };
    let mut k = (init as u64) & mask;
    let mut trip: u64 = 0;
    loop {
        let cond_true = eval_cc(decoded.rel_cc, k, (decoded.bound as u64) & mask, width)
            .ok_or("unsupported condition code")?;
        let taken = if decoded.taken_when_cond_true {
            cond_true
        } else {
            !cond_true
        };
        let goes_to = if taken { t_target } else { f_target };
        if goes_to == exit {
            break;
        }
        trip += 1;
        if trip > MAX_TRIP {
            return Err("trip count over cap (or non-terminating shape)");
        }
        k = k.wrapping_add(step as u64) & mask;
    }
    if trip == 0 {
        return Err("zero-trip loop");
    }
    if (trip as usize - 1) * body.len() > MAX_CLONED_INSTS {
        return Err("clone volume over cap");
    }

    // Synthesized rather than cloned: the preheader init may be a copy of a
    // constant vreg, but the PROVEN fact is simply `iv == init` at body
    // entry, which `MovRI iv, #init` states directly.
    let mut seeds = vec![X86ISelInst::new(
        X86Opcode::MovRI,
        vec![X86ISelOperand::VReg(iv), X86ISelOperand::Imm(init)],
    )];
    let mut seeded: HashSet<VReg> = HashSet::new();
    seeded.insert(iv);
    // Seed every body-read vreg that provably holds an invariant constant.
    // Re-stating a proven-constant vreg's value is a no-op for every reader
    // anywhere (it is the vreg's unique-def value), so this cannot change
    // semantics; it only informs the block-local const tracker.
    'outer: for inst in &body {
        let mut reads: Vec<VReg> = Vec::new();
        collect_read_vregs(inst, &mut reads);
        for v in reads {
            if seeds.len() > 16 {
                break 'outer;
            }
            if !seeded.insert(v) {
                continue;
            }
            if let Some(c) = resolve_invariant_const(func, cfg, &chain_set, header, v) {
                seeds.push(X86ISelInst::new(
                    X86Opcode::MovRI,
                    vec![X86ISelOperand::VReg(v), X86ISelOperand::Imm(c)],
                ));
            }
        }
    }
    Ok(UnrollPlan {
        header,
        chain,
        exit,
        trip,
        body,
        seeds,
    })
}

/// Collect every vreg `inst` reads (all operand positions except a pure
/// operand-0 def; tied ops read operand 0 too, but over-collecting a def is
/// harmless here — it only ADDS seed candidates that then fail the
/// invariant-const proof).
fn collect_read_vregs(inst: &X86ISelInst, out: &mut Vec<VReg>) {
    fn walk(op: &X86ISelOperand, out: &mut Vec<VReg>) {
        match op {
            X86ISelOperand::VReg(v) => out.push(*v),
            X86ISelOperand::MemAddr { base, .. } => walk(base, out),
            X86ISelOperand::SibMemAddr { base, index, .. } => {
                walk(base, out);
                walk(index, out);
            }
            _ => {}
        }
    }
    for op in &inst.operands {
        walk(op, out);
    }
}

/// Concatenate the chain blocks' instructions in control-flow order,
/// dropping ONLY each block's trailing `Jmp` to the next block (or to the
/// header, for the latch). A chain block may also simply fall through
/// (no terminator); any other branch anywhere refuses.
fn concat_chain_body(
    func: &X86ISelFunction,
    header: Block,
    chain: &[Block],
) -> Result<Vec<X86ISelInst>, &'static str> {
    let mut body: Vec<X86ISelInst> = Vec::new();
    for (i, &b) in chain.iter().enumerate() {
        let insts = &block(func, b)?.insts;
        let expected_next = if i + 1 < chain.len() {
            chain[i + 1]
        } else {
            header
        };
        let mut take = insts.len();
        if let Some(last) = insts.last() {
            if last.opcode == X86Opcode::Jmp {
                if last.operands.as_slice() != [X86ISelOperand::Block(expected_next)] {
                    return Err("chain terminator jumps to unexpected block");
                }
                take -= 1;
            } else if last.flags.is_branch() || last.flags.is_terminator() {
                return Err("chain block ends in a non-Jmp terminator");
            }
            // else: fallthrough — successors[] already validated the edge.
        }
        body.extend(insts[..take].iter().cloned());
    }
    Ok(body)
}

fn block(func: &X86ISelFunction, b: Block) -> Result<&trust_cg_lower::X86ISelBlock, &'static str> {
    func.blocks.get(&b).ok_or("missing block")
}

/// The single vreg an instruction defines (operand 0 when the opcode
/// produces a value), mirroring x86_dce's model.
fn def_vreg(inst: &X86ISelInst) -> Option<VReg> {
    if !x86_produces_value(inst.opcode) {
        return None;
    }
    match inst.operands.first() {
        Some(X86ISelOperand::VReg(v)) => Some(*v),
        _ => None,
    }
}

/// Opcodes whose SECOND def (operand 1, or implicit) is invisible to the
/// operand-0 def model above. Every def/init/affine argument in this pass
/// rests on `def_vreg`, so these must refuse wherever they could hide a
/// write (adversarial-review finding, 2026-07-19).
fn has_hidden_defs(op: X86Opcode) -> bool {
    matches!(
        op,
        X86Opcode::Xchg | X86Opcode::Cmpxchg | X86Opcode::Cmpxchg8 | X86Opcode::Cmpxchg16
    )
}

/// The exact value-preserving register copy, under the same opcode/class
/// discipline as x86_const_fold's `copy_opcode_class`: `MovRR` copies a
/// Gpr64 pair, `MovRR32` a Gpr32 pair. Any other opcode/class combination
/// is NOT an exact copy (a 32-bit write zero-extends its 64-bit carrier).
fn exact_copy(inst: &X86ISelInst) -> Option<(VReg, VReg)> {
    let want = match inst.opcode {
        X86Opcode::MovRR => RegClass::Gpr64,
        X86Opcode::MovRR32 => RegClass::Gpr32,
        _ => return None,
    };
    match inst.operands.as_slice() {
        [X86ISelOperand::VReg(d), X86ISelOperand::VReg(s)]
            if d.class == want && s.class == want =>
        {
            Some((*d, *s))
        }
        _ => None,
    }
}

/// Does `inst` mention any of `vregs` in ANY operand position (recursing
/// into memory operands)? Used for the fail-closed escape checks.
fn inst_mentions_any(inst: &X86ISelInst, vregs: &HashSet<VReg>) -> bool {
    fn operand_mentions(op: &X86ISelOperand, vregs: &HashSet<VReg>) -> bool {
        match op {
            X86ISelOperand::VReg(v) => vregs.contains(v),
            X86ISelOperand::MemAddr { base, .. } => operand_mentions(base, vregs),
            X86ISelOperand::SibMemAddr { base, index, .. } => {
                operand_mentions(base, vregs) || operand_mentions(index, vregs)
            }
            _ => false,
        }
    }
    inst.operands.iter().any(|op| operand_mentions(op, vregs))
}

/// Operands that make a body instruction non-replicable.
fn operand_refuses_in_body(op: &X86ISelOperand) -> bool {
    match op {
        X86ISelOperand::PReg(_) | X86ISelOperand::Block(_) | X86ISelOperand::JumpTableIndex(_) => {
            true
        }
        X86ISelOperand::MemAddr { base, .. } => operand_refuses_in_body(base),
        X86ISelOperand::SibMemAddr { base, index, .. } => {
            operand_refuses_in_body(base) || operand_refuses_in_body(index)
        }
        _ => false,
    }
}

/// Every flag-reader in `insts` must be preceded (in `insts`) by an
/// instruction that DEFINES every condition flag — i.e. the sequence
/// re-establishes all flags it consumes. A may-write partial flag writer
/// (`Inc`/`Dec` preserve CF, `BtRI` writes only CF, shifts write nothing
/// at count 0) is NOT a barrier: a reader behind one would still observe
/// the deleted header chain's flags across the clone boundary
/// (adversarial-review finding, 2026-07-19). Trap-carrier pseudos are
/// deliberately NOT barriers either: they fully define flags when later
/// EXPANDED (their expansion begins with CMP), but a proof-gated pass may
/// instead DELETE them — transparency is the only classification sound in
/// both worlds.
fn check_local_flag_pairing(insts: &[X86ISelInst]) -> Result<(), ()> {
    let mut writer_seen = false;
    for inst in insts {
        if x86_reads_flags(inst.opcode) && !writer_seen {
            return Err(());
        }
        if x86_defines_all_cc_flags(inst.opcode) {
            writer_seen = true;
        }
    }
    Ok(())
}

/// The exit block previously observed the header chain's RFLAGS; after the
/// unroll it observes the last body instruction's instead. Safe only if
/// every path from the exit provably writes flags before any read (or
/// returns — flags die at `Ret`). Flag-neutral single-successor forwarding
/// blocks are flowed through, bounded and fail-closed.
fn check_exit_flag_safety(func: &X86ISelFunction, exit: Block) -> Result<(), &'static str> {
    let mut visited: HashSet<Block> = HashSet::new();
    let mut worklist: Vec<Block> = vec![exit];
    while let Some(b) = worklist.pop() {
        if !visited.insert(b) {
            continue;
        }
        if visited.len() > 8 {
            return Err("exit flag-safety walk over block cap");
        }
        let insts = &block(func, b)?.insts;
        let mut settled = false;
        for inst in insts {
            if x86_reads_flags(inst.opcode) {
                return Err("exit path reads flags before writing them");
            }
            // Settling requires a MUST-define-all-flags writer: a partial
            // writer (Inc/Dec/BtRI/shift) passes stale flag bits through.
            if x86_defines_all_cc_flags(inst.opcode) {
                settled = true;
                break;
            }
        }
        if settled {
            continue;
        }
        match insts.last() {
            // Flags die at Ret and at a trap dead-end alike.
            Some(last) if last.opcode == X86Opcode::Ret || last.opcode == X86Opcode::Ud2 => {
                continue;
            }
            _ => {
                // Flag-neutral block: flags flow to every successor. A
                // conditional terminator is a flag READER (caught above),
                // so any remaining multi-successor shape is indirect
                // control flow — refuse.
                let succs = &block(func, b)?.successors;
                if succs.is_empty() {
                    return Err("exit path ends without Ret or flag write");
                }
                if succs.len() != 1 {
                    return Err("exit path forks without writing flags");
                }
                worklist.push(succs[0]);
            }
        }
    }
    Ok(())
}

/// Resolve `v`, read at chain position `upto`, through NEAREST-reaching-def
/// same-class `MovRR` copies within the header chain, yielding the value's
/// live-in source vreg. Pure local reaching-def reasoning on straight-line
/// code — no whole-function uniqueness needed (isel reuses vreg ids, so
/// global uniqueness is the wrong question). Stops (returning the current
/// vreg) at a non-copy local def — downstream checks then refuse it.
fn resolve_local_copies(chain: &[X86ISelInst], upto: usize, v: VReg) -> VReg {
    let mut cur = v;
    let mut limit = upto;
    'walk: for _ in 0..4 {
        for i in (0..limit).rev() {
            if def_vreg(&chain[i]) != Some(cur) {
                continue;
            }
            if let Some((_, s)) = exact_copy(&chain[i]) {
                cur = s;
                limit = i;
                continue 'walk;
            }
            return cur; // nearest local def is not a transparent copy
        }
        return cur; // no local def: live-in to the header
    }
    cur
}

/// If `v` resolves — through unique-def same-class copies, every hop
/// defined OUTSIDE the loop in a block dominating the header — to a unique
/// `MovRI #c`, return `c`. The uniqueness + dominance of every hop makes
/// the value `c` at every point the loop can observe it.
fn resolve_invariant_const(
    func: &X86ISelFunction,
    cfg: &CfgAnalysis<Block>,
    loop_body: &HashSet<Block>,
    header: Block,
    v: VReg,
) -> Option<i64> {
    let mut cur = v;
    for _ in 0..8 {
        let mut only_def: Option<(Block, &X86ISelInst)> = None;
        for (&b, blk) in &func.blocks {
            for inst in &blk.insts {
                if def_vreg(inst) == Some(cur) {
                    if only_def.is_some() {
                        return None; // multi-def
                    }
                    only_def = Some((b, inst));
                }
            }
        }
        let (def_block, inst) = only_def?;
        if loop_body.contains(&def_block) || !cfg.dominates(def_block, header) {
            return None;
        }
        if let (X86Opcode::MovRI, [X86ISelOperand::VReg(_), X86ISelOperand::Imm(c)]) =
            (inst.opcode, inst.operands.as_slice())
        {
            return Some(*c);
        }
        if let Some((_, s)) = exact_copy(inst) {
            cur = s;
            continue;
        }
        return None;
    }
    None
}

/// Decoded loop condition: `iv REL bound` drives the Jcc.
struct DecodedCond {
    iv: VReg,
    bound: i64,
    /// The cc under which `iv REL bound` is TRUE (CMP iv, bound order).
    rel_cc: X86CondCode,
    /// Whether `Jcc` takes its target when the relation is true.
    taken_when_cond_true: bool,
}

/// `a REL b` under `CMP a,b ; Jcc cc` — expressed as `b REL' a`.
fn swap_cc(cc: X86CondCode) -> X86CondCode {
    match cc {
        X86CondCode::B => X86CondCode::A,
        X86CondCode::A => X86CondCode::B,
        X86CondCode::AE => X86CondCode::BE,
        X86CondCode::BE => X86CondCode::AE,
        X86CondCode::L => X86CondCode::G,
        X86CondCode::G => X86CondCode::L,
        X86CondCode::GE => X86CondCode::LE,
        X86CondCode::LE => X86CondCode::GE,
        other => other, // E/NE symmetric; others rejected by eval_cc anyway
    }
}

/// Decode the header chain into `iv REL #bound` + branch polarity.
fn decode_header_condition(
    func: &X86ISelFunction,
    cfg: &CfgAnalysis<Block>,
    loop_body: &HashSet<Block>,
    header: Block,
    chain: &[X86ISelInst],
    jcc_cc: X86CondCode,
) -> Result<DecodedCond, &'static str> {
    // The flag-setter feeding the Jcc: the LAST flag-writer in the chain.
    let (s_idx, setter) = chain
        .iter()
        .enumerate()
        .rev()
        .find(|(_, i)| x86_writes_flags(i.opcode))
        .ok_or("no flag-setter before Jcc")?;

    // Boolean-test tails over a Setcc-materialized bool.
    let boolean_tail: Option<VReg> = match setter.opcode {
        X86Opcode::CmpRI | X86Opcode::CmpRI8 => match setter.operands.as_slice() {
            [X86ISelOperand::VReg(v), X86ISelOperand::Imm(0)] => Some(*v),
            _ => None,
        },
        X86Opcode::TestRR => match setter.operands.as_slice() {
            [X86ISelOperand::VReg(a), X86ISelOperand::VReg(b)] if a == b => Some(*a),
            _ => None,
        },
        X86Opcode::TestRI | X86Opcode::AndRI => match setter.operands.as_slice() {
            // Tied 2-operand and 3-operand forms both occur.
            [X86ISelOperand::VReg(v), X86ISelOperand::Imm(1)] => Some(*v),
            [
                X86ISelOperand::VReg(_),
                X86ISelOperand::VReg(s),
                X86ISelOperand::Imm(1),
            ] => Some(*s),
            _ => None,
        },
        _ => None,
    };
    if let Some(bool_vreg) = boolean_tail
        && let Some(setcc) = resolve_setcc_bool(chain, s_idx, bool_vreg)
    {
        let taken_when_cond_true = match jcc_cc {
            X86CondCode::NE => true,
            X86CondCode::E => false,
            _ => return Err("boolean-test Jcc is not NE/E"),
        };
        let (iv, bound, rel_cc) = decode_bound_compare(
            func,
            cfg,
            loop_body,
            header,
            chain,
            setcc.setcc_idx,
            setcc.cc,
        )?;
        return Ok(DecodedCond {
            iv,
            bound,
            rel_cc,
            taken_when_cond_true,
        });
    }
    // A `CmpRI v,#0` whose v is NOT a Setcc bool falls through to the
    // direct-compare interpretation below (`iv != 0`-style loops).

    // Direct compare feeding the Jcc.
    match setter.opcode {
        X86Opcode::CmpRI | X86Opcode::CmpRI8 => match setter.operands.as_slice() {
            [X86ISelOperand::VReg(v), X86ISelOperand::Imm(imm)] => Ok(DecodedCond {
                iv: resolve_local_copies(chain, s_idx, *v),
                bound: *imm,
                rel_cc: jcc_cc,
                taken_when_cond_true: true,
            }),
            _ => Err("compare with non-VReg/Imm operands"),
        },
        X86Opcode::CmpRR => {
            let (iv, bound, rel_cc) =
                decode_cmprr(func, cfg, loop_body, header, chain, s_idx, jcc_cc)?;
            Ok(DecodedCond {
                iv,
                bound,
                rel_cc,
                taken_when_cond_true: true,
            })
        }
        _ => Err("unrecognized flag-setter"),
    }
}

/// The compare feeding a Setcc: the nearest earlier flag-writer, either
/// `CmpRI/CmpRI8 iv,#bound` or `CmpRR` with a const-resolvable side.
/// Returns (iv, bound, cc-with-iv-first).
fn decode_bound_compare(
    func: &X86ISelFunction,
    cfg: &CfgAnalysis<Block>,
    loop_body: &HashSet<Block>,
    header: Block,
    chain: &[X86ISelInst],
    setcc_idx: usize,
    setcc_cc: X86CondCode,
) -> Result<(VReg, i64, X86CondCode), &'static str> {
    let (cmp_idx, cmp) = chain[..setcc_idx]
        .iter()
        .enumerate()
        .rev()
        .find(|(_, i)| x86_writes_flags(i.opcode))
        .ok_or("no compare feeds the Setcc")?;
    match cmp.opcode {
        X86Opcode::CmpRI | X86Opcode::CmpRI8 => match cmp.operands.as_slice() {
            [X86ISelOperand::VReg(iv), X86ISelOperand::Imm(bound)] => {
                Ok((resolve_local_copies(chain, cmp_idx, *iv), *bound, setcc_cc))
            }
            _ => Err("bound compare with non-VReg/Imm operands"),
        },
        X86Opcode::CmpRR => decode_cmprr(func, cfg, loop_body, header, chain, cmp_idx, setcc_cc),
        _ => Err("Setcc source compare is unrecognized"),
    }
}

/// `CmpRR a,b` at chain position `cmp_idx`, where — after resolving both
/// sides through local header copies — exactly one side resolves to a
/// loop-invariant constant. Returns (iv, bound, cc oriented iv-first).
fn decode_cmprr(
    func: &X86ISelFunction,
    cfg: &CfgAnalysis<Block>,
    loop_body: &HashSet<Block>,
    header: Block,
    chain: &[X86ISelInst],
    cmp_idx: usize,
    cc: X86CondCode,
) -> Result<(VReg, i64, X86CondCode), &'static str> {
    let cmp = &chain[cmp_idx];
    let (a, b) = match cmp.operands.as_slice() {
        [X86ISelOperand::VReg(a), X86ISelOperand::VReg(b)] => (*a, *b),
        _ => return Err("CmpRR with non-VReg operands"),
    };
    // The trip simulation runs at the IV's class width; a mixed-class
    // compare would encode at a width the simulation does not model.
    if a.class != b.class {
        return Err("CmpRR operand classes differ");
    }
    let a = resolve_local_copies(chain, cmp_idx, a);
    let b = resolve_local_copies(chain, cmp_idx, b);
    let ca = resolve_invariant_const(func, cfg, loop_body, header, a);
    let cb = resolve_invariant_const(func, cfg, loop_body, header, b);
    match (ca, cb) {
        (None, Some(bound)) => Ok((a, bound, cc)),
        (Some(bound), None) => Ok((b, bound, swap_cc(cc))),
        (Some(_), Some(_)) => Err("CmpRR with two constant sides"),
        (None, None) => Err("CmpRR bound is not a loop-invariant constant"),
    }
}

struct SetccBool {
    setcc_idx: usize,
    cc: X86CondCode,
}

/// If `v` (read at chain position `at`) is, through transparent single-def
/// copies WITHIN the chain, the product of a `Setcc`, return that Setcc.
/// Transparent: `MovRR`, `MovRR32`, `Movzx*`, `AndRI #1`.
fn resolve_setcc_bool(chain: &[X86ISelInst], at: usize, v: VReg) -> Option<SetccBool> {
    let mut cur = v;
    let mut limit = at;
    for _ in 0..chain.len().max(8) {
        let (idx, def) = chain[..limit]
            .iter()
            .enumerate()
            .rev()
            .find(|(_, i)| def_vreg(i) == Some(cur))?;
        match def.opcode {
            X86Opcode::Setcc => {
                if let [X86ISelOperand::VReg(_), X86ISelOperand::CondCode(cc)] =
                    def.operands.as_slice()
                {
                    return Some(SetccBool {
                        setcc_idx: idx,
                        cc: *cc,
                    });
                }
                return None;
            }
            X86Opcode::MovRR | X86Opcode::MovRR32 => {
                if let Some((_, s)) = exact_copy(def) {
                    cur = s;
                    limit = idx;
                    continue;
                }
                return None;
            }
            X86Opcode::Movzx | X86Opcode::MovzxW => {
                // Zero-extension preserves the 0/1 Setcc bool value.
                if let Some(X86ISelOperand::VReg(src)) = def.operands.get(1) {
                    cur = *src;
                    limit = idx;
                    continue;
                }
                return None;
            }
            X86Opcode::AndRI => {
                // `AndRI b, #1` boolean mask keeps the value (0/1 bools).
                // Tied 2-operand and 3-operand forms both occur.
                match def.operands.as_slice() {
                    [X86ISelOperand::VReg(_), X86ISelOperand::Imm(1)] => {
                        limit = idx;
                        continue;
                    }
                    [
                        X86ISelOperand::VReg(_),
                        X86ISelOperand::VReg(s),
                        X86ISelOperand::Imm(1),
                    ] => {
                        cur = *s;
                        limit = idx;
                        continue;
                    }
                    _ => return None,
                }
            }
            _ => return None,
        }
    }
    None
}

/// Profitability heuristic (NOT soundness-bearing): does the body consume
/// an IV-derived value through a guard index or a memory address? Those
/// are the consumers the post-unroll collapse (const-fold + guard-elim)
/// turns into immediates/deletions. Taint flows forward from the IV
/// through any value-producing instruction that reads a tainted vreg.
fn body_has_foldable_iv_consumer(body: &[X86ISelInst], iv: VReg) -> bool {
    let mut tainted: HashSet<VReg> = HashSet::new();
    tainted.insert(iv);
    fn operand_tainted(op: &X86ISelOperand, tainted: &HashSet<VReg>) -> bool {
        match op {
            X86ISelOperand::VReg(v) => tainted.contains(v),
            X86ISelOperand::MemAddr { base, .. } => operand_tainted(base, tainted),
            X86ISelOperand::SibMemAddr { base, index, .. } => {
                operand_tainted(base, tainted) || operand_tainted(index, tainted)
            }
            _ => false,
        }
    }
    for inst in body {
        // Consumers checked before this inst's own def updates the taint.
        if inst.opcode == X86Opcode::TrapBoundsCheckExact
            && let [_, X86ISelOperand::VReg(idx), _] = inst.operands.as_slice()
            && tainted.contains(idx)
        {
            return true;
        }
        for op in &inst.operands {
            match op {
                X86ISelOperand::MemAddr { .. } | X86ISelOperand::SibMemAddr { .. }
                    if operand_tainted(op, &tainted) =>
                {
                    return true;
                }
                _ => {}
            }
        }
        if let Some(d) = def_vreg(inst) {
            let reads_taint = inst.operands.iter().any(|op| operand_tainted(op, &tainted));
            if reads_taint {
                tainted.insert(d);
            } else {
                tainted.remove(&d);
            }
        }
    }
    false
}

/// Conservative affine walk over the iteration body: does executing it map
/// `iv := iv + <const>`? Tracks vregs whose value is `iv_entry + offset`;
/// any unmodeled def of a tracked vreg unmaps it; any unmodeled def of `iv`
/// itself fails. Steps come from `AddRI/SubRI #imm` (tied) or
/// `AddRR/SubRR d, s` where `s` is a proven loop-invariant constant vreg
/// (the LICM-hoisted `MovRI #1` idiom). Returns the net step for `iv`.
fn chain_iv_step(
    func: &X86ISelFunction,
    cfg: &CfgAnalysis<Block>,
    loop_body: &HashSet<Block>,
    header: Block,
    body: &[X86ISelInst],
    iv: VReg,
) -> Option<i64> {
    let mut offsets: HashMap<VReg, i64> = HashMap::new();
    offsets.insert(iv, 0);
    for inst in body {
        let def = def_vreg(inst);
        match inst.opcode {
            X86Opcode::MovRR | X86Opcode::MovRR32 => {
                if let Some((d, s)) = exact_copy(inst) {
                    match offsets.get(&s).copied() {
                        Some(off) => {
                            offsets.insert(d, off);
                        }
                        None => {
                            offsets.remove(&d);
                        }
                    }
                    continue;
                }
            }
            X86Opcode::Inc | X86Opcode::Dec => {
                // Tied single-operand `Inc/Dec d` (the peephole's AddRI#1
                // rewrite, seen at O3 fixpoint iteration 2+).
                if let (Some(d), [X86ISelOperand::VReg(_)]) = (def, inst.operands.as_slice())
                    && let Some(off) = offsets.get(&d).copied()
                {
                    let delta = if inst.opcode == X86Opcode::Inc { 1 } else { -1 };
                    offsets.insert(d, off.wrapping_add(delta));
                    continue;
                }
            }
            X86Opcode::AddRI | X86Opcode::SubRI => {
                let neg = inst.opcode == X86Opcode::SubRI;
                // Tied `Op d, #imm` and 3-operand `Op d, s, #imm` forms.
                let src_off = match inst.operands.as_slice() {
                    [X86ISelOperand::VReg(d), X86ISelOperand::Imm(imm)] => {
                        offsets.get(d).copied().map(|o| (o, *imm))
                    }
                    [
                        X86ISelOperand::VReg(_),
                        X86ISelOperand::VReg(s),
                        X86ISelOperand::Imm(imm),
                    ] => offsets.get(s).copied().map(|o| (o, *imm)),
                    _ => None,
                };
                if let (Some(d), Some((off, imm))) = (def, src_off) {
                    let next = if neg {
                        off.wrapping_sub(imm)
                    } else {
                        off.wrapping_add(imm)
                    };
                    offsets.insert(d, next);
                    continue;
                }
            }
            X86Opcode::AddRR | X86Opcode::SubRR => {
                let neg = inst.opcode == X86Opcode::SubRR;
                // Tied `Op d, s` and 3-operand `Op d, s1, s2` forms; one
                // side must be IV-derived, the other a proven invariant
                // constant (for SubRR only `tracked - const` is affine).
                let resolved: Option<(i64, i64)> = match inst.operands.as_slice() {
                    [X86ISelOperand::VReg(d), X86ISelOperand::VReg(s)] => {
                        match (
                            offsets.get(d).copied(),
                            resolve_invariant_const(func, cfg, loop_body, header, *s),
                        ) {
                            (Some(off), Some(c)) => Some((off, c)),
                            _ => None,
                        }
                    }
                    [
                        X86ISelOperand::VReg(_),
                        X86ISelOperand::VReg(s1),
                        X86ISelOperand::VReg(s2),
                    ] => {
                        match (
                            offsets.get(s1).copied(),
                            resolve_invariant_const(func, cfg, loop_body, header, *s2),
                        ) {
                            (Some(off), Some(c)) => Some((off, c)),
                            _ => {
                                if neg {
                                    None // const - tracked: not affine-preserving
                                } else {
                                    match (
                                        resolve_invariant_const(func, cfg, loop_body, header, *s1),
                                        offsets.get(s2).copied(),
                                    ) {
                                        (Some(c), Some(off)) => Some((off, c)),
                                        _ => None,
                                    }
                                }
                            }
                        }
                    }
                    _ => None,
                };
                if let (Some(d), Some((off, c))) = (def, resolved) {
                    let next = if neg {
                        off.wrapping_sub(c)
                    } else {
                        off.wrapping_add(c)
                    };
                    offsets.insert(d, next);
                    continue;
                }
            }
            _ => {}
        }
        // Unmodeled instruction: any def it makes leaves the tracked set.
        if let Some(d) = def {
            if d == iv {
                return None; // iv rewritten by something we cannot model
            }
            offsets.remove(&d);
        }
    }
    match offsets.get(&iv).copied() {
        Some(0) | None => None,
        Some(step) => Some(step),
    }
}

/// Evaluate `lhs cc rhs` with compare semantics (CMP lhs, rhs) at `width`.
fn eval_cc(cc: X86CondCode, lhs: u64, rhs: u64, width: u32) -> Option<bool> {
    let mask: u64 = if width == 64 {
        u64::MAX
    } else {
        (1u64 << width) - 1
    };
    let l = lhs & mask;
    let r = rhs & mask;
    let sign_extend = |v: u64| -> i64 {
        if width == 64 {
            v as i64
        } else {
            let shift = 64 - width;
            ((v << shift) as i64) >> shift
        }
    };
    let sl = sign_extend(l);
    let sr = sign_extend(r);
    Some(match cc {
        X86CondCode::E => l == r,
        X86CondCode::NE => l != r,
        X86CondCode::B => l < r,
        X86CondCode::AE => l >= r,
        X86CondCode::BE => l <= r,
        X86CondCode::A => l > r,
        X86CondCode::L => sl < sr,
        X86CondCode::GE => sl >= sr,
        X86CondCode::LE => sl <= sr,
        X86CondCode::G => sl > sr,
        _ => return None,
    })
}

// ---------------------------------------------------------------------------
// Transform
// ---------------------------------------------------------------------------

fn apply_unroll(func: &mut X86ISelFunction, plan: &UnrollPlan) {
    let c1 = plan.chain[0];

    // The merged-away chain blocks are NOT deleted: the x86 pipeline
    // requires contiguous block ids for regalloc replay (deleting one
    // fails the compile closed with [TCG-REGALLOC-063]). They become
    // empty pass-throughs threaded on the exit path — executed ONCE per
    // loop exit (one jmp each), and eligible for downstream layout
    // cleanup.
    let after_c1 = plan.chain.get(1).copied().unwrap_or(plan.exit);

    // --- c1 becomes the merged unrolled body ---
    let blk = func.blocks.get_mut(&c1).expect("chain head vanished");
    blk.insts.clear();
    blk.insts.extend(plan.seeds.iter().cloned());
    for _ in 0..plan.trip {
        for inst in &plan.body {
            blk.insts.push(inst.clone());
        }
    }
    blk.insts.push(X86ISelInst::new(
        X86Opcode::Jmp,
        vec![X86ISelOperand::Block(after_c1)],
    ));
    blk.successors = vec![after_c1];

    // --- c2..cm: empty pass-throughs toward the exit ---
    for i in 1..plan.chain.len() {
        let b = plan.chain[i];
        let next = plan.chain.get(i + 1).copied().unwrap_or(plan.exit);
        let blk = func.blocks.get_mut(&b).expect("chain block vanished");
        blk.insts.clear();
        blk.insts.push(X86ISelInst::new(
            X86Opcode::Jmp,
            vec![X86ISelOperand::Block(next)],
        ));
        blk.successors = vec![next];
    }

    // --- Header: drop the compare chain; fall through to the merged body
    let header = func
        .blocks
        .get_mut(&plan.header)
        .expect("header block vanished");
    header.insts.clear();
    header.insts.push(X86ISelInst::new(
        X86Opcode::Jmp,
        vec![X86ISelOperand::Block(c1)],
    ));
    header.successors = vec![c1];
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use trust_cg_lower::X86ISelBlock;
    use trust_cg_lower::function::Signature;

    const PRE: Block = Block(0);
    const HDR: Block = Block(1);
    const LATCH: Block = Block(2);
    const EXIT: Block = Block(3);
    const MID: Block = Block(4);

    fn empty_func(name: &str) -> X86ISelFunction {
        let sig = Signature {
            params: vec![],
            returns: vec![],
        };
        let mut f = X86ISelFunction::new(name.to_string(), sig);
        for b in 0..5u32 {
            f.blocks.insert(
                Block(b),
                X86ISelBlock {
                    insts: vec![],
                    successors: vec![],
                },
            );
        }
        f.block_order = vec![PRE, HDR, LATCH, EXIT, MID];
        f.next_vreg = 100;
        f
    }

    fn vreg(id: u32) -> VReg {
        VReg {
            id,
            class: RegClass::Gpr64,
        }
    }

    fn vreg32_op(id: u32) -> X86ISelOperand {
        X86ISelOperand::VReg(VReg {
            id,
            class: RegClass::Gpr32,
        })
    }

    fn vr(id: u32) -> X86ISelOperand {
        X86ISelOperand::VReg(vreg(id))
    }

    fn imm(v: i64) -> X86ISelOperand {
        X86ISelOperand::Imm(v)
    }

    fn blk(b: Block) -> X86ISelOperand {
        X86ISelOperand::Block(b)
    }

    fn cc(c: X86CondCode) -> X86ISelOperand {
        X86ISelOperand::CondCode(c)
    }

    fn inst(op: X86Opcode, ops: Vec<X86ISelOperand>) -> X86ISelInst {
        X86ISelInst::new(op, ops)
    }

    /// The Setcc-materialized counted loop the frontend emits:
    ///
    /// pre:   MovRI v0,#init ; MovRI v1,#0 ; Jmp hdr
    /// hdr:   CmpRI v0,#limit ; Setcc B,v2 ; CmpRI v2,#0 ; Jcc NE,latch ; Jmp exit
    /// latch: AddRI v1,#5 ; AddRI v0,#step ; Jmp hdr
    /// exit:  AddRI v1,#0 ; Ret          (flag WRITER first: exit-safe)
    fn counted_loop(init: i64, step: i64, limit: i64) -> X86ISelFunction {
        let mut f = empty_func("counted");
        let pre = f.blocks.get_mut(&PRE).unwrap();
        pre.insts = vec![
            inst(X86Opcode::MovRI, vec![vr(0), imm(init)]),
            inst(X86Opcode::MovRI, vec![vr(1), imm(0)]),
            inst(X86Opcode::Jmp, vec![blk(HDR)]),
        ];
        pre.successors = vec![HDR];
        let hdr = f.blocks.get_mut(&HDR).unwrap();
        hdr.insts = vec![
            inst(X86Opcode::CmpRI, vec![vr(0), imm(limit)]),
            inst(X86Opcode::Setcc, vec![vr(2), cc(X86CondCode::B)]),
            inst(X86Opcode::CmpRI, vec![vr(2), imm(0)]),
            inst(X86Opcode::Jcc, vec![cc(X86CondCode::NE), blk(LATCH)]),
            inst(X86Opcode::Jmp, vec![blk(EXIT)]),
        ];
        hdr.successors = vec![LATCH, EXIT];
        let latch = f.blocks.get_mut(&LATCH).unwrap();
        latch.insts = vec![
            inst(X86Opcode::AddRI, vec![vr(1), imm(5)]),
            // IV-indexed guard: makes the loop pass the profitability gate
            // (the b05-class shape the pass exists for).
            inst(
                X86Opcode::TrapBoundsCheckExact,
                vec![vr(20), vr(0), imm(999)],
            ),
            inst(X86Opcode::AddRI, vec![vr(0), imm(step)]),
            inst(X86Opcode::Jmp, vec![blk(HDR)]),
        ];
        latch.successors = vec![HDR];
        let exit = f.blocks.get_mut(&EXIT).unwrap();
        exit.insts = vec![
            inst(X86Opcode::AddRI, vec![vr(1), imm(0)]),
            inst(X86Opcode::Ret, vec![]),
        ];
        exit.successors = vec![];
        f
    }

    fn run(f: &mut X86ISelFunction) -> bool {
        X86LoopUnroll.run(f)
    }

    fn body_add5_count(f: &X86ISelFunction) -> usize {
        f.blocks[&LATCH]
            .insts
            .iter()
            .filter(|i| i.opcode == X86Opcode::AddRI && i.operands.as_slice() == [vr(1), imm(5)])
            .count()
    }

    #[test]
    fn unrolls_trip_4_setcc_form() {
        let mut f = counted_loop(0, 1, 4);
        assert!(run(&mut f));
        // Header is a bare fall-through to the merged body.
        let hdr = &f.blocks[&HDR];
        assert_eq!(hdr.insts.len(), 1);
        assert_eq!(hdr.insts[0].opcode, X86Opcode::Jmp);
        assert_eq!(hdr.successors, vec![LATCH]);
        // Merged body: seed + 4 iterations + Jmp exit.
        let latch = &f.blocks[&LATCH];
        assert_eq!(latch.successors, vec![EXIT]);
        assert_eq!(latch.insts[0].opcode, X86Opcode::MovRI);
        assert_eq!(latch.insts[0].operands.as_slice(), [vr(0), imm(0)]);
        assert_eq!(body_add5_count(&f), 4);
        assert_eq!(latch.insts.last().unwrap().opcode, X86Opcode::Jmp);
        assert_eq!(latch.insts.last().unwrap().operands.as_slice(), [blk(EXIT)]);
    }

    #[test]
    fn unrolls_direct_compare_form() {
        let mut f = counted_loop(0, 1, 4);
        // Rewrite the header to the direct form: CmpRI ; Jcc AE,exit ; Jmp latch.
        let hdr = f.blocks.get_mut(&HDR).unwrap();
        hdr.insts = vec![
            inst(X86Opcode::CmpRI, vec![vr(0), imm(4)]),
            inst(X86Opcode::Jcc, vec![cc(X86CondCode::AE), blk(EXIT)]),
            inst(X86Opcode::Jmp, vec![blk(LATCH)]),
        ];
        assert!(run(&mut f));
        assert_eq!(body_add5_count(&f), 4);
    }

    #[test]
    fn unrolls_cmprr_hoisted_const_bound() {
        // LICM-hoisted bound: pre defines v9 = MovRI #4; header CmpRR v0,v9.
        let mut f = counted_loop(0, 1, 999);
        let pre = f.blocks.get_mut(&PRE).unwrap();
        pre.insts
            .insert(0, inst(X86Opcode::MovRI, vec![vr(9), imm(4)]));
        let hdr = f.blocks.get_mut(&HDR).unwrap();
        hdr.insts[0] = inst(X86Opcode::CmpRR, vec![vr(0), vr(9)]);
        assert!(run(&mut f));
        assert_eq!(body_add5_count(&f), 4);
    }

    #[test]
    fn unrolls_cmprr_bound_first_swapped() {
        // CmpRR bound,iv with Setcc A ("bound > iv" == "iv < bound").
        let mut f = counted_loop(0, 1, 999);
        let pre = f.blocks.get_mut(&PRE).unwrap();
        pre.insts
            .insert(0, inst(X86Opcode::MovRI, vec![vr(9), imm(3)]));
        let hdr = f.blocks.get_mut(&HDR).unwrap();
        hdr.insts[0] = inst(X86Opcode::CmpRR, vec![vr(9), vr(0)]);
        hdr.insts[1] = inst(X86Opcode::Setcc, vec![vr(2), cc(X86CondCode::A)]);
        assert!(run(&mut f));
        assert_eq!(body_add5_count(&f), 3);
    }

    #[test]
    fn unrolls_two_block_chain_body() {
        // Body split: LATCH does the work then falls through to MID which
        // increments the IV and jumps back. Chain = [LATCH, MID]; after the
        // unroll MID is deleted and LATCH holds the merged copies.
        let mut f = counted_loop(0, 1, 3);
        {
            let latch = f.blocks.get_mut(&LATCH).unwrap();
            latch.insts = vec![
                inst(X86Opcode::AddRI, vec![vr(1), imm(5)]),
                inst(
                    X86Opcode::TrapBoundsCheckExact,
                    vec![vr(20), vr(0), imm(999)],
                ),
            ];
            latch.successors = vec![MID];
        }
        {
            let mid = f.blocks.get_mut(&MID).unwrap();
            mid.insts = vec![
                inst(X86Opcode::AddRI, vec![vr(0), imm(1)]),
                inst(X86Opcode::Jmp, vec![blk(HDR)]),
            ];
            mid.successors = vec![HDR];
        }
        assert!(run(&mut f));
        assert_eq!(body_add5_count(&f), 3);
        // The merged-away chain block survives as an empty pass-through
        // (block ids must stay contiguous for regalloc replay).
        let mid = &f.blocks[&MID];
        assert_eq!(mid.insts.len(), 1);
        assert_eq!(mid.insts[0].opcode, X86Opcode::Jmp);
        assert_eq!(mid.successors, vec![EXIT]);
        let latch = &f.blocks[&LATCH];
        assert_eq!(latch.successors, vec![MID]);
        // seed + 3*(AddRI acc + guard + AddRI iv) + Jmp
        assert_eq!(latch.insts.len(), 1 + 3 * 3 + 1);
    }

    #[test]
    fn unrolls_merge_copy_dialect() {
        // The REAL importer dialect around the k-loop: IV initialized by a
        // preheader COPY of a constant vreg, compared through a header-local
        // copy, stepped by AddRR with a LICM-hoisted constant-1 vreg.
        let mut f = counted_loop(0, 1, 999);
        {
            let pre = f.blocks.get_mut(&PRE).unwrap();
            pre.insts = vec![
                inst(X86Opcode::MovRI, vec![vr(10), imm(0)]), // zero const
                inst(X86Opcode::MovRI, vec![vr(11), imm(1)]), // one const
                inst(X86Opcode::MovRI, vec![vr(9), imm(3)]),  // bound const
                inst(X86Opcode::MovRR, vec![vr(0), vr(10)]),  // iv = copy(zero)
                inst(X86Opcode::MovRI, vec![vr(1), imm(0)]),
                inst(X86Opcode::Jmp, vec![blk(HDR)]),
            ];
        }
        {
            let hdr = f.blocks.get_mut(&HDR).unwrap();
            hdr.insts = vec![
                inst(X86Opcode::MovRR, vec![vr(5), vr(0)]), // header copy of iv
                inst(X86Opcode::CmpRR, vec![vr(5), vr(9)]),
                inst(X86Opcode::Setcc, vec![vr(2), cc(X86CondCode::B)]),
                inst(X86Opcode::CmpRI, vec![vr(2), imm(0)]),
                inst(X86Opcode::Jcc, vec![cc(X86CondCode::NE), blk(LATCH)]),
                inst(X86Opcode::Jmp, vec![blk(EXIT)]),
            ];
        }
        {
            let latch = f.blocks.get_mut(&LATCH).unwrap();
            latch.insts = vec![
                inst(X86Opcode::AddRI, vec![vr(1), imm(5)]),
                inst(
                    X86Opcode::TrapBoundsCheckExact,
                    vec![vr(20), vr(0), imm(999)],
                ),
                inst(X86Opcode::AddRR, vec![vr(0), vr(11)]), // iv += one
                inst(X86Opcode::Jmp, vec![blk(HDR)]),
            ];
        }
        assert!(run(&mut f));
        assert_eq!(body_add5_count(&f), 3);
        // Seed synthesized as a direct MovRI of the proven init.
        let latch = &f.blocks[&LATCH];
        assert_eq!(latch.insts[0].opcode, X86Opcode::MovRI);
        assert_eq!(latch.insts[0].operands.as_slice(), [vr(0), imm(0)]);
    }

    #[test]
    fn unrolls_real_importer_dialect_3op() {
        // The exact observed b05 k-loop header/latch dialect: header copy of
        // the IV, CmpRR against a far-defined const vreg, Setcc + self-Movzx
        // + widening Movzx + 3-OPERAND AndRI #1 + CmpRI #0 + Jcc NE; latch
        // increments via 3-operand AddRR with a hoisted const-1 vreg and a
        // merge copy back into the IV.
        let mut f = counted_loop(0, 1, 999);
        {
            let pre = f.blocks.get_mut(&PRE).unwrap();
            pre.insts = vec![
                inst(X86Opcode::MovRI, vec![vr(9), imm(3)]), // bound const
                inst(X86Opcode::MovRI, vec![vr(11), imm(1)]), // one const
                inst(X86Opcode::MovRI, vec![vr(10), imm(0)]), // zero const
                inst(X86Opcode::MovRR, vec![vr(0), vr(10)]), // iv = copy(zero)
                inst(X86Opcode::MovRI, vec![vr(1), imm(0)]),
                inst(X86Opcode::Jmp, vec![blk(HDR)]),
            ];
        }
        {
            let hdr = f.blocks.get_mut(&HDR).unwrap();
            hdr.insts = vec![
                inst(X86Opcode::MovRR, vec![vr(5), vr(0)]),
                inst(X86Opcode::CmpRR, vec![vr(5), vr(9)]),
                inst(X86Opcode::Setcc, vec![vr(2), cc(X86CondCode::B)]),
                inst(X86Opcode::Movzx, vec![vr(2), vr(2)]), // self zero-extend
                inst(X86Opcode::Movzx, vec![vr(6), vr(2)]), // widen
                inst(X86Opcode::AndRI, vec![vr(6), vr(6), imm(1)]), // 3-op mask
                inst(X86Opcode::CmpRI, vec![vr(6), imm(0)]),
                inst(X86Opcode::Jcc, vec![cc(X86CondCode::NE), blk(LATCH)]),
                inst(X86Opcode::Jmp, vec![blk(EXIT)]),
            ];
        }
        {
            let latch = f.blocks.get_mut(&LATCH).unwrap();
            latch.insts = vec![
                inst(X86Opcode::AddRI, vec![vr(1), imm(5)]),
                inst(
                    X86Opcode::TrapBoundsCheckExact,
                    vec![vr(20), vr(0), imm(999)],
                ),
                // k_next = k + one ; k = k_next  (3-op + merge copy)
                inst(X86Opcode::AddRR, vec![vr(7), vr(0), vr(11)]),
                inst(X86Opcode::MovRR, vec![vr(0), vr(7)]),
                inst(X86Opcode::Jmp, vec![blk(HDR)]),
            ];
        }
        assert!(run(&mut f));
        assert_eq!(body_add5_count(&f), 3);
        let latch = &f.blocks[&LATCH];
        assert_eq!(latch.insts[0].opcode, X86Opcode::MovRI);
        assert_eq!(latch.insts[0].operands.as_slice(), [vr(0), imm(0)]);
    }

    #[test]
    fn unrolls_through_flagfree_forwarding_exit() {
        // Exit is a flag-neutral forwarding block; safety must flow through
        // to MID, which writes flags before any read.
        let mut f = counted_loop(0, 1, 4);
        {
            let exit = f.blocks.get_mut(&EXIT).unwrap();
            exit.insts = vec![inst(X86Opcode::Jmp, vec![blk(MID)])];
            exit.successors = vec![MID];
        }
        {
            let mid = f.blocks.get_mut(&MID).unwrap();
            mid.insts = vec![
                inst(X86Opcode::AddRI, vec![vr(1), imm(0)]),
                inst(X86Opcode::Ret, vec![]),
            ];
        }
        assert!(run(&mut f));
        assert_eq!(body_add5_count(&f), 4);
    }

    #[test]
    fn refuses_flag_reader_behind_forwarding_exit() {
        let mut f = counted_loop(0, 1, 4);
        {
            let exit = f.blocks.get_mut(&EXIT).unwrap();
            exit.insts = vec![inst(X86Opcode::Jmp, vec![blk(MID)])];
            exit.successors = vec![MID];
        }
        {
            let mid = f.blocks.get_mut(&MID).unwrap();
            mid.insts = vec![
                inst(X86Opcode::Setcc, vec![vr(5), cc(X86CondCode::B)]),
                inst(X86Opcode::Ret, vec![]),
            ];
        }
        assert!(!run(&mut f));
    }

    #[test]
    fn unrolls_step_2_and_trip_1() {
        let mut f = counted_loop(0, 2, 8); // trips: k=0,2,4,6 -> 4
        assert!(run(&mut f));
        assert_eq!(body_add5_count(&f), 4);

        let mut f1 = counted_loop(0, 1, 1); // single trip
        assert!(run(&mut f1));
        assert_eq!(body_add5_count(&f1), 1);
        assert_eq!(f1.blocks[&LATCH].successors, vec![EXIT]);
    }

    #[test]
    fn refuses_unprofitable_pure_alu_body() {
        // A data-dependent pure-ALU body (the crc32 bit-loop class): no
        // IV-derived guard or address — unrolling only removes loop
        // control and pays in code size. Must refuse.
        let mut f = counted_loop(0, 1, 4);
        let latch = f.blocks.get_mut(&LATCH).unwrap();
        latch.insts = vec![
            inst(X86Opcode::AddRI, vec![vr(1), imm(5)]),
            inst(X86Opcode::AddRI, vec![vr(0), imm(1)]),
            inst(X86Opcode::Jmp, vec![blk(HDR)]),
        ];
        assert!(!run(&mut f));
    }

    #[test]
    fn refuses_zero_trip_and_over_cap() {
        let mut f = counted_loop(5, 1, 5); // 5 < 5 false immediately
        assert!(!run(&mut f));
        let mut f2 = counted_loop(0, 1, (MAX_TRIP + 1) as i64);
        assert!(!run(&mut f2));
    }

    #[test]
    fn refuses_symbolic_bound() {
        let mut f = counted_loop(0, 1, 4);
        let hdr = f.blocks.get_mut(&HDR).unwrap();
        // v9 has NO def anywhere: not a resolvable constant.
        hdr.insts[0] = inst(X86Opcode::CmpRR, vec![vr(0), vr(9)]);
        assert!(!run(&mut f));
    }

    #[test]
    fn refuses_bound_defined_inside_loop() {
        let mut f = counted_loop(0, 1, 999);
        let hdr = f.blocks.get_mut(&HDR).unwrap();
        hdr.insts[0] = inst(X86Opcode::CmpRR, vec![vr(0), vr(9)]);
        let latch = f.blocks.get_mut(&LATCH).unwrap();
        latch
            .insts
            .insert(0, inst(X86Opcode::MovRI, vec![vr(9), imm(4)]));
        assert!(!run(&mut f));
    }

    #[test]
    fn refuses_call_or_branch_in_body() {
        let mut f = counted_loop(0, 1, 4);
        let latch = f.blocks.get_mut(&LATCH).unwrap();
        latch
            .insts
            .insert(0, inst(X86Opcode::Jcc, vec![cc(X86CondCode::E), blk(EXIT)]));
        assert!(!run(&mut f));
    }

    #[test]
    fn refuses_header_def_escape() {
        let mut f = counted_loop(0, 1, 4);
        // Exit reads the Setcc bool v2 -> chain removal would break it.
        let exit = f.blocks.get_mut(&EXIT).unwrap();
        exit.insts
            .insert(0, inst(X86Opcode::MovRR, vec![vr(3), vr(2)]));
        assert!(!run(&mut f));
    }

    #[test]
    fn refuses_latch_flag_reader_without_writer() {
        let mut f = counted_loop(0, 1, 4);
        let latch = f.blocks.get_mut(&LATCH).unwrap();
        // A Setcc at the body head reads flags established by the header
        // chain — clone 2 would read clone 1's stale flags instead.
        latch
            .insts
            .insert(0, inst(X86Opcode::Setcc, vec![vr(4), cc(X86CondCode::B)]));
        assert!(!run(&mut f));
    }

    #[test]
    fn refuses_partial_flag_writer_before_body_reader() {
        // Adversarial-review finding: Dec preserves CF, so a body
        // `Dec ; AdcRR` pair would read the DELETED header compare's CF
        // across the clone boundary. Dec must not count as a flag barrier.
        let mut f = counted_loop(0, 1, 4);
        let latch = f.blocks.get_mut(&LATCH).unwrap();
        latch
            .insts
            .insert(0, inst(X86Opcode::AdcRR, vec![vr(4), vr(4), vr(4)]));
        latch.insts.insert(0, inst(X86Opcode::Dec, vec![vr(8)]));
        assert!(!run(&mut f));
    }

    #[test]
    fn refuses_partial_flag_writer_in_exit() {
        // Exit `Dec ; Setcc B`: Dec preserves CF, the Setcc would read the
        // deleted header compare's CF. Must refuse (writes_flags(Dec) is
        // true — the old barrier model accepted this).
        let mut f = counted_loop(0, 1, 4);
        let exit = f.blocks.get_mut(&EXIT).unwrap();
        exit.insts
            .insert(0, inst(X86Opcode::Setcc, vec![vr(5), cc(X86CondCode::B)]));
        exit.insts.insert(0, inst(X86Opcode::Dec, vec![vr(8)]));
        assert!(!run(&mut f));
    }

    #[test]
    fn accepts_ud2_terminated_exit() {
        let mut f = counted_loop(0, 1, 4);
        let exit = f.blocks.get_mut(&EXIT).unwrap();
        exit.insts = vec![inst(X86Opcode::Ud2, vec![])];
        exit.successors = vec![];
        assert!(run(&mut f));
        assert_eq!(body_add5_count(&f), 4);
    }

    #[test]
    fn refuses_hidden_def_xchg_in_body() {
        let mut f = counted_loop(0, 1, 4);
        let latch = f.blocks.get_mut(&LATCH).unwrap();
        latch
            .insts
            .insert(0, inst(X86Opcode::Xchg, vec![vr(4), vr(0)]));
        assert!(!run(&mut f));
    }

    #[test]
    fn refuses_mixed_class_cmprr() {
        let mut f = counted_loop(0, 1, 999);
        let pre = f.blocks.get_mut(&PRE).unwrap();
        pre.insts
            .insert(0, inst(X86Opcode::MovRI, vec![vreg32_op(9), imm(4)]));
        let hdr = f.blocks.get_mut(&HDR).unwrap();
        hdr.insts[0] = inst(X86Opcode::CmpRR, vec![vr(0), vreg32_op(9)]);
        assert!(!run(&mut f));
    }

    #[test]
    fn refuses_exit_flag_reader() {
        let mut f = counted_loop(0, 1, 4);
        let exit = f.blocks.get_mut(&EXIT).unwrap();
        exit.insts
            .insert(0, inst(X86Opcode::Setcc, vec![vr(5), cc(X86CondCode::B)]));
        assert!(!run(&mut f));
    }

    #[test]
    fn unrolls_despite_post_loop_iv_reuse() {
        // isel reuses vreg ids: a def of the IV id AFTER the loop is
        // irrelevant (the preheader's last def re-establishes init on
        // every entry) and must not block the unroll.
        let mut f = counted_loop(0, 1, 4);
        let exit = f.blocks.get_mut(&EXIT).unwrap();
        exit.insts
            .insert(0, inst(X86Opcode::MovRI, vec![vr(0), imm(9)]));
        assert!(run(&mut f));
        assert_eq!(body_add5_count(&f), 4);
        // The post-loop def is untouched.
        assert!(
            f.blocks[&EXIT]
                .insts
                .iter()
                .any(|i| i.opcode == X86Opcode::MovRI && i.operands.as_slice() == [vr(0), imm(9)])
        );
    }

    #[test]
    fn refuses_iv_defined_in_header() {
        // A header that REDEFINES the IV (not a copy of it) breaks the
        // compare-reads-loop-carried-value premise.
        let mut f = counted_loop(0, 1, 4);
        let hdr = f.blocks.get_mut(&HDR).unwrap();
        hdr.insts
            .insert(0, inst(X86Opcode::AddRI, vec![vr(0), imm(0)]));
        assert!(!run(&mut f));
    }

    #[test]
    fn refuses_trap_pseudo_in_header_chain() {
        // A hoisted TrapBoundsCheckExact in the header is MemoryEffect::Pure
        // (register-only) yet MUST NOT be deleted with the compare chain.
        let mut f = counted_loop(0, 1, 4);
        let hdr = f.blocks.get_mut(&HDR).unwrap();
        hdr.insts.insert(
            0,
            inst(X86Opcode::TrapBoundsCheckExact, vec![vr(7), vr(8), imm(24)]),
        );
        assert!(!run(&mut f));
    }

    #[test]
    fn refuses_eh_functions() {
        let mut f = counted_loop(0, 1, 4);
        f.eh_info.personality = Some("rust_eh_personality".to_string());
        assert!(!run(&mut f));
    }

    #[test]
    fn idempotent_after_unroll() {
        let mut f = counted_loop(0, 1, 4);
        assert!(run(&mut f));
        assert!(!run(&mut f));
        assert_eq!(body_add5_count(&f), 4);
    }

    #[test]
    fn unrolls_countdown_with_sub() {
        // Counting DOWN with SubRI: init=4, step -1, exit when v0 == 0.
        let mut f = counted_loop(4, 1, 0);
        {
            let hdr = f.blocks.get_mut(&HDR).unwrap();
            hdr.insts = vec![
                inst(X86Opcode::CmpRI, vec![vr(0), imm(0)]),
                inst(X86Opcode::Jcc, vec![cc(X86CondCode::E), blk(EXIT)]),
                inst(X86Opcode::Jmp, vec![blk(LATCH)]),
            ];
            let latch = f.blocks.get_mut(&LATCH).unwrap();
            latch.insts = vec![
                inst(X86Opcode::AddRI, vec![vr(1), imm(5)]),
                inst(
                    X86Opcode::TrapBoundsCheckExact,
                    vec![vr(20), vr(0), imm(999)],
                ),
                inst(X86Opcode::SubRI, vec![vr(0), imm(1)]),
                inst(X86Opcode::Jmp, vec![blk(HDR)]),
            ];
        }
        assert!(run(&mut f));
        assert_eq!(body_add5_count(&f), 4);
    }

    #[test]
    fn unrolls_iv_copy_shuffle() {
        // Latch updates iv through a copy: v3 = MovRR v0 ; AddRI v3,#1 ;
        // v0 = MovRR v3 — the affine walk must still find step 1.
        let mut f = counted_loop(0, 1, 3);
        let latch = f.blocks.get_mut(&LATCH).unwrap();
        latch.insts = vec![
            inst(X86Opcode::AddRI, vec![vr(1), imm(5)]),
            inst(
                X86Opcode::TrapBoundsCheckExact,
                vec![vr(20), vr(0), imm(999)],
            ),
            inst(X86Opcode::MovRR, vec![vr(3), vr(0)]),
            inst(X86Opcode::AddRI, vec![vr(3), imm(1)]),
            inst(X86Opcode::MovRR, vec![vr(0), vr(3)]),
            inst(X86Opcode::Jmp, vec![blk(HDR)]),
        ];
        assert!(run(&mut f));
        assert_eq!(body_add5_count(&f), 3);
    }
}
