// trust-cg-opt - x86-64 induction-variable strength reduction
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Induction-variable strength reduction (OPT-3a) for x86-64 ISel-output
//! functions.
//!
//! # What it does
//!
//! Replaces a per-iteration multiply of a loop induction variable by a
//! compile-time-constant stride with an add recurrence:
//!
//! ```text
//!   loop body:  d = imul iv', s           ; every iteration (3c latency, on
//!                                         ; the address critical path;
//!                                         ; iv' = iv or a proven copy)
//! ```
//!
//! becomes
//!
//! ```text
//!   preheader:  r = imul iv, s            ; ONCE (the entering iv; s as an
//!                                         ; ImulRRI immediate)
//!   loop body:  d = mov r                 ; replaces the multiply
//!   ...
//!   right after the iv update (iv = iv + step):
//!               r = add r, s*step         ; the recurrence advance (AddRI)
//! ```
//!
//! This is the classical strength reduction LLVM performs in
//! `LoopStrengthReduce`: the canonical win is a matmul-style nested loop
//! addressing `a[i*N + k]`, where `i*N` (stride `N` not SIB-encodable, e.g.
//! 24) is re-multiplied on every iteration of the INNER loop. LICM cannot
//! hoist the multiply (x86 `imul` writes RFLAGS), so before this pass it
//! stays on the hot path. After this pass the multiply is a register copy
//! that copy-prop/LICM/DCE downstream passes clean up further.
//!
//! # Correctness argument (hand proof + gated ring-lemma discharge)
//!
//! The rewrite maintains the invariant `r == iv * s` (all values mod 2^64,
//! the Gpr64 carrier width — identical to release-mode wrapping-mul
//! semantics) at every program point of the loop except between the iv
//! update and the immediately-following recurrence advance, where `r` is
//! never read:
//!
//!   * Base case: the preheader seed `r = imul iv, s` is executed on every
//!     entry into the loop (the loop has a natural preheader, its header's
//!     only non-loop predecessor, and no side entry into any body block),
//!     and computes the SAME operation the deleted multiply would on the
//!     entering `iv`.
//!   * Inductive step: the loop's ONLY definition of `iv` inside the body
//!     is the update `iv = iv + step` (a compile-time-constant step); the
//!     advance `r = r + s*step` is inserted IMMEDIATELY after it, so both
//!     are updated in lockstep on every path. Given `r == iv*s` before the
//!     pair, `r' == r + s*step == (iv + step)*s == iv'*s` after it. The
//!     algebraic identity `(iv + step)*s == iv*s + s*step  (mod 2^w)` is
//!     discharged only through the pipeline admission callback. The normal
//!     fast path structurally recognizes this exact identity and cites
//!     distributivity plus multiplication commutativity in `Z/2^w`; any
//!     non-matching obligation falls through to the formal solver
//!     (`trust_cg_verify::pass_validators::StrengthReduceRecurrenceValidator`).
//!     An undischarged obligation means the rewrite is NOT applied; the
//!     original multiply is always correct.
//!   * The multiply's IV operand may be the IV carrier itself or a COPY
//!     CHAIN proven to hold the IV's current value at the multiply (see
//!     `resolve_iv_operand` for the chain side conditions — this is the
//!     load-bearing generalization for real phi-eliminated loop bodies,
//!     where every use flows through single-def `MovRR` renames), or a chain
//!     rooted at a multi-def PASS-THROUGH block param (see the dedicated
//!     section below). Since the operand equals `iv` at the multiply and
//!     `r == iv*s` there, replacing the multiply with `d = mov r` writes the
//!     identical value to `d`.
//!
//! # Pass-through block params (multi-def canonicalization)
//!
//! Phi elimination threads an OUTER loop's IV through an INNER loop as a
//! block param with one definition per predecessor edge: the matmul `i*N`
//! multiply reads `i` through a param of the inner `k`-loop whose
//! entry-edge def copies `i` in and whose back-edge def passes the param's
//! own value through unchanged. Such a MULTI-DEF vreg defeats the
//! single-def copy-chain rule, so `resolve_value_at` additionally admits
//! a chain rooted at a pass-through param `P` under these conditions
//! (checked in `resolve_passthrough_param`):
//!
//!   P1. EVERY definition of `P` (whole function) is a plain Gpr64
//!       `MovRR [P, s_i]` located inside the loop body and outside the
//!       latch (update block);
//!   P2. the read of `P` is MUST-COVERED by `P`'s defs: every CFG path
//!       from the loop-header start to the read executes some def of `P`
//!       (`param_defs_cover_read`, a boolean AND-meet dataflow over the
//!       body with the header forced uncovered — the strict generalization
//!       of the single-def rule's dominance condition 3, which implies
//!       coverage via the same no-side-entry/preheader-entry argument);
//!   P3. every def's source `s_i` resolves AT THE DEF SITE — through the
//!       same chain rules — either to the IV's current value (an "entry
//!       def") or to `P` itself (a "pass-through def", whose root read of
//!       `P` must again be must-covered per P2). Nested params (the IV
//!       threaded through several loop levels) recurse; a chain rooting at
//!       a param OTHER than the one whose defs are currently under
//!       validation (a mutual param cycle, which edge-split phi
//!       elimination never produces) is conservatively rejected.
//!
//! If ANY def fails these conditions the param is not canonicalized and
//! the multiply stays in place (fail-safe).
//!
//! ## Why `P == iv` at every admitted read (extension of the chain proof)
//!
//! Take any admitted read R of `P` (R inside the body and — the same
//! no-stale-read condition as chains — not at/after the update if in the
//! latch). Let H* be the LAST execution of the loop-header start before R.
//! The segment H* -> R executes no IV update: the update lives in the
//! latch, whose only successor is the header, so an update inside the
//! segment would put a header entry after it and before R, contradicting
//! the choice of H*. By P2 the segment executes at least one def of `P`
//! (every H*-to-R path passes one; entry executions are covered too, since
//! the first header execution precedes every body read — natural-loop
//! bodies are unreachable before the header). Let D (`MovRR [P, s]`) be
//! the last def executed before R: `P` at R holds exactly what D wrote,
//! and `iv` is unchanged between D and R.
//!
//!   * If D's source chain roots at the IV, the unmodified chain-window
//!     argument (with D as the final use — D is never in the latch by P1)
//!     gives `s == iv` at D. Hence `P == iv` from D through R.
//!   * If D's source chain roots at `P` itself, the chain transports `P`'s
//!     value at the root copy C (`c = mov P`). C dominates its reader and
//!     the window C -> D contains no IV update (the same window argument),
//!     and the root read at C is itself covered (P3) — so by induction on
//!     execution order (C executes strictly before D), `P == iv` held at
//!     C, and D rewrites `P` with that still-current value.
//!
//! The induction is well-founded: each pass-through def's justification
//! steps to a strictly earlier covered read, and P2 guarantees a def of
//! `P` precedes every covered read on any finite trace, so the regress
//! terminates at an entry def whose chain roots at the IV.
//!
//! # Side conditions (each must hold or the candidate is skipped)
//!
//!   1. The loop is a natural loop with a preheader (unique non-loop
//!      predecessor of the header) and NO side entries: every body block
//!      except the header has all predecessors inside the body.
//!   2. `iv` has EXACTLY ONE definition inside the loop body, of one of the
//!      shapes (all operands Gpr64 vregs):
//!        * writeback `MovRR [iv, t]` with `t` defined exactly once in the
//!          whole function, inside the body, in the SAME block before the
//!          writeback (lockstep: a writeback re-executing without a fresh
//!          increment would advance the recurrence without advancing the
//!          IV), by `AddRR [t, iv', c]` (either operand order) where `iv'`
//!          resolves to the IV via `resolve_iv_operand` and `c` is a
//!          `canon_const` constant, or by `AddRI [t, iv', imm]`;
//!        * tied increment `AddRI [iv, imm]` (two-operand form).
//!          The update block must be a LATCH: its only successor is the loop
//!          header (this is what makes copy-chain windows re-execute before any
//!          later use — see `resolve_iv_operand`).
//!   3. The multiply is `ImulRR [d, x, y]` (one operand resolving to the IV,
//!      the other to a `canon_const` compile-time constant) or
//!      `ImulRRI [d, x, imm]` (`x` resolving to the IV), at opcode-default
//!      flags with no proof origin, inside the loop body, operands Gpr64.
//!   4. Definite initialization: `iv` has a definition in the preheader
//!      itself or in a block dominating the preheader, so the preheader
//!      seed never reads a possibly-undefined vreg (which would trip the
//!      fail-closed definite-init gate). The stride is re-materialized as
//!      an immediate, so no other new reads are introduced.
//!   5. RFLAGS deadness, three separate points (the pass both REMOVES a
//!      flag writer — the multiply becomes a flag-free `mov` — and INSERTS
//!      flag writers at the preheader seed and the advance): at each point
//!      the current flags must be provably dead — a FULL flag overwrite is
//!      reached before any flag reader, call, return, or conditional
//!      branch, following unconditional control flow through at most a few
//!      blocks.
//!   6. The per-(width, step, stride) recurrence obligation is discharged
//!      by the admission callback's exact ring-lemma recognition or its
//!      formal-solver fallback (see above), and both `stride` and
//!      `stride*step` fit in the sign-extended imm32 the emitted
//!      `ImulRRI`/`AddRI` forms encode. SIB-legal strides ({1,2,4,8}) are
//!      deliberately SKIPPED: those scale-multiplies are the OPT-7 SIB
//!      address fold's territory (a single `mov (%base,%idx,scale)` beats a
//!      recurrence), and reducing them would destroy the scale-def shape
//!      that fold matches.
//!
//! Every emitted opcode (`ImulRRI`, `AddRI`, `MovRR`) is already produced
//! by ISel on existing paths, so the per-instruction proof certificate
//! surface, the encoder, and decode-check cover them — a gap would fail
//! closed downstream, never miscompile.
//!
//! # Reference
//!
//! LLVM `LoopStrengthReduce.cpp`; Muchnick ch. 14.1; the AArch64
//! counterpart `crates/trust-cg-opt/src/strength_reduce.rs` (which operates
//! on the phi-based `MachFunction` IR; this pass is its port to the phi-free
//! multi-def-carrier `X86ISelFunction` IR).

use std::collections::{HashMap, HashSet};

use trust_cg_ir::regs::RegClass;
use trust_cg_ir::{VReg, X86Opcode};
use trust_cg_lower::instructions::Block;
use trust_cg_lower::{X86ISelFunction, X86ISelInst, X86ISelOperand};

use crate::effects::{x86_produces_value, x86_reads_flags};
use crate::mach_view;
use crate::x86_pass_manager::X86MachinePass;
use crate::x86_peephole::{FlagOverwrite, condition_flag_overwrite};

/// Admission callback: must return `true` only when the per-`(width, step,
/// stride)` recurrence obligation `(iv + step)*stride == iv*stride +
/// stride*step (mod 2^width)` has been discharged either by exact structural
/// recognition of the cited ring identity or by the formal-solver fallback.
/// Provided by the pipeline (which binds it to
/// `StrengthReduceRecurrenceValidator` + the fail-closed certified pass chain);
/// an undischarged obligation leaves the original multiply in place.
pub type StrengthReduceAdmission = fn(width: u32, step: i64, stride: i64) -> bool;

/// Induction-variable strength reduction for x86-64 ISel machine functions.
pub struct X86StrengthReduce {
    admit: StrengthReduceAdmission,
}

impl X86StrengthReduce {
    /// Create the pass with the given per-(width, step, stride) admission
    /// gate.
    pub fn new(admit: StrengthReduceAdmission) -> Self {
        Self { admit }
    }

    /// Run directly on an ISel function (test entry point).
    pub fn run_on_function(&mut self, func: &mut X86ISelFunction) -> bool {
        run_impl(func, self.admit)
    }
}

impl X86MachinePass for X86StrengthReduce {
    fn name(&self) -> &str {
        "x86-strength-reduce"
    }

    fn run(&mut self, func: &mut X86ISelFunction) -> bool {
        run_impl(func, self.admit)
    }
}

fn log_enabled() -> bool {
    std::env::var_os("TRUST_CG_X86_SR_LOG").is_some()
}

/// Verbose per-rejection diagnostics (development / triage only).
fn debug_enabled() -> bool {
    std::env::var_os("TRUST_CG_X86_SR_DEBUG").is_some()
}

macro_rules! sr_debug {
    ($($arg:tt)*) => {
        if debug_enabled() {
            eprintln!($($arg)*);
        }
    };
}

/// Hard cap on rewrites per function. Termination is already guaranteed (each
/// rewrite deletes one in-loop multiply and only ever inserts multiplies into
/// strictly shallower blocks — a decreasing multiset measure); the cap is
/// belt-and-suspenders against an analysis bug looping the driver.
const MAX_REDUCTIONS_PER_FUNCTION: usize = 64;

/// Copy-chain chase depth bound for [`canon_const`] / [`resolve_iv_operand`].
const MAX_CHAIN_DEPTH: u32 = 8;

fn run_impl(func: &mut X86ISelFunction, admit: StrengthReduceAdmission) -> bool {
    if func.block_order.len() < 2 {
        return false;
    }

    // Development triage: dump the whole function before the pass runs.
    if debug_enabled() && std::env::var_os("TRUST_CG_X86_SR_DUMP").is_some() {
        eprintln!("x86-strength-reduce[dump] fn `{}`:", func.name);
        for block_id in &func.block_order {
            let Some(block) = func.blocks.get(block_id) else {
                continue;
            };
            eprintln!("  block {:?} succs {:?}:", block_id.0, block.successors);
            for (i, inst) in block.insts.iter().enumerate() {
                eprintln!("    [{i}] {:?} {:?}", inst.opcode, inst.operands);
            }
        }
    }

    let mut changed = false;
    // Apply one reduction at a time and re-derive every analysis from the
    // rewritten function. Functions are small at this stage and the pass runs
    // once per opt-pipeline invocation; full recomputation keeps every index
    // and def-count trivially consistent (no incremental bookkeeping to get
    // wrong).
    for _ in 0..MAX_REDUCTIONS_PER_FUNCTION {
        if !apply_one_reduction(func, admit) {
            break;
        }
        changed = true;
    }
    changed
}

// ===========================================================================
// One-candidate driver
// ===========================================================================

/// A matched induction variable.
#[derive(Debug, Clone, Copy)]
struct IvMatch {
    /// The induction-variable carrier vreg.
    iv: VReg,
    /// Compile-time constant step of the single in-body update.
    step: i64,
    /// Location of the single in-body definition of `iv` (the update); the
    /// recurrence advance is inserted immediately after it. The update block
    /// is a latch (single successor: the loop header).
    update_block: Block,
    update_idx: usize,
}

/// A strength-reduction candidate: one in-loop multiply of an IV by a
/// compile-time-constant stride.
///
/// The stride VALUE must be a compile-time constant (an `ImulRRI` immediate,
/// or an `ImulRR` register operand canonicalized through single-def `MovRR`
/// copies to a single-def `MovRI` — see [`canon_const`]): the per-instance
/// proof obligation carries it as a literal, keeping the obligation
/// single-symbolic-input (constant multiplies bit-blast to shift-add
/// circuits the solver discharges quickly; a symbolic-times-symbolic 64-bit
/// `bvmul` miter is beyond its practical reach, and an undischargeable
/// obligation would silently disable the pass). A stride held in a register
/// whose runtime value is NOT a provable constant is deliberately not
/// reduced. The rewrite re-materializes the stride as an immediate, so the
/// original stride register (and its possibly-body-local copy chain) is
/// never read at any new position.
#[derive(Debug, Clone, Copy)]
struct Candidate {
    iv: IvMatch,
    /// The compile-time constant stride.
    stride: i64,
    /// Location of the multiply to replace.
    mul_block: Block,
    mul_idx: usize,
    /// dst of the multiply.
    dst: VReg,
    /// Preheader of the loop this candidate reduces over.
    preheader: Block,
}

fn apply_one_reduction(func: &mut X86ISelFunction, admit: StrengthReduceAdmission) -> bool {
    let preds = build_predecessor_map(func);
    let idom = compute_idom(func, &preds);
    let mut loops = find_natural_loops(func, &preds, &idom);
    sr_debug!(
        "x86-strength-reduce[debug] `{}`: {} block(s), {} natural loop(s)",
        func.name,
        func.block_order.len(),
        loops.len()
    );
    if loops.is_empty() {
        return false;
    }

    // Deterministic order: innermost first, header id as tiebreaker.
    loops.sort_by_key(|lp| (std::cmp::Reverse(lp.depth), lp.header.0));

    let def_sites = build_def_sites(func);

    for lp in &loops {
        let Some(candidate) = find_candidate(func, lp, &preds, &idom, &def_sites, admit) else {
            continue;
        };
        apply_candidate(func, &candidate);
        return true;
    }
    false
}

// ===========================================================================
// Candidate discovery
// ===========================================================================

fn find_candidate(
    func: &X86ISelFunction,
    lp: &NaturalLoop,
    preds: &HashMap<Block, Vec<Block>>,
    idom: &HashMap<Block, Block>,
    def_sites: &HashMap<VReg, Vec<(Block, usize)>>,
    admit: StrengthReduceAdmission,
) -> Option<Candidate> {
    let Some(preheader) = lp.preheader else {
        sr_debug!(
            "x86-strength-reduce[debug] `{}` loop@{:?}: no natural preheader",
            func.name,
            lp.header.0
        );
        return None;
    };

    // Side condition 1: no side entries. Every body block except the header
    // has all predecessors inside the body, and the header's only non-body
    // predecessor is the preheader (guaranteed by the mach_view preheader
    // rule, but re-checked here so the invariant is local).
    let empty: Vec<Block> = Vec::new();
    for block in &lp.body {
        let block_preds = preds.get(block).unwrap_or(&empty);
        if *block == lp.header {
            if block_preds
                .iter()
                .any(|p| !lp.body.contains(p) && *p != preheader)
            {
                return None;
            }
        } else if block_preds.iter().any(|p| !lp.body.contains(p)) {
            sr_debug!(
                "x86-strength-reduce[debug] `{}` loop@{:?}: side entry into body block {:?}",
                func.name,
                lp.header.0,
                block.0
            );
            return None;
        }
    }

    // Side condition 5 (preheader point): the seed multiply writes RFLAGS
    // right before the preheader's terminator; current flags there must be
    // dead.
    let ph_insert = preheader_insert_pos(func.blocks.get(&preheader)?);
    if !flags_dead_from(func, preheader, ph_insert, &mut HashSet::new(), 4) {
        sr_debug!(
            "x86-strength-reduce[debug] `{}` loop@{:?}: RFLAGS live at preheader {:?} insert",
            func.name,
            lp.header.0,
            preheader.0
        );
        return None;
    }

    // Side condition 2: match induction variables.
    let ivs = find_induction_variables(func, lp, def_sites, idom, preds);
    if ivs.is_empty() {
        sr_debug!(
            "x86-strength-reduce[debug] `{}` loop@{:?}: no induction variable matched",
            func.name,
            lp.header.0
        );
        return None;
    }
    sr_debug!(
        "x86-strength-reduce[debug] `{}` loop@{:?}: {} IV(s): {:?}",
        func.name,
        lp.header.0,
        ivs.len(),
        ivs.iter().map(|iv| (iv.iv.id, iv.step)).collect::<Vec<_>>()
    );
    let resolution = IvResolutionContext {
        func,
        lp,
        def_sites,
        idom,
        preds,
    };

    // Side condition 3: find the first multiply of an IV by a constant
    // stride (deterministic scan in block order).
    for &block_id in &func.block_order {
        if !lp.body.contains(&block_id) {
            continue;
        }
        let block = func.blocks.get(&block_id)?;
        for (idx, inst) in block.insts.iter().enumerate() {
            if debug_enabled() && matches!(inst.opcode, X86Opcode::ImulRR | X86Opcode::ImulRRI) {
                eprintln!(
                    "x86-strength-reduce[debug] `{}` loop@{:?}: imul at {:?}[{}]: {:?}",
                    func.name, lp.header.0, block_id.0, idx, inst.operands
                );
            }
            let Some((dst, iv, stride)) =
                match_candidate_mul(&resolution, inst, (block_id, idx), &ivs)
            else {
                continue;
            };
            // Side condition 5 (multiply point): the multiply's own flag
            // write disappears (mov writes no flags); its flags must be dead.
            if !flags_dead_from(func, block_id, idx + 1, &mut HashSet::new(), 4) {
                sr_debug!(
                    "x86-strength-reduce[debug]   -> rejected: RFLAGS live after imul {:?}[{}]",
                    block_id.0,
                    idx
                );
                continue;
            }
            // Side condition 4: definite initialization of the preheader
            // seed's IV read at the preheader.
            if !defined_at_preheader(func, iv.iv, &lp.body, preheader, idom) {
                sr_debug!(
                    "x86-strength-reduce[debug]   -> rejected: iv v{} not definitely \
                     initialized at preheader {:?}",
                    iv.iv.id,
                    preheader.0
                );
                continue;
            }
            // SIB-legal scales are the OPT-7 address-fold's territory: an
            // `imul idx, {1,2,4,8}` feeding a load/store folds into a single
            // `mov (%base,%idx,scale)` operand (strictly better than a
            // recurrence + add), and reducing it here would destroy the
            // scale-def shape that fold matches. Leave them to the peephole;
            // a scale-1/2/4/8 multiply not feeding memory is cheap anyway.
            if matches!(stride, 1 | 2 | 4 | 8) {
                sr_debug!(
                    "x86-strength-reduce[debug]   -> skipped: SIB-legal stride {} (OPT-7 \
                     SIB fold territory)",
                    stride
                );
                continue;
            }
            // Immediate encodability (the encoder rejects imm outside the
            // sign-extended i32 range for ImulRRI/AddRI).
            let advance = stride.wrapping_mul(iv.step);
            if i32::try_from(stride).is_err() || i32::try_from(advance).is_err() {
                sr_debug!(
                    "x86-strength-reduce[debug]   -> rejected: stride {} / advance {} \
                     outside imm32",
                    stride,
                    advance
                );
                continue;
            }
            // Side condition 6: the per-(width, step, stride) algebraic
            // obligation must be discharged. Gpr64 carriers only in v1.
            if !admit(64, iv.step, stride) {
                if log_enabled() {
                    eprintln!(
                        "x86-strength-reduce: obligation (width 64, step {}, stride {}) NOT \
                         discharged; leaving multiply in place in `{}`",
                        iv.step, stride, func.name
                    );
                }
                continue;
            }
            return Some(Candidate {
                iv,
                stride,
                mul_block: block_id,
                mul_idx: idx,
                dst,
                preheader,
            });
        }
    }
    None
}

/// Match `inst` as `ImulRR [d, x, y]` (one operand resolving to an IV via
/// [`resolve_iv_operand`], the other to a [`canon_const`] constant) or
/// `ImulRRI [d, x, imm]` (`x` resolving to an IV), against one of the loop's
/// IVs. All register operands must be Gpr64 vregs. Returns
/// `(dst, iv, stride)`.
struct IvResolutionContext<'a> {
    func: &'a X86ISelFunction,
    lp: &'a NaturalLoop,
    def_sites: &'a HashMap<VReg, Vec<(Block, usize)>>,
    idom: &'a HashMap<Block, Block>,
    preds: &'a HashMap<Block, Vec<Block>>,
}

fn match_candidate_mul(
    context: &IvResolutionContext<'_>,
    inst: &X86ISelInst,
    inst_pos: (Block, usize),
    ivs: &[IvMatch],
) -> Option<(VReg, IvMatch, i64)> {
    let func = context.func;
    if inst.proof_origin.is_some() {
        return None;
    }
    match inst.opcode {
        X86Opcode::ImulRR => {
            if inst.flags != X86Opcode::ImulRR.default_flags() {
                return None;
            }
            let [
                X86ISelOperand::VReg(d),
                X86ISelOperand::VReg(x),
                X86ISelOperand::VReg(y),
            ] = inst.operands.as_slice()
            else {
                return None;
            };
            if !all_gpr64(&[*d, *x, *y]) {
                return None;
            }
            for iv in ivs {
                // The multiply must not redefine the IV (it cannot — the IV
                // has exactly one body def, the update — but keep the
                // invariant local).
                if *d == iv.iv {
                    continue;
                }
                for (iv_op, const_op) in [(*x, *y), (*y, *x)] {
                    if !resolve_iv_operand(context, iv_op, inst_pos, iv) {
                        continue;
                    }
                    let Some(value) =
                        canon_const(func, const_op, context.def_sites, MAX_CHAIN_DEPTH)
                    else {
                        sr_debug!(
                            "x86-strength-reduce[debug]   -> operand v{} resolves to iv v{} \
                             but v{} is not a provable constant",
                            iv_op.id,
                            iv.iv.id,
                            const_op.id
                        );
                        continue;
                    };
                    return Some((*d, *iv, value));
                }
            }
            None
        }
        X86Opcode::ImulRRI => {
            if inst.flags != X86Opcode::ImulRRI.default_flags() {
                return None;
            }
            let [
                X86ISelOperand::VReg(d),
                X86ISelOperand::VReg(x),
                X86ISelOperand::Imm(k),
            ] = inst.operands.as_slice()
            else {
                return None;
            };
            if !all_gpr64(&[*d, *x]) {
                return None;
            }
            for iv in ivs {
                if *d != iv.iv && resolve_iv_operand(context, *x, inst_pos, iv) {
                    return Some((*d, *iv, *k));
                }
            }
            None
        }
        _ => None,
    }
}

fn all_gpr64(vregs: &[VReg]) -> bool {
    vregs.iter().all(|v| v.class == RegClass::Gpr64)
}

// ===========================================================================
// Value canonicalization
// ===========================================================================

/// Resolve `v`, read at `use_site` inside loop `lp`, to the CURRENT value of
/// the induction variable `iv` — the IV carrier itself, a chain of
/// single-def `MovRR` copies rooted at it, or a chain rooted at a multi-def
/// pass-through block param (module doc, "Pass-through block params"; the
/// walk itself lives in [`resolve_value_at`]).
///
/// # Why chains are needed
///
/// Phi-eliminated ISel output renames every use through fresh single-def
/// `MovRR` copies (`vK = mov k` in the loop body, then `t = add vK, one`),
/// so requiring the multiply/increment to read the IV carrier directly
/// almost never fires on real code.
///
/// # Soundness (why the chain value equals `iv` at the use)
///
/// For the DIRECT case (`v == iv`) the read trivially yields the IV's
/// current value; the `r == iv*s` invariant holds at every point outside
/// the update/advance pair, so no position constraint is needed.
///
/// For a CHAIN `v = mov v1; v1 = mov v2; ...; vn = mov iv` (each link
/// single-def, whole function) the copies hold a SNAPSHOT of `iv`, so we
/// must prove the snapshot cannot be STALE (taken before the last IV
/// update). The conditions, per link (reader at `(rb, ri)` reading a copy
/// defined at `(db, di)`):
///
///   1. `(db, di)` is inside the loop body — a copy outside the body holds
///      the loop-ENTRY value, stale after the first update;
///   2. `db != update_block` — no chain copy in the latch;
///   3. `db` strictly dominates `rb`, or `db == rb && di < ri`;
///
/// plus, for the chain as a whole:
///
///   4. the update block is a LATCH: its ONLY successor is the loop header
///      (checked during IV recognition — see [`find_induction_variables`]);
///   5. the FINAL use is not after the update in the latch
///      (`rb != update_block || ri < update_idx`).
///
/// Claim: at the final use, `v == iv`. The only definition of `iv` in the
/// body is the update (single-def side condition). Consider the last
/// executions of each chain copy before the use. If the update executed
/// after chain copy `C` (at `db`) but before the use, control passed
/// through the latch and — by (4) — continued to the HEADER. Any path from
/// the header back to the reader's block `rb` passes `db` again: `db`
/// dominates `rb` (3), the loop has no side entries, and the first entry
/// into the loop runs through the preheader, so a header-to-`rb` path
/// avoiding `db` extended by an entry path `entry -> preheader -> header`
/// (which avoids `db`: `db` is a BODY block, and the natural-loop body is
/// unreachable before the header on any entry path) would contradict
/// dominance. Re-passing `db` re-executes `C` AFTER the update —
/// contradicting "last execution". Within the resulting straight-line
/// window (all copies ordered by (3), no header re-entry), the only
/// possible `iv` definition is the update itself, excluded from the window
/// by (2) and (5). So every chain copy transports the CURRENT `iv` value to
/// the use.
fn resolve_iv_operand(
    context: &IvResolutionContext<'_>,
    v: VReg,
    use_site: (Block, usize),
    iv: &IvMatch,
) -> bool {
    if v == iv.iv {
        return true;
    }
    // Chain/param case: condition 5 — no stale reads at/after the update in
    // the latch.
    if use_site.0 == iv.update_block && use_site.1 >= iv.update_idx {
        return false;
    }
    let mut param_stack: Vec<VReg> = Vec::new();
    resolve_value_at(context, v, use_site, iv, &mut param_stack, MAX_CHAIN_DEPTH)
}

/// Resolve `v`, read at `reader` (a site inside the body that is NOT
/// at/after the IV update in the latch), to the CURRENT value of the IV:
/// the IV carrier itself, a chain of single-def `MovRR` copies rooted at it
/// (per-link conditions in [`resolve_iv_operand`]'s doc), or a chain rooted
/// at a multi-def pass-through block param (module doc, "Pass-through block
/// params"; conditions in [`resolve_passthrough_param`]).
///
/// `param_stack` holds the params whose defs are currently being validated
/// up-stack: a chain rooting at the INNERMOST such param (the stack top) is
/// the pass-through-def shape — the def rewrites the param with its own
/// transported value — and is accepted iff the root read is must-covered by
/// the param's defs (P2). Rooting at a param DEEPER in the stack would be a
/// mutual param cycle; edge-split phi elimination never emits one, and it
/// is conservatively rejected.
fn resolve_value_at(
    context: &IvResolutionContext<'_>,
    v: VReg,
    reader: (Block, usize),
    iv: &IvMatch,
    param_stack: &mut Vec<VReg>,
    depth: u32,
) -> bool {
    let func = context.func;
    let lp = context.lp;
    let def_sites = context.def_sites;
    let idom = context.idom;
    let preds = context.preds;
    let mut reader = reader;
    let mut cur = v;
    // Inclusive bound: the root test at the loop top runs once more than the
    // link walk, so a chain of exactly MAX_CHAIN_DEPTH links still resolves
    // (parity with the pre-extension walk, whose root test sat at the link).
    for _ in 0..=MAX_CHAIN_DEPTH {
        if cur == iv.iv {
            return true;
        }
        if param_stack.last() == Some(&cur) {
            // Pass-through root: the def under validation rewrites the param
            // with the param's own value at this read; sound iff the read is
            // must-covered (module-doc proof, pass-through-def case).
            return param_defs_cover_read(func, cur, lp, def_sites, preds, reader);
        }
        if param_stack.contains(&cur) {
            // Mutual param cycle: reject (fail-safe).
            return false;
        }
        let Some((db, di)) = single_def_site(def_sites, cur) else {
            // Multi-def vreg: admissible only as a pass-through block param.
            return resolve_passthrough_param(context, cur, reader, iv, param_stack, depth);
        };
        // Condition 1: inside the body.
        if !lp.body.contains(&db) {
            return false;
        }
        // Condition 2: not in the latch.
        if db == iv.update_block {
            return false;
        }
        // Condition 3: dominates the reader (same-block: earlier index).
        if db == reader.0 {
            if di >= reader.1 {
                return false;
            }
        } else if !dominates(db, reader.0, idom) {
            return false;
        }
        // The link must be a plain Gpr64 register copy.
        let Some(block) = func.blocks.get(&db) else {
            return false;
        };
        let inst = &block.insts[di];
        if inst.opcode != X86Opcode::MovRR || inst.flags != X86Opcode::MovRR.default_flags() {
            return false;
        }
        let [X86ISelOperand::VReg(dst), X86ISelOperand::VReg(src)] = inst.operands.as_slice()
        else {
            return false;
        };
        if *dst != cur || !all_gpr64(&[*src]) {
            return false;
        }
        reader = (db, di);
        cur = *src;
    }
    false
}

/// Canonicalize the MULTI-DEF vreg `p`, read at `read_site`, as a
/// PASS-THROUGH block param holding the IV's current value (module doc,
/// conditions P1–P3). Fail-safe: any def that is not provably a copy of the
/// same canonical source rejects the whole param.
fn resolve_passthrough_param(
    context: &IvResolutionContext<'_>,
    p: VReg,
    read_site: (Block, usize),
    iv: &IvMatch,
    param_stack: &mut Vec<VReg>,
    depth: u32,
) -> bool {
    let func = context.func;
    let lp = context.lp;
    let def_sites = context.def_sites;
    let preds = context.preds;
    if depth == 0 || param_stack.contains(&p) {
        return false;
    }
    let Some(defs) = def_sites.get(&p) else {
        return false;
    };
    // Single-def vregs are the chain walk's territory; an undefined vreg has
    // nothing to canonicalize.
    if defs.len() < 2 {
        return false;
    }
    // P1: every def is a plain Gpr64 `MovRR [p, src]` inside the loop body,
    // outside the latch.
    let mut srcs: Vec<(Block, usize, VReg)> = Vec::with_capacity(defs.len());
    for &(db, di) in defs {
        if !lp.body.contains(&db) || db == iv.update_block {
            sr_debug!(
                "x86-strength-reduce[debug]   -> param v{} def at {:?}[{}] outside \
                 body/in latch",
                p.id,
                db.0,
                di
            );
            return false;
        }
        let Some(block) = func.blocks.get(&db) else {
            return false;
        };
        let inst = &block.insts[di];
        if inst.opcode != X86Opcode::MovRR || inst.flags != X86Opcode::MovRR.default_flags() {
            sr_debug!(
                "x86-strength-reduce[debug]   -> param v{} def at {:?}[{}] is not a plain \
                 MovRR copy",
                p.id,
                db.0,
                di
            );
            return false;
        }
        let [X86ISelOperand::VReg(dst), X86ISelOperand::VReg(src)] = inst.operands.as_slice()
        else {
            return false;
        };
        if *dst != p || !all_gpr64(&[*src]) {
            return false;
        }
        srcs.push((db, di, *src));
    }
    // P2: the read is must-covered by p's defs.
    if !param_defs_cover_read(func, p, lp, def_sites, preds, read_site) {
        sr_debug!(
            "x86-strength-reduce[debug]   -> param v{} read at {:?}[{}] not must-covered \
             by its defs",
            p.id,
            read_site.0.0,
            read_site.1
        );
        return false;
    }
    // P3: every def's source resolves at the def site to the IV's current
    // value or passes `p` itself through unchanged.
    param_stack.push(p);
    let ok = srcs
        .iter()
        .all(|&(db, di, src)| resolve_value_at(context, src, (db, di), iv, param_stack, depth - 1));
    param_stack.pop();
    if !ok {
        sr_debug!(
            "x86-strength-reduce[debug]   -> param v{}: a def's source does not resolve \
             to iv v{} / pass-through",
            p.id,
            iv.iv.id
        );
    }
    ok
}

/// Must-cover analysis for a pass-through-param read (condition P2): is
/// EVERY path from the loop-header start to `read_site` guaranteed to
/// execute a definition of `p`?
///
/// Coverage restarts at the header (`in(header) = false`): the latch's only
/// successor is the header, so any execution of the IV update forces a
/// header re-entry before control can reach a body read again, and a def of
/// `p` re-executed after that re-entry (which coverage guarantees) rewrites
/// `p` with a fresh copy — no admitted read observes a value staled by the
/// update. Loop-entry paths are covered by the same forced `false`: the
/// first header execution precedes every body read (natural-loop bodies are
/// unreachable before the header), so entry reads also see a preceding def.
///
/// Boolean AND-meet greatest-fixpoint dataflow over the body blocks, in
/// deterministic `block_order`. Non-body predecessors (impossible after the
/// no-side-entry check, except the preheader edge into the header, whose
/// in-state is forced anyway) and predecessor-less blocks are conservatively
/// uncovered.
fn param_defs_cover_read(
    func: &X86ISelFunction,
    p: VReg,
    lp: &NaturalLoop,
    def_sites: &HashMap<VReg, Vec<(Block, usize)>>,
    preds: &HashMap<Block, Vec<Block>>,
    read_site: (Block, usize),
) -> bool {
    let no_defs: Vec<(Block, usize)> = Vec::new();
    let defs = def_sites.get(&p).unwrap_or(&no_defs);
    // A def earlier in the read's own block covers the read directly: the
    // window from that def to the read is straight-line and cannot contain
    // the IV update (reads at/after the update in the latch are rejected
    // upstream, and defs never sit in the latch per P1).
    if defs
        .iter()
        .any(|&(b, i)| b == read_site.0 && i < read_site.1)
    {
        return true;
    }
    let def_blocks: HashSet<Block> = defs.iter().map(|&(b, _)| b).collect();
    let empty: Vec<Block> = Vec::new();
    let covered_in = |b: Block, covered_out: &HashMap<Block, bool>| -> bool {
        if b == lp.header {
            return false;
        }
        let block_preds = preds.get(&b).unwrap_or(&empty);
        !block_preds.is_empty()
            && block_preds
                .iter()
                .all(|pr| lp.body.contains(pr) && covered_out.get(pr).copied().unwrap_or(false))
    };
    let mut covered_out: HashMap<Block, bool> = lp.body.iter().map(|b| (*b, true)).collect();
    let mut changed = true;
    while changed {
        changed = false;
        for block_id in &func.block_order {
            if !lp.body.contains(block_id) {
                continue;
            }
            let new_out = def_blocks.contains(block_id) || covered_in(*block_id, &covered_out);
            if covered_out.get(block_id) != Some(&new_out) {
                covered_out.insert(*block_id, new_out);
                changed = true;
            }
        }
    }
    // No in-block def before the read: covered iff every path into the
    // read's block is.
    covered_in(read_site.0, &covered_out)
}

/// The compile-time constant value of `v`: `v` (and every vreg in its copy
/// chain) is defined exactly once in the whole function, each link a plain
/// `MovRR`, rooted at a single-def `MovRI` immediate.
///
/// No position/dominance conditions are needed: a single-def vreg has ONE
/// static value assignment, so wherever the original code read it as a
/// defined value, that value is the chased constant. The rewrite
/// re-materializes the constant as an immediate and never reads the chain
/// at any new position, so definite-initialization is preserved trivially.
fn canon_const(
    func: &X86ISelFunction,
    v: VReg,
    def_sites: &HashMap<VReg, Vec<(Block, usize)>>,
    depth: u32,
) -> Option<i64> {
    if depth == 0 {
        return None;
    }
    let (db, di) = single_def_site(def_sites, v)?;
    let inst = &func.blocks.get(&db)?.insts[di];
    match inst.opcode {
        X86Opcode::MovRI => match inst.operands.as_slice() {
            [X86ISelOperand::VReg(d), X86ISelOperand::Imm(imm)] if *d == v => Some(*imm),
            _ => None,
        },
        X86Opcode::MovRR => {
            if inst.flags != X86Opcode::MovRR.default_flags() {
                return None;
            }
            match inst.operands.as_slice() {
                [X86ISelOperand::VReg(d), X86ISelOperand::VReg(src)]
                    if *d == v && all_gpr64(&[*src]) =>
                {
                    canon_const(func, *src, def_sites, depth - 1)
                }
                _ => None,
            }
        }
        _ => None,
    }
}

// ===========================================================================
// Induction-variable recognition
// ===========================================================================

fn find_induction_variables(
    func: &X86ISelFunction,
    lp: &NaturalLoop,
    def_sites: &HashMap<VReg, Vec<(Block, usize)>>,
    idom: &HashMap<Block, Block>,
    preds: &HashMap<Block, Vec<Block>>,
) -> Vec<IvMatch> {
    let mut ivs = Vec::new();
    // Deterministic: iterate defs in block order.
    for &block_id in &func.block_order {
        if !lp.body.contains(&block_id) {
            continue;
        }
        let Some(block) = func.blocks.get(&block_id) else {
            continue;
        };
        for (idx, inst) in block.insts.iter().enumerate() {
            let Some(iv) = match_iv_update(func, inst, (block_id, idx), lp, def_sites, idom, preds)
            else {
                continue;
            };
            // The update block must be a latch: its only successor is the
            // loop header. This is load-bearing for the copy-chain windows
            // (see `resolve_iv_operand`, condition 4).
            match block.successors.as_slice() {
                [succ] if *succ == lp.header => {}
                _ => continue,
            }
            // This must be the vreg's ONLY in-body definition.
            let mut body_defs = def_sites
                .get(&iv.0)
                .map(|s| s.as_slice())
                .unwrap_or(&[])
                .iter()
                .filter(|(b, _)| lp.body.contains(b));
            if body_defs.next() != Some(&(block_id, idx)) || body_defs.next().is_some() {
                continue;
            }
            // The recurrence advance (a flag writer) goes immediately after
            // the update; the flags there must be dead (side condition 5).
            if !flags_dead_from(func, block_id, idx + 1, &mut HashSet::new(), 4) {
                continue;
            }
            ivs.push(IvMatch {
                iv: iv.0,
                step: iv.1,
                update_block: block_id,
                update_idx: idx,
            });
        }
    }
    ivs
}

/// Match one in-body IV-update shape; returns `(iv, step)`.
///
///   * writeback `MovRR [iv, t]`, `t` single-def in the whole function and
///     defined inside the body by `AddRR [t, iv', c]` (`iv'` resolving to
///     the IV via [`resolve_iv_operand`], `c` a [`canon_const`] constant,
///     either operand order) or `AddRI [t, iv', imm]`. The increment must
///     sit in the SAME block as (and before) the writeback: this makes the
///     two execute 1:1 in lockstep — a writeback re-executing without a
///     fresh increment (e.g. an edge copy inside a nested loop) would
///     advance the recurrence without advancing the IV;
///   * tied `AddRI [iv, imm]` (two-operand form), which is increment and
///     writeback in one instruction.
fn match_iv_update(
    func: &X86ISelFunction,
    inst: &X86ISelInst,
    inst_pos: (Block, usize),
    lp: &NaturalLoop,
    def_sites: &HashMap<VReg, Vec<(Block, usize)>>,
    idom: &HashMap<Block, Block>,
    preds: &HashMap<Block, Vec<Block>>,
) -> Option<(VReg, i64)> {
    match inst.opcode {
        X86Opcode::MovRR => {
            if inst.flags != X86Opcode::MovRR.default_flags() {
                return None;
            }
            let [X86ISelOperand::VReg(iv), X86ISelOperand::VReg(t)] = inst.operands.as_slice()
            else {
                return None;
            };
            if !all_gpr64(&[*iv, *t]) || iv == t {
                return None;
            }
            // `t` is a pure single-def temporary defined inside the body.
            let (t_block, t_idx) = single_def_site(def_sites, *t)?;
            if !lp.body.contains(&t_block) {
                return None;
            }
            // Lockstep guard: increment in the same block, before the
            // writeback.
            if t_block != inst_pos.0 || t_idx >= inst_pos.1 {
                return None;
            }
            let t_def = &func.blocks.get(&t_block)?.insts[t_idx];
            let resolution = IvResolutionContext {
                func,
                lp,
                def_sites,
                idom,
                preds,
            };
            let step = match_increment_of(&resolution, t_def, (t_block, t_idx), *t, *iv, inst_pos)?;
            Some((*iv, step))
        }
        X86Opcode::AddRI => {
            if inst.flags != X86Opcode::AddRI.default_flags() {
                return None;
            }
            // Tied two-operand form only: `add iv, imm`.
            let [X86ISelOperand::VReg(iv), X86ISelOperand::Imm(step)] = inst.operands.as_slice()
            else {
                return None;
            };
            if !all_gpr64(&[*iv]) {
                return None;
            }
            Some((*iv, *step))
        }
        _ => None,
    }
}

/// Match `t_def` as `t = iv + <constant>`: `AddRR [t, iv', c]`/`AddRR [t, c,
/// iv']` (with `iv'` resolving to the IV via the copy-chain rules and `c` a
/// [`canon_const`] constant) or `AddRI [t, iv', imm]` (three-address).
/// Returns the constant step.
///
/// `wb_pos` is the position of the writeback (`mov iv, t`) this increment
/// feeds; the copy-chain resolution uses it as the IV update site.
fn match_increment_of(
    context: &IvResolutionContext<'_>,
    t_def: &X86ISelInst,
    t_pos: (Block, usize),
    t: VReg,
    iv: VReg,
    wb_pos: (Block, usize),
) -> Option<i64> {
    let func = context.func;
    // Provisional IvMatch for the chain resolution: the update is the
    // writeback this increment feeds (`step` is what we are determining; the
    // chain rules never read it).
    let prov = IvMatch {
        iv,
        step: 0,
        update_block: wb_pos.0,
        update_idx: wb_pos.1,
    };
    match t_def.opcode {
        X86Opcode::AddRR => {
            if t_def.flags != X86Opcode::AddRR.default_flags() {
                return None;
            }
            let [
                X86ISelOperand::VReg(d),
                X86ISelOperand::VReg(x),
                X86ISelOperand::VReg(y),
            ] = t_def.operands.as_slice()
            else {
                return None;
            };
            if *d != t || !all_gpr64(&[*x, *y]) {
                return None;
            }
            for (iv_op, const_op) in [(*x, *y), (*y, *x)] {
                if resolve_iv_operand(context, iv_op, t_pos, &prov)
                    && let Some(step) =
                        canon_const(func, const_op, context.def_sites, MAX_CHAIN_DEPTH)
                {
                    return Some(step);
                }
            }
            None
        }
        X86Opcode::AddRI => {
            if t_def.flags != X86Opcode::AddRI.default_flags() {
                return None;
            }
            let [
                X86ISelOperand::VReg(d),
                X86ISelOperand::VReg(src),
                X86ISelOperand::Imm(step),
            ] = t_def.operands.as_slice()
            else {
                return None;
            };
            if *d != t || !all_gpr64(&[*src]) {
                return None;
            }
            if !resolve_iv_operand(context, *src, t_pos, &prov) {
                return None;
            }
            Some(*step)
        }
        _ => None,
    }
}

// ===========================================================================
// Definite initialization at the preheader
// ===========================================================================

/// True iff `v` has a definition outside the loop body located in the
/// preheader itself or in a block dominating the preheader — so a read of
/// `v` appended at the end of the preheader is definitely initialized.
fn defined_at_preheader(
    func: &X86ISelFunction,
    v: VReg,
    body: &HashSet<Block>,
    preheader: Block,
    idom: &HashMap<Block, Block>,
) -> bool {
    for block_id in &func.block_order {
        if body.contains(block_id) {
            continue;
        }
        let Some(block) = func.blocks.get(block_id) else {
            continue;
        };
        for inst in &block.insts {
            // Same carrier exclusion as `defined_vreg`: a proof-only guard
            // carrier never writes its operand, so it must not be credited as
            // a definite init at/above the preheader.
            if x86_produces_value(inst.opcode)
                && trust_cg_ir::guard_target::classify_x86_carrier(inst.opcode).is_none()
                && matches!(inst.operands.first(), Some(X86ISelOperand::VReg(d)) if *d == v)
                && (*block_id == preheader || dominates(*block_id, preheader, idom))
            {
                return true;
            }
        }
    }
    false
}

// ===========================================================================
// RFLAGS deadness
// ===========================================================================

/// Are the RFLAGS at position `(block, start_idx)` dead — i.e. is a FULL flag
/// overwrite reached before any flag reader, call, return, or flag-reading
/// terminator, following unconditional single-successor control flow through
/// at most `depth` blocks?
///
/// This is the cross-block generalization of the SIB fold's
/// `sib_fold_flags_dead`: inserting a flag WRITER at a point requires the
/// same condition as deleting one — the flags state at that point must be
/// dead. `Jmp` neither reads nor writes flags, so it is safe to traverse; a
/// `Jcc` reads flags and refuses; falling off a block with anything but
/// exactly one successor refuses (conservative).
fn flags_dead_from(
    func: &X86ISelFunction,
    block_id: Block,
    start_idx: usize,
    visited: &mut HashSet<Block>,
    depth: u32,
) -> bool {
    if depth == 0 || !visited.insert(block_id) {
        return false;
    }
    let Some(block) = func.blocks.get(&block_id) else {
        return false;
    };
    for inst in block.insts.iter().skip(start_idx) {
        if x86_reads_flags(inst.opcode) {
            return false;
        }
        let flags = inst.flags;
        if flags.is_call() || flags.is_return() {
            return false;
        }
        match condition_flag_overwrite(inst) {
            FlagOverwrite::Full => return true,
            FlagOverwrite::Partial => return false,
            FlagOverwrite::None => {}
        }
        if flags.is_branch() || flags.is_terminator() {
            // A non-flag-reading, non-flag-writing branch: only `Jmp` (and
            // Jcc/Ret are rejected above). Follow the unique successor.
            break;
        }
    }
    match block.successors.as_slice() {
        [succ] => flags_dead_from(func, *succ, 0, visited, depth - 1),
        _ => false,
    }
}

// ===========================================================================
// Rewrite
// ===========================================================================

fn apply_candidate(func: &mut X86ISelFunction, candidate: &Candidate) {
    let iv = candidate.iv;
    let dst = candidate.dst;

    // Fresh recurrence carrier, mirroring the multiply dst's nominal width.
    let r = new_gpr64_vreg(func);
    if let Some(w) = func.vreg_nominal_widths.get(&dst).copied() {
        func.vreg_nominal_widths.insert(r, w);
    }

    // Preheader seed `r = iv * stride` (constant stride as an immediate) and
    // latch advance `r = r + stride*step`.
    let seed = X86ISelInst::new(
        X86Opcode::ImulRRI,
        vec![
            X86ISelOperand::VReg(r),
            X86ISelOperand::VReg(iv.iv),
            X86ISelOperand::Imm(candidate.stride),
        ],
    );
    let advance = X86ISelInst::new(
        X86Opcode::AddRI,
        vec![
            X86ISelOperand::VReg(r),
            X86ISelOperand::VReg(r),
            X86ISelOperand::Imm(candidate.stride.wrapping_mul(iv.step)),
        ],
    );

    if log_enabled() {
        eprintln!(
            "x86-strength-reduce: fired in `{}`: imul at #{:?}[{}] (iv v{}, step {}, stride \
             {}) -> recurrence v{}",
            func.name,
            candidate.mul_block.0,
            candidate.mul_idx,
            iv.iv.id,
            iv.step,
            candidate.stride,
            r.id,
        );
    }

    // 1. Replace the multiply in place with `mov dst, r` (keeps the
    //    instruction's lowering provenance; index-stable).
    {
        let block = func
            .blocks
            .get_mut(&candidate.mul_block)
            .expect("candidate block exists");
        let inst = &mut block.insts[candidate.mul_idx];
        inst.opcode = X86Opcode::MovRR;
        inst.flags = X86Opcode::MovRR.default_flags();
        inst.operands = vec![X86ISelOperand::VReg(dst), X86ISelOperand::VReg(r)];
    }

    // 2. Insert the advance immediately after the IV update. The multiply
    //    replacement above was done by index first, so this insertion cannot
    //    invalidate it.
    {
        let block = func
            .blocks
            .get_mut(&iv.update_block)
            .expect("update block exists");
        block.insts.insert(iv.update_idx + 1, advance);
    }

    // 3. Splice the seed into the preheader before its terminator. The
    //    preheader is never the update block (it is outside the loop body),
    //    so the advance insertion above cannot shift this position.
    {
        let ph = func
            .blocks
            .get_mut(&candidate.preheader)
            .expect("preheader exists");
        let pos = preheader_insert_pos(ph);
        ph.insts.insert(pos, seed);
    }
}

fn new_gpr64_vreg(func: &mut X86ISelFunction) -> VReg {
    let id = func.next_vreg;
    func.next_vreg += 1;
    VReg::new(id, RegClass::Gpr64)
}

/// Splice point in the preheader: immediately before the trailing
/// terminator, if any (mirrors `x86_licm::preheader_insert_pos`).
fn preheader_insert_pos(block: &trust_cg_lower::X86ISelBlock) -> usize {
    match block.insts.last() {
        Some(last) if last.flags.is_terminator() || last.flags.is_branch() => block.insts.len() - 1,
        _ => block.insts.len(),
    }
}

// ===========================================================================
// Def maps
// ===========================================================================

/// Every definition site of every vreg, whole function, in block order.
fn build_def_sites(func: &X86ISelFunction) -> HashMap<VReg, Vec<(Block, usize)>> {
    let mut sites: HashMap<VReg, Vec<(Block, usize)>> = HashMap::new();
    for block_id in &func.block_order {
        let Some(block) = func.blocks.get(block_id) else {
            continue;
        };
        for (idx, inst) in block.insts.iter().enumerate() {
            if let Some(def) = defined_vreg(inst) {
                sites.entry(def).or_default().push((*block_id, idx));
            }
        }
    }
    sites
}

/// The unique whole-function definition site of `v`, if it has exactly one.
fn single_def_site(
    def_sites: &HashMap<VReg, Vec<(Block, usize)>>,
    v: VReg,
) -> Option<(Block, usize)> {
    match def_sites.get(&v)?.as_slice() {
        &[site] => Some(site),
        _ => None,
    }
}

fn defined_vreg(inst: &X86ISelInst) -> Option<VReg> {
    if !x86_produces_value(inst.opcode) {
        return None;
    }
    // Proof-only guard carriers (TrapBoundsCheckExact etc.) carry the checked
    // vreg in operand[0] but NEVER write a register (the post-pipeline
    // expansion emits only a compare + branch — fail-closed, canary-gated).
    // Counting them as defs makes every bounds-checked index copy look
    // multi-def, which blocked the IV chain rule on exactly the hot loops
    // that carry checks. Excluded here (pass-local; the global
    // x86_produces_value stays untouched because the Certified-Elimination
    // Kernel's operand fingerprinting depends on it).
    if trust_cg_ir::guard_target::classify_x86_carrier(inst.opcode).is_some() {
        return None;
    }
    match inst.operands.first() {
        Some(X86ISelOperand::VReg(v)) => Some(*v),
        _ => None,
    }
}

// ===========================================================================
// CFG / dominators / natural loops — shared arch-neutral implementations
// from `crate::mach_view` (predecessor map, RPO, Cooper/Harvey/Kennedy idom,
// natural-loop discovery, written once for both machine-IR universes and
// already consumed default-ON by the x86 layout passes). The thin wrappers
// below keep this pass's original signatures; the only pass-local piece is
// the `NaturalLoop` cache struct, which keeps exactly the fields this pass
// consumes. `GenericLoop::latches` is dropped on conversion: the pass never
// reads a latch list — side condition 2 derives the update/latch block
// itself, by requiring the IV update block's only successor to be the loop
// header.
// ===========================================================================

/// A natural loop on the x86 ISel CFG (filled from
/// [`mach_view::GenericLoop`]).
struct NaturalLoop {
    header: Block,
    body: HashSet<Block>,
    /// Unique non-loop predecessor of the header, if one exists.
    preheader: Option<Block>,
    /// Nesting depth (outermost = 1); larger = more deeply nested.
    depth: u32,
}

fn build_predecessor_map(func: &X86ISelFunction) -> HashMap<Block, Vec<Block>> {
    mach_view::predecessor_map(func)
}

/// Immediate dominators via Cooper/Harvey/Kennedy, keyed by block. Entry maps
/// to itself. Shared implementation: [`mach_view::compute_idom`] over
/// [`mach_view::compute_rpo`].
fn compute_idom(
    func: &X86ISelFunction,
    preds: &HashMap<Block, Vec<Block>>,
) -> HashMap<Block, Block> {
    let rpo = mach_view::compute_rpo(func);
    mach_view::compute_idom(func, preds, &rpo)
}

/// `a` dominates `b` (reflexive). Shared implementation:
/// [`mach_view::dominates`].
fn dominates(a: Block, b: Block, idom: &HashMap<Block, Block>) -> bool {
    mach_view::dominates(a, b, idom)
}

/// Identify natural loops by back-edges (latch -> header where header
/// dominates latch); merge multiple back-edges into one loop per header.
/// Shared implementation: [`mach_view::find_natural_loops`]. Results arrive
/// sorted by header block index; the sole caller re-sorts by
/// `(Reverse(depth), header.0)` — a total key, headers being unique per
/// merged loop — so the pre-sort order cannot influence pass behavior.
fn find_natural_loops(
    func: &X86ISelFunction,
    preds: &HashMap<Block, Vec<Block>>,
    idom: &HashMap<Block, Block>,
) -> Vec<NaturalLoop> {
    mach_view::find_natural_loops(func, preds, idom)
        .into_iter()
        .map(|lp| NaturalLoop {
            header: lp.header,
            body: lp.body,
            preheader: lp.preheader,
            depth: lp.depth,
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    use std::sync::Mutex;
    use std::sync::atomic::{AtomicI64, Ordering};

    use trust_cg_ir::X86CondCode;
    use trust_cg_lower::function::Signature;
    use trust_cg_lower::types::Type;

    fn vreg(id: u32) -> X86ISelOperand {
        X86ISelOperand::VReg(VReg::new(id, RegClass::Gpr64))
    }
    fn vr(id: u32) -> VReg {
        VReg::new(id, RegClass::Gpr64)
    }
    fn imm(v: i64) -> X86ISelOperand {
        X86ISelOperand::Imm(v)
    }

    fn admit_all(_width: u32, _step: i64, _stride: i64) -> bool {
        true
    }
    fn admit_none(_width: u32, _step: i64, _stride: i64) -> bool {
        false
    }

    static LAST_ADMIT_STEP: AtomicI64 = AtomicI64::new(i64::MIN);
    static LAST_ADMIT_STRIDE: AtomicI64 = AtomicI64::new(i64::MIN);
    static ADMIT_RECORDING_LOCK: Mutex<()> = Mutex::new(());
    fn admit_recording(width: u32, step: i64, stride: i64) -> bool {
        assert_eq!(width, 64, "v1 admits Gpr64 carriers only");
        LAST_ADMIT_STEP.store(step, Ordering::SeqCst);
        LAST_ADMIT_STRIDE.store(stride, Ordering::SeqCst);
        true
    }

    /// The canonical post-ISel/post-LICM while-loop shape:
    ///
    /// ```text
    ///   bb0 (preheader): v0=0; v1=mov v0 (iv); v2=24 (stride); v3=1; jmp bb1
    ///   bb1 (header)   : cmp v1, 100; jcc AE bb3
    ///   bb2 (body/latch): v4 = imul v1, v2      ; candidate
    ///                     v5 = mov v4           ; a flag-free use
    ///                     v6 = add v1, v3       ; t = iv + 1
    ///                     v1 = mov v6           ; writeback
    ///                     jmp bb1
    ///   bb3 (exit)     : ret
    /// ```
    fn make_canonical_loop() -> X86ISelFunction {
        let sig = Signature {
            params: vec![],
            returns: vec![Type::I64],
        };
        let mut func = X86ISelFunction::new("sr_test".to_string(), sig);
        let (bb0, bb1, bb2, bb3) = (Block(0), Block(1), Block(2), Block(3));
        for b in [bb0, bb1, bb2, bb3] {
            func.ensure_block(b);
        }
        func.next_vreg = 64;

        func.blocks.get_mut(&bb0).unwrap().successors = vec![bb1];
        func.push_inst(
            bb0,
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(0), imm(0)]),
        );
        func.push_inst(
            bb0,
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(1), vreg(0)]),
        );
        func.push_inst(
            bb0,
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(2), imm(24)]),
        );
        func.push_inst(
            bb0,
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(3), imm(1)]),
        );
        func.push_inst(
            bb0,
            X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(bb1)]),
        );

        func.blocks.get_mut(&bb1).unwrap().successors = vec![bb2, bb3];
        func.push_inst(
            bb1,
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(1), imm(100)]),
        );
        func.push_inst(
            bb1,
            X86ISelInst::new(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::AE),
                    X86ISelOperand::Block(bb3),
                ],
            ),
        );

        func.blocks.get_mut(&bb2).unwrap().successors = vec![bb1];
        func.push_inst(
            bb2,
            X86ISelInst::new(X86Opcode::ImulRR, vec![vreg(4), vreg(1), vreg(2)]),
        );
        func.push_inst(
            bb2,
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(5), vreg(4)]),
        );
        func.push_inst(
            bb2,
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(6), vreg(1), vreg(3)]),
        );
        func.push_inst(
            bb2,
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(1), vreg(6)]),
        );
        func.push_inst(
            bb2,
            X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(bb1)]),
        );

        func.push_inst(bb3, X86ISelInst::new(X86Opcode::Ret, vec![]));

        func
    }

    fn insts(func: &X86ISelFunction, b: Block) -> &[X86ISelInst] {
        &func.blocks.get(&b).unwrap().insts
    }

    fn count_opcode(func: &X86ISelFunction, opcode: X86Opcode) -> usize {
        func.block_order
            .iter()
            .flat_map(|b| insts(func, *b))
            .filter(|i| i.opcode == opcode)
            .count()
    }

    #[test]
    fn reduces_canonical_iv_times_invariant_mul() {
        let mut func = make_canonical_loop();
        let r = vr(func.next_vreg);
        let mut pass = X86StrengthReduce::new(admit_all);
        assert!(
            pass.run_on_function(&mut func),
            "canonical loop must reduce"
        );

        // The loop-body multiply is replaced by `mov v4, r`.
        let body = insts(&func, Block(2));
        assert_eq!(body[0].opcode, X86Opcode::MovRR);
        assert_eq!(body[0].operands, vec![vreg(4), X86ISelOperand::VReg(r)]);

        // The preheader gains the seed `r = imul v1, 24` before its jmp.
        let ph = insts(&func, Block(0));
        assert_eq!(ph.len(), 6);
        assert_eq!(ph[4].opcode, X86Opcode::ImulRRI);
        assert_eq!(
            ph[4].operands,
            vec![X86ISelOperand::VReg(r), vreg(1), imm(24)]
        );
        assert_eq!(ph[5].opcode, X86Opcode::Jmp);

        // The advance `r = add r, 24` sits immediately after the writeback.
        assert_eq!(body[4].opcode, X86Opcode::AddRI);
        assert_eq!(
            body[4].operands,
            vec![X86ISelOperand::VReg(r), X86ISelOperand::VReg(r), imm(24)]
        );
        assert_eq!(body[5].opcode, X86Opcode::Jmp);

        // No multiply remains in the loop; the seed is the only one, in the
        // preheader. A second run is idempotent.
        assert_eq!(count_opcode(&func, X86Opcode::ImulRR), 0);
        assert_eq!(count_opcode(&func, X86Opcode::ImulRRI), 1);
        assert!(
            !pass.run_on_function(&mut func),
            "second run must be a no-op"
        );
    }

    #[test]
    fn admission_gate_refusal_leaves_multiply_in_place() {
        let mut func = make_canonical_loop();
        let mut pass = X86StrengthReduce::new(admit_none);
        assert!(
            !pass.run_on_function(&mut func),
            "an undischarged obligation must leave the loop unoptimized"
        );
        assert_eq!(insts(&func, Block(2))[0].opcode, X86Opcode::ImulRR);
        assert_eq!(count_opcode(&func, X86Opcode::ImulRR), 1);
    }

    #[test]
    fn admission_gate_receives_the_emitted_step_and_stride() {
        let _recording_guard = ADMIT_RECORDING_LOCK
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        let mut func = make_canonical_loop();
        // Make the increment step 3 via the three-address AddRI form.
        let body = &mut func.blocks.get_mut(&Block(2)).unwrap().insts;
        body[2] = X86ISelInst::new(X86Opcode::AddRI, vec![vreg(6), vreg(1), imm(3)]);
        LAST_ADMIT_STEP.store(i64::MIN, Ordering::SeqCst);
        LAST_ADMIT_STRIDE.store(i64::MIN, Ordering::SeqCst);
        let r = vr(func.next_vreg);
        let mut pass = X86StrengthReduce::new(admit_recording);
        assert!(pass.run_on_function(&mut func));
        assert_eq!(
            LAST_ADMIT_STEP.load(Ordering::SeqCst),
            3,
            "the admission gate must see the same step the rewrite uses"
        );
        assert_eq!(
            LAST_ADMIT_STRIDE.load(Ordering::SeqCst),
            24,
            "the admission gate must see the same stride the rewrite uses"
        );
        // Non-unit step: the advance immediate is stride*step = 72.
        let body = insts(&func, Block(2));
        assert_eq!(body[4].opcode, X86Opcode::AddRI);
        assert_eq!(
            body[4].operands,
            vec![X86ISelOperand::VReg(r), X86ISelOperand::VReg(r), imm(72)]
        );
    }

    #[test]
    fn reduces_tied_addri_iv_with_imm_stride_mul() {
        let mut func = make_canonical_loop();
        {
            let body = &mut func.blocks.get_mut(&Block(2)).unwrap().insts;
            // imul-by-immediate candidate + tied two-operand increment.
            body[0] = X86ISelInst::new(X86Opcode::ImulRRI, vec![vreg(4), vreg(1), imm(24)]);
            body[2] = X86ISelInst::new(X86Opcode::AddRI, vec![vreg(1), imm(1)]);
            // Drop the writeback (the tied add IS the update); keep the jmp.
            body.remove(3);
        }
        let r = vr(func.next_vreg);
        let mut pass = X86StrengthReduce::new(admit_all);
        assert!(pass.run_on_function(&mut func), "tied-AddRI IV must reduce");

        let body = insts(&func, Block(2));
        assert_eq!(body[0].opcode, X86Opcode::MovRR);
        assert_eq!(body[0].operands, vec![vreg(4), X86ISelOperand::VReg(r)]);
        // Advance: r = add r, 24*1 (immediate form), right after the tied add.
        assert_eq!(body[3].opcode, X86Opcode::AddRI);
        assert_eq!(
            body[3].operands,
            vec![X86ISelOperand::VReg(r), X86ISelOperand::VReg(r), imm(24)]
        );
        // Seed: r = imul v1, 24 in the preheader.
        let ph = insts(&func, Block(0));
        assert!(ph.iter().any(|i| i.opcode == X86Opcode::ImulRRI
            && i.operands == vec![X86ISelOperand::VReg(r), vreg(1), imm(24)]));
    }

    /// The load-bearing real-world shape (matmul k-loop): every use of the
    /// IV and of the stride flows through single-def `MovRR` renames in a
    /// body block that dominates both the multiply and the increment.
    ///
    /// ```text
    ///   bb0 (preheader): v0=0; v1=mov v0 (iv); v2=24; v3=1; jmp bb1
    ///   bb1 (header)   : cmp v1, 100; jcc AE bb4
    ///   bb2 (body)     : v10 = mov v1   ; iv rename
    ///                    v11 = mov v2   ; stride rename
    ///                    v12 = mov v10  ; second-level iv rename
    ///                    v4 = imul v12, v11
    ///                    v5 = mov v4
    ///                    jmp bb3
    ///   bb3 (latch)    : v6 = add v10, v3  ; increment reads the RENAME
    ///                    v1 = mov v6       ; writeback
    ///                    jmp bb1
    ///   bb4 (exit)     : ret
    /// ```
    fn make_copy_chain_loop() -> X86ISelFunction {
        let sig = Signature {
            params: vec![],
            returns: vec![Type::I64],
        };
        let mut func = X86ISelFunction::new("sr_chain".to_string(), sig);
        let (bb0, bb1, bb2, bb3, bb4) = (Block(0), Block(1), Block(2), Block(3), Block(4));
        for b in [bb0, bb1, bb2, bb3, bb4] {
            func.ensure_block(b);
        }
        func.next_vreg = 64;

        func.blocks.get_mut(&bb0).unwrap().successors = vec![bb1];
        func.push_inst(
            bb0,
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(0), imm(0)]),
        );
        func.push_inst(
            bb0,
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(1), vreg(0)]),
        );
        func.push_inst(
            bb0,
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(2), imm(24)]),
        );
        func.push_inst(
            bb0,
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(3), imm(1)]),
        );
        func.push_inst(
            bb0,
            X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(bb1)]),
        );

        func.blocks.get_mut(&bb1).unwrap().successors = vec![bb2, bb4];
        func.push_inst(
            bb1,
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(1), imm(100)]),
        );
        func.push_inst(
            bb1,
            X86ISelInst::new(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::AE),
                    X86ISelOperand::Block(bb4),
                ],
            ),
        );

        func.blocks.get_mut(&bb2).unwrap().successors = vec![bb3];
        func.push_inst(
            bb2,
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(10), vreg(1)]),
        );
        func.push_inst(
            bb2,
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(11), vreg(2)]),
        );
        func.push_inst(
            bb2,
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(12), vreg(10)]),
        );
        func.push_inst(
            bb2,
            X86ISelInst::new(X86Opcode::ImulRR, vec![vreg(4), vreg(12), vreg(11)]),
        );
        func.push_inst(
            bb2,
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(5), vreg(4)]),
        );
        func.push_inst(
            bb2,
            X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(bb3)]),
        );

        func.blocks.get_mut(&bb3).unwrap().successors = vec![bb1];
        func.push_inst(
            bb3,
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(6), vreg(10), vreg(3)]),
        );
        func.push_inst(
            bb3,
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(1), vreg(6)]),
        );
        func.push_inst(
            bb3,
            X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(bb1)]),
        );

        func.push_inst(bb4, X86ISelInst::new(X86Opcode::Ret, vec![]));

        func
    }

    #[test]
    fn matmul_shaped_copy_chain_reduces() {
        let mut func = make_copy_chain_loop();
        let r = vr(func.next_vreg);
        let mut pass = X86StrengthReduce::new(admit_all);
        assert!(
            pass.run_on_function(&mut func),
            "the copy-chain (phi-eliminated) shape must reduce"
        );

        // The multiply became `mov v4, r`.
        let body = insts(&func, Block(2));
        assert_eq!(body[3].opcode, X86Opcode::MovRR);
        assert_eq!(body[3].operands, vec![vreg(4), X86ISelOperand::VReg(r)]);

        // Seed in the preheader reads the IV CARRIER (v1), not the rename.
        let ph = insts(&func, Block(0));
        assert!(ph.iter().any(|i| i.opcode == X86Opcode::ImulRRI
            && i.operands == vec![X86ISelOperand::VReg(r), vreg(1), imm(24)]));

        // Advance right after the writeback in the latch.
        let latch = insts(&func, Block(3));
        assert_eq!(latch[2].opcode, X86Opcode::AddRI);
        assert_eq!(
            latch[2].operands,
            vec![X86ISelOperand::VReg(r), X86ISelOperand::VReg(r), imm(24)]
        );
        assert_eq!(count_opcode(&func, X86Opcode::ImulRR), 0);
    }

    #[test]
    fn non_dominating_copy_chain_is_rejected() {
        // The iv rename sits in a CONDITIONAL arm: it does not dominate the
        // multiply, so its snapshot can be stale — must reject.
        //
        //   bb0 ph -> bb1 header -> bb2 (split) -> bb5a / bb5b -> bb3 latch
        let sig = Signature {
            params: vec![],
            returns: vec![Type::I64],
        };
        let mut func = X86ISelFunction::new("sr_nondom".to_string(), sig);
        let (bb0, bb1, bb2, bb3, bb4, bb5a, bb5b) = (
            Block(0),
            Block(1),
            Block(2),
            Block(3),
            Block(4),
            Block(5),
            Block(6),
        );
        for b in [bb0, bb1, bb2, bb3, bb4, bb5a, bb5b] {
            func.ensure_block(b);
        }
        func.next_vreg = 64;

        func.blocks.get_mut(&bb0).unwrap().successors = vec![bb1];
        func.push_inst(
            bb0,
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(0), imm(0)]),
        );
        func.push_inst(
            bb0,
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(1), vreg(0)]),
        );
        func.push_inst(
            bb0,
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(2), imm(24)]),
        );
        func.push_inst(
            bb0,
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(3), imm(1)]),
        );
        func.push_inst(
            bb0,
            X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(bb1)]),
        );

        func.blocks.get_mut(&bb1).unwrap().successors = vec![bb2, bb4];
        func.push_inst(
            bb1,
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(1), imm(100)]),
        );
        func.push_inst(
            bb1,
            X86ISelInst::new(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::AE),
                    X86ISelOperand::Block(bb4),
                ],
            ),
        );

        // bb2 splits on some in-loop condition.
        func.blocks.get_mut(&bb2).unwrap().successors = vec![bb5a, bb5b];
        func.push_inst(
            bb2,
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(0), imm(5)]),
        );
        func.push_inst(
            bb2,
            X86ISelInst::new(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::E),
                    X86ISelOperand::Block(bb5a),
                ],
            ),
        );

        // The iv rename lives ONLY in the taken arm.
        func.blocks.get_mut(&bb5a).unwrap().successors = vec![bb3];
        func.push_inst(
            bb5a,
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(10), vreg(1)]),
        );
        func.push_inst(
            bb5a,
            X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(bb3)]),
        );
        func.blocks.get_mut(&bb5b).unwrap().successors = vec![bb3];
        func.push_inst(
            bb5b,
            X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(bb3)]),
        );

        // Latch: the multiply reads the non-dominating rename; increment is
        // direct.
        func.blocks.get_mut(&bb3).unwrap().successors = vec![bb1];
        func.push_inst(
            bb3,
            X86ISelInst::new(X86Opcode::ImulRR, vec![vreg(4), vreg(10), vreg(2)]),
        );
        func.push_inst(
            bb3,
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(6), vreg(1), vreg(3)]),
        );
        func.push_inst(
            bb3,
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(1), vreg(6)]),
        );
        func.push_inst(
            bb3,
            X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(bb1)]),
        );

        func.push_inst(bb4, X86ISelInst::new(X86Opcode::Ret, vec![]));

        let mut pass = X86StrengthReduce::new(admit_all);
        assert!(
            !pass.run_on_function(&mut func),
            "a non-dominating (conditional-arm) iv rename must be rejected"
        );
        assert_eq!(count_opcode(&func, X86Opcode::ImulRR), 1);
    }

    #[test]
    fn stale_copy_read_after_writeback_is_rejected() {
        // The multiply reads an iv RENAME positioned after the writeback in
        // the latch: the snapshot is stale (one step behind) — must reject.
        let mut func = make_canonical_loop();
        {
            let body = &mut func.blocks.get_mut(&Block(2)).unwrap().insts;
            body.clear();
            body.push(X86ISelInst::new(X86Opcode::MovRR, vec![vreg(10), vreg(1)]));
            body.push(X86ISelInst::new(
                X86Opcode::AddRR,
                vec![vreg(6), vreg(1), vreg(3)],
            ));
            body.push(X86ISelInst::new(X86Opcode::MovRR, vec![vreg(1), vreg(6)]));
            // Reads the pre-update rename AFTER the update.
            body.push(X86ISelInst::new(
                X86Opcode::ImulRR,
                vec![vreg(4), vreg(10), vreg(2)],
            ));
            body.push(X86ISelInst::new(X86Opcode::MovRR, vec![vreg(5), vreg(4)]));
            body.push(X86ISelInst::new(
                X86Opcode::Jmp,
                vec![X86ISelOperand::Block(Block(1))],
            ));
        }
        let mut pass = X86StrengthReduce::new(admit_all);
        assert!(
            !pass.run_on_function(&mut func),
            "a stale rename read after the iv update must be rejected"
        );
        assert_eq!(count_opcode(&func, X86Opcode::ImulRR), 1);
    }

    #[test]
    fn sib_legal_strides_are_left_to_the_sib_fold() {
        for scale in [1i64, 2, 4, 8] {
            let mut func = make_canonical_loop();
            let ph = &mut func.blocks.get_mut(&Block(0)).unwrap().insts;
            ph[2] = X86ISelInst::new(X86Opcode::MovRI, vec![vreg(2), imm(scale)]);
            let mut pass = X86StrengthReduce::new(admit_all);
            assert!(
                !pass.run_on_function(&mut func),
                "SIB-legal stride {scale} must be left for the OPT-7 SIB fold"
            );
            assert_eq!(insts(&func, Block(2))[0].opcode, X86Opcode::ImulRR);
        }
    }

    #[test]
    fn runtime_valued_stride_is_rejected() {
        let mut func = make_canonical_loop();
        // The stride register is no longer a provable compile-time constant
        // (defined by an add, not MovRI): the obligation cannot carry it as
        // a literal, so the candidate must be left unreduced.
        let ph = &mut func.blocks.get_mut(&Block(0)).unwrap().insts;
        ph[2] = X86ISelInst::new(X86Opcode::AddRR, vec![vreg(2), vreg(0), vreg(0)]);
        let mut pass = X86StrengthReduce::new(admit_all);
        assert!(
            !pass.run_on_function(&mut func),
            "a runtime-valued stride must be rejected (constant strides only)"
        );
        assert_eq!(insts(&func, Block(2))[0].opcode, X86Opcode::ImulRR);
    }

    #[test]
    fn non_invariant_stride_is_rejected() {
        let mut func = make_canonical_loop();
        // Redefine the stride inside the loop body: no longer a single-def
        // constant.
        let body = &mut func.blocks.get_mut(&Block(2)).unwrap().insts;
        body.insert(4, X86ISelInst::new(X86Opcode::MovRI, vec![vreg(2), imm(5)]));
        let mut pass = X86StrengthReduce::new(admit_all);
        assert!(
            !pass.run_on_function(&mut func),
            "an in-loop stride definition must reject the candidate"
        );
        assert_eq!(insts(&func, Block(2))[0].opcode, X86Opcode::ImulRR);
    }

    #[test]
    fn multi_def_iv_is_rejected() {
        let mut func = make_canonical_loop();
        // A second in-loop writeback to the IV (e.g. a conditional re-entry
        // copy): the IV no longer has a single lockstep update.
        let body = &mut func.blocks.get_mut(&Block(2)).unwrap().insts;
        body.insert(
            4,
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(1), vreg(6)]),
        );
        let mut pass = X86StrengthReduce::new(admit_all);
        assert!(
            !pass.run_on_function(&mut func),
            "a multi-def IV must reject the candidate"
        );
        assert_eq!(insts(&func, Block(2))[0].opcode, X86Opcode::ImulRR);
    }

    #[test]
    fn live_flags_after_multiply_are_rejected() {
        let mut func = make_canonical_loop();
        // A flag reader right after the multiply: replacing imul (a flag
        // writer) with mov would change the consumed flags.
        let body = &mut func.blocks.get_mut(&Block(2)).unwrap().insts;
        body.insert(
            1,
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg(7), X86ISelOperand::CondCode(X86CondCode::O)],
            ),
        );
        let mut pass = X86StrengthReduce::new(admit_all);
        assert!(
            !pass.run_on_function(&mut func),
            "live flags after the multiply must reject the candidate"
        );
    }

    #[test]
    fn side_entry_into_loop_body_is_rejected() {
        let mut func = make_canonical_loop();
        // bb4 jumps into the middle of the loop from outside: the preheader
        // seed no longer dominates every execution of the body.
        let bb4 = Block(4);
        func.ensure_block(bb4);
        func.push_inst(
            bb4,
            X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(Block(2))]),
        );
        func.blocks.get_mut(&bb4).unwrap().successors = vec![Block(2)];
        // Reach bb4 from the entry so it is not dead.
        func.blocks.get_mut(&Block(0)).unwrap().successors = vec![Block(1), bb4];
        let mut pass = X86StrengthReduce::new(admit_all);
        assert!(
            !pass.run_on_function(&mut func),
            "a side entry into the loop body must reject the loop"
        );
    }

    #[test]
    fn split_increment_and_writeback_blocks_are_rejected() {
        let mut func = make_canonical_loop();
        // Move the writeback (and the jmp) into a separate latch block: the
        // lockstep same-block guard must refuse.
        let (bb2, bb5) = (Block(2), Block(5));
        func.ensure_block(bb5);
        let moved: Vec<X86ISelInst> = {
            let body = &mut func.blocks.get_mut(&bb2).unwrap().insts;
            body.split_off(3) // writeback + jmp
        };
        for inst in moved {
            let last = func.blocks.get_mut(&bb5).unwrap();
            last.insts.push(inst);
        }
        func.push_inst(
            bb2,
            X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(bb5)]),
        );
        func.blocks.get_mut(&bb2).unwrap().successors = vec![bb5];
        func.blocks.get_mut(&bb5).unwrap().successors = vec![Block(1)];
        let mut pass = X86StrengthReduce::new(admit_all);
        assert!(
            !pass.run_on_function(&mut func),
            "an increment/writeback split across blocks must be rejected (lockstep guard)"
        );
    }

    #[test]
    fn preheader_with_live_flags_is_rejected() {
        let mut func = make_canonical_loop();
        // The preheader ends in cmp + jcc: inserting the flag-writing seed
        // before the jcc would corrupt the branch.
        let bb0 = Block(0);
        {
            let ph = &mut func.blocks.get_mut(&bb0).unwrap().insts;
            ph.pop(); // drop jmp
            ph.push(X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(0), imm(7)]));
            ph.push(X86ISelInst::new(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::E),
                    X86ISelOperand::Block(Block(3)),
                ],
            ));
        }
        func.blocks.get_mut(&bb0).unwrap().successors = vec![Block(1), Block(3)];
        let mut pass = X86StrengthReduce::new(admit_all);
        assert!(
            !pass.run_on_function(&mut func),
            "a flag-live preheader insertion point must be rejected"
        );
    }

    #[test]
    fn non_iv_multiply_is_rejected() {
        let mut func = make_canonical_loop();
        // Both multiply operands are loop-invariant: nothing to reduce
        // (LICM's job, and imul writes flags so it declines too).
        let body = &mut func.blocks.get_mut(&Block(2)).unwrap().insts;
        body[0] = X86ISelInst::new(X86Opcode::ImulRR, vec![vreg(4), vreg(0), vreg(2)]);
        let mut pass = X86StrengthReduce::new(admit_all);
        assert!(
            !pass.run_on_function(&mut func),
            "a multiply of two invariants is not an IV reduction"
        );
    }

    #[test]
    fn quadratic_iv_times_iv_is_rejected() {
        let mut func = make_canonical_loop();
        let body = &mut func.blocks.get_mut(&Block(2)).unwrap().insts;
        body[0] = X86ISelInst::new(X86Opcode::ImulRR, vec![vreg(4), vreg(1), vreg(1)]);
        let mut pass = X86StrengthReduce::new(admit_all);
        assert!(
            !pass.run_on_function(&mut func),
            "iv*iv is quadratic, not a linear recurrence"
        );
    }

    #[test]
    fn nominal_width_is_mirrored_onto_the_recurrence_carrier() {
        let mut func = make_canonical_loop();
        func.vreg_nominal_widths.insert(vr(4), 64);
        let r = vr(func.next_vreg);
        let mut pass = X86StrengthReduce::new(admit_all);
        assert!(pass.run_on_function(&mut func));
        assert_eq!(
            func.vreg_nominal_widths.get(&r).copied(),
            Some(64),
            "the recurrence carrier must inherit the multiply dst's nominal width"
        );
    }

    #[test]
    fn nested_loop_invariant_mul_reduces_against_outer_iv() {
        // Outer loop over v1 (the IV); an INNER loop whose body contains the
        // multiply `v4 = v1 * v2`. The multiply is invariant in the inner
        // loop (imuls write flags, so LICM never hoists it) but linear in the
        // outer IV — the reduction must fire against the OUTER loop and
        // replace the inner-loop multiply with a mov of the recurrence.
        //
        //   bb0: v0=0; v1=mov v0; v2=24; v3=1; jmp bb1
        //   bb1 (outer header): cmp v1,100; jcc AE bb5
        //   bb2 (inner preheader): v7=0; v8=mov v7; jmp bb3
        //   bb3 (inner header/body/latch): v4 = imul v1, v2
        //                                  v9 = add v8, v3; v8 = mov v9
        //                                  cmp v8, 10; jcc B bb3 ; else fall bb4
        //   bb4 (outer latch): v6 = add v1, v3; v1 = mov v6; jmp bb1
        //   bb5: ret
        let sig = Signature {
            params: vec![],
            returns: vec![Type::I64],
        };
        let mut func = X86ISelFunction::new("sr_nested".to_string(), sig);
        let (bb0, bb1, bb2, bb3, bb4, bb5) =
            (Block(0), Block(1), Block(2), Block(3), Block(4), Block(5));
        for b in [bb0, bb1, bb2, bb3, bb4, bb5] {
            func.ensure_block(b);
        }
        func.next_vreg = 64;

        func.blocks.get_mut(&bb0).unwrap().successors = vec![bb1];
        func.push_inst(
            bb0,
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(0), imm(0)]),
        );
        func.push_inst(
            bb0,
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(1), vreg(0)]),
        );
        func.push_inst(
            bb0,
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(2), imm(24)]),
        );
        func.push_inst(
            bb0,
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(3), imm(1)]),
        );
        func.push_inst(
            bb0,
            X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(bb1)]),
        );

        func.blocks.get_mut(&bb1).unwrap().successors = vec![bb2, bb5];
        func.push_inst(
            bb1,
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(1), imm(100)]),
        );
        func.push_inst(
            bb1,
            X86ISelInst::new(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::AE),
                    X86ISelOperand::Block(bb5),
                ],
            ),
        );

        func.blocks.get_mut(&bb2).unwrap().successors = vec![bb3];
        func.push_inst(
            bb2,
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(7), imm(0)]),
        );
        func.push_inst(
            bb2,
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(8), vreg(7)]),
        );
        func.push_inst(
            bb2,
            X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(bb3)]),
        );

        func.blocks.get_mut(&bb3).unwrap().successors = vec![bb3, bb4];
        func.push_inst(
            bb3,
            X86ISelInst::new(X86Opcode::ImulRR, vec![vreg(4), vreg(1), vreg(2)]),
        );
        func.push_inst(
            bb3,
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(9), vreg(8), vreg(3)]),
        );
        func.push_inst(
            bb3,
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(8), vreg(9)]),
        );
        func.push_inst(
            bb3,
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(8), imm(10)]),
        );
        func.push_inst(
            bb3,
            X86ISelInst::new(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::B),
                    X86ISelOperand::Block(bb3),
                ],
            ),
        );

        func.blocks.get_mut(&bb4).unwrap().successors = vec![bb1];
        func.push_inst(
            bb4,
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(6), vreg(1), vreg(3)]),
        );
        func.push_inst(
            bb4,
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(1), vreg(6)]),
        );
        func.push_inst(
            bb4,
            X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(bb1)]),
        );

        func.push_inst(bb5, X86ISelInst::new(X86Opcode::Ret, vec![]));

        let r = vr(func.next_vreg);
        let mut pass = X86StrengthReduce::new(admit_all);
        assert!(
            pass.run_on_function(&mut func),
            "the inner-loop multiply must reduce against the outer IV"
        );

        // The multiply in the inner loop became a mov of the recurrence.
        let inner = insts(&func, bb3);
        assert_eq!(inner[0].opcode, X86Opcode::MovRR);
        assert_eq!(inner[0].operands, vec![vreg(4), X86ISelOperand::VReg(r)]);

        // The seed went to the OUTER preheader (bb0), the advance right after
        // the outer writeback in bb4.
        assert!(
            insts(&func, bb0)
                .iter()
                .any(|i| i.opcode == X86Opcode::ImulRRI
                    && i.operands == vec![X86ISelOperand::VReg(r), vreg(1), imm(24)]),
            "seed belongs in the outer preheader"
        );
        let outer_latch = insts(&func, bb4);
        assert_eq!(outer_latch[2].opcode, X86Opcode::AddRI);
        assert_eq!(
            outer_latch[2].operands,
            vec![X86ISelOperand::VReg(r), X86ISelOperand::VReg(r), imm(24)]
        );
        assert_eq!(count_opcode(&func, X86Opcode::ImulRR), 0);
    }

    /// The phi-eliminated PASS-THROUGH PARAM shape (matmul i-loop): the
    /// outer IV `v1` reaches its multiply inside the INNER loop through the
    /// multi-def block param `v20` — one def per inner-header predecessor
    /// edge, entry def copying the IV in, back-edge def passing the param's
    /// own value through unchanged.
    ///
    /// ```text
    ///   bb0 (outer ph)    : v0=0; v1=mov v0 (outer iv); v2=24; v3=1; jmp bb1
    ///   bb1 (outer header): cmp v1, 100; jcc AE bb6
    ///   bb2 (inner ph)    : v7=0; v8=mov v7 (inner iv)
    ///                       v20 = mov v1        ; P ENTRY def (edge copy)
    ///                       jmp bb3
    ///   bb3 (inner header): cmp v8, 10; jcc AE bb5
    ///   bb4 (inner latch) : v21 = mov v20       ; rename of P
    ///                       v4 = imul v21, v2   ; the i*N candidate
    ///                       v9 = add v8, v3; v8 = mov v9  ; inner iv update
    ///                       v20 = mov v21       ; P PASS-THROUGH def (edge copy)
    ///                       jmp bb3
    ///   bb5 (outer latch) : v6 = add v1, v3; v1 = mov v6; jmp bb1
    ///   bb6 (exit)        : ret
    /// ```
    fn make_passthrough_param_loop() -> X86ISelFunction {
        let sig = Signature {
            params: vec![],
            returns: vec![Type::I64],
        };
        let mut func = X86ISelFunction::new("sr_passthrough".to_string(), sig);
        let (bb0, bb1, bb2, bb3, bb4, bb5, bb6) = (
            Block(0),
            Block(1),
            Block(2),
            Block(3),
            Block(4),
            Block(5),
            Block(6),
        );
        for b in [bb0, bb1, bb2, bb3, bb4, bb5, bb6] {
            func.ensure_block(b);
        }
        func.next_vreg = 64;

        func.blocks.get_mut(&bb0).unwrap().successors = vec![bb1];
        func.push_inst(
            bb0,
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(0), imm(0)]),
        );
        func.push_inst(
            bb0,
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(1), vreg(0)]),
        );
        func.push_inst(
            bb0,
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(2), imm(24)]),
        );
        func.push_inst(
            bb0,
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(3), imm(1)]),
        );
        func.push_inst(
            bb0,
            X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(bb1)]),
        );

        func.blocks.get_mut(&bb1).unwrap().successors = vec![bb2, bb6];
        func.push_inst(
            bb1,
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(1), imm(100)]),
        );
        func.push_inst(
            bb1,
            X86ISelInst::new(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::AE),
                    X86ISelOperand::Block(bb6),
                ],
            ),
        );

        func.blocks.get_mut(&bb2).unwrap().successors = vec![bb3];
        func.push_inst(
            bb2,
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(7), imm(0)]),
        );
        func.push_inst(
            bb2,
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(8), vreg(7)]),
        );
        func.push_inst(
            bb2,
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(20), vreg(1)]),
        );
        func.push_inst(
            bb2,
            X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(bb3)]),
        );

        func.blocks.get_mut(&bb3).unwrap().successors = vec![bb4, bb5];
        func.push_inst(
            bb3,
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(8), imm(10)]),
        );
        func.push_inst(
            bb3,
            X86ISelInst::new(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::AE),
                    X86ISelOperand::Block(bb5),
                ],
            ),
        );

        func.blocks.get_mut(&bb4).unwrap().successors = vec![bb3];
        func.push_inst(
            bb4,
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(21), vreg(20)]),
        );
        func.push_inst(
            bb4,
            X86ISelInst::new(X86Opcode::ImulRR, vec![vreg(4), vreg(21), vreg(2)]),
        );
        func.push_inst(
            bb4,
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(9), vreg(8), vreg(3)]),
        );
        func.push_inst(
            bb4,
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(8), vreg(9)]),
        );
        func.push_inst(
            bb4,
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(20), vreg(21)]),
        );
        func.push_inst(
            bb4,
            X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(bb3)]),
        );

        func.blocks.get_mut(&bb5).unwrap().successors = vec![bb1];
        func.push_inst(
            bb5,
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(6), vreg(1), vreg(3)]),
        );
        func.push_inst(
            bb5,
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(1), vreg(6)]),
        );
        func.push_inst(
            bb5,
            X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(bb1)]),
        );

        func.push_inst(bb6, X86ISelInst::new(X86Opcode::Ret, vec![]));

        func
    }

    #[test]
    fn passthrough_param_canonicalizes() {
        let _recording_guard = ADMIT_RECORDING_LOCK
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        let mut func = make_passthrough_param_loop();
        let r = vr(func.next_vreg);
        LAST_ADMIT_STEP.store(i64::MIN, Ordering::SeqCst);
        LAST_ADMIT_STRIDE.store(i64::MIN, Ordering::SeqCst);
        let mut pass = X86StrengthReduce::new(admit_recording);
        assert!(
            pass.run_on_function(&mut func),
            "the pass-through-param shape must reduce against the OUTER IV"
        );
        assert_eq!(LAST_ADMIT_STEP.load(Ordering::SeqCst), 1);
        assert_eq!(LAST_ADMIT_STRIDE.load(Ordering::SeqCst), 24);

        // The inner-loop multiply became a mov of the recurrence.
        let inner = insts(&func, Block(4));
        assert_eq!(inner[1].opcode, X86Opcode::MovRR);
        assert_eq!(inner[1].operands, vec![vreg(4), X86ISelOperand::VReg(r)]);

        // The seed reads the OUTER IV CARRIER in the OUTER preheader (bb0),
        // never the param.
        let ph = insts(&func, Block(0));
        assert_eq!(ph[4].opcode, X86Opcode::ImulRRI);
        assert_eq!(
            ph[4].operands,
            vec![X86ISelOperand::VReg(r), vreg(1), imm(24)]
        );

        // The advance sits right after the OUTER writeback in bb5.
        let outer_latch = insts(&func, Block(5));
        assert_eq!(outer_latch[2].opcode, X86Opcode::AddRI);
        assert_eq!(
            outer_latch[2].operands,
            vec![X86ISelOperand::VReg(r), X86ISelOperand::VReg(r), imm(24)]
        );

        assert_eq!(count_opcode(&func, X86Opcode::ImulRR), 0);
        assert_eq!(count_opcode(&func, X86Opcode::ImulRRI), 1);
        assert!(
            !pass.run_on_function(&mut func),
            "second run must be a no-op"
        );
    }

    #[test]
    fn matmul_shaped_nested_loop_reduces_both_imuls() {
        // Both matmul multiplies at once: the k*N imul against the INNER IV
        // (direct carrier read) and the i*N imul against the OUTER IV
        // (through the pass-through param). Both must reduce.
        let mut func = make_passthrough_param_loop();
        {
            let body = &mut func.blocks.get_mut(&Block(4)).unwrap().insts;
            // Insert the k*N multiply right after the i*N one.
            body.insert(
                2,
                X86ISelInst::new(X86Opcode::ImulRR, vec![vreg(5), vreg(8), vreg(2)]),
            );
        }
        let r_inner = vr(func.next_vreg); // round 1: k*N against the inner IV
        let r_outer = vr(func.next_vreg + 1); // round 2: i*N via the param
        let mut pass = X86StrengthReduce::new(admit_all);
        assert!(
            pass.run_on_function(&mut func),
            "the matmul-shaped nested loop must reduce"
        );

        // BOTH multiplies are gone from the loops; the only remaining
        // multiplies are the two preheader seeds.
        assert_eq!(count_opcode(&func, X86Opcode::ImulRR), 0);
        assert_eq!(count_opcode(&func, X86Opcode::ImulRRI), 2);

        let inner = insts(&func, Block(4));
        assert_eq!(inner[1].opcode, X86Opcode::MovRR);
        assert_eq!(
            inner[1].operands,
            vec![vreg(4), X86ISelOperand::VReg(r_outer)]
        );
        assert_eq!(inner[2].opcode, X86Opcode::MovRR);
        assert_eq!(
            inner[2].operands,
            vec![vreg(5), X86ISelOperand::VReg(r_inner)]
        );

        // Inner seed in the INNER preheader (bb2), inner advance right after
        // the inner writeback.
        assert!(insts(&func, Block(2)).iter().any(|i| {
            i.opcode == X86Opcode::ImulRRI
                && i.operands == vec![X86ISelOperand::VReg(r_inner), vreg(8), imm(24)]
        }));
        assert_eq!(inner[5].opcode, X86Opcode::AddRI);
        assert_eq!(
            inner[5].operands,
            vec![
                X86ISelOperand::VReg(r_inner),
                X86ISelOperand::VReg(r_inner),
                imm(24)
            ]
        );

        // Outer seed in the OUTER preheader (bb0), outer advance right after
        // the outer writeback.
        assert!(insts(&func, Block(0)).iter().any(|i| {
            i.opcode == X86Opcode::ImulRRI
                && i.operands == vec![X86ISelOperand::VReg(r_outer), vreg(1), imm(24)]
        }));
        let outer_latch = insts(&func, Block(5));
        assert_eq!(outer_latch[2].opcode, X86Opcode::AddRI);
        assert_eq!(
            outer_latch[2].operands,
            vec![
                X86ISelOperand::VReg(r_outer),
                X86ISelOperand::VReg(r_outer),
                imm(24)
            ]
        );
    }

    #[test]
    fn passthrough_param_defs_must_agree() {
        // The back-edge def copies the INNER IV instead of passing the param
        // through: the defs no longer agree on one canonical source.
        let mut func = make_passthrough_param_loop();
        {
            let body = &mut func.blocks.get_mut(&Block(4)).unwrap().insts;
            body[4] = X86ISelInst::new(X86Opcode::MovRR, vec![vreg(20), vreg(8)]);
        }
        let mut pass = X86StrengthReduce::new(admit_all);
        assert!(
            !pass.run_on_function(&mut func),
            "disagreeing param defs must be rejected"
        );
        assert_eq!(count_opcode(&func, X86Opcode::ImulRR), 1);
    }

    #[test]
    fn passthrough_def_that_is_not_a_copy_is_rejected() {
        // The back-edge def MUTATES the value (add) instead of copying it.
        let mut func = make_passthrough_param_loop();
        {
            let body = &mut func.blocks.get_mut(&Block(4)).unwrap().insts;
            body[4] = X86ISelInst::new(X86Opcode::AddRR, vec![vreg(20), vreg(21), vreg(3)]);
        }
        let mut pass = X86StrengthReduce::new(admit_all);
        assert!(
            !pass.run_on_function(&mut func),
            "a non-copy param def must be rejected"
        );
        assert_eq!(count_opcode(&func, X86Opcode::ImulRR), 1);
    }

    #[test]
    fn passthrough_entry_def_in_conditional_arm_is_rejected() {
        // The ENTRY def sits in one arm of an in-loop conditional: paths
        // through the other arm reach the multiply with a value staled by a
        // previous outer iteration — the must-cover dataflow must reject.
        //
        //   bb0 ph -> bb1 hdr -> bb2 (split) -> bb7 (def) / bb8 -> bb8 ...
        let sig = Signature {
            params: vec![],
            returns: vec![Type::I64],
        };
        let mut func = X86ISelFunction::new("sr_param_arm".to_string(), sig);
        let (bb0, bb1, bb2, bb3, bb4, bb5, bb6, bb7, bb8) = (
            Block(0),
            Block(1),
            Block(2),
            Block(3),
            Block(4),
            Block(5),
            Block(6),
            Block(7),
            Block(8),
        );
        for b in [bb0, bb1, bb2, bb3, bb4, bb5, bb6, bb7, bb8] {
            func.ensure_block(b);
        }
        func.next_vreg = 64;

        func.blocks.get_mut(&bb0).unwrap().successors = vec![bb1];
        func.push_inst(
            bb0,
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(0), imm(0)]),
        );
        func.push_inst(
            bb0,
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(1), vreg(0)]),
        );
        func.push_inst(
            bb0,
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(2), imm(24)]),
        );
        func.push_inst(
            bb0,
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(3), imm(1)]),
        );
        func.push_inst(
            bb0,
            X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(bb1)]),
        );

        func.blocks.get_mut(&bb1).unwrap().successors = vec![bb2, bb6];
        func.push_inst(
            bb1,
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(1), imm(100)]),
        );
        func.push_inst(
            bb1,
            X86ISelInst::new(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::AE),
                    X86ISelOperand::Block(bb6),
                ],
            ),
        );

        // bb2: inner-iv init, then split on some condition.
        func.blocks.get_mut(&bb2).unwrap().successors = vec![bb7, bb8];
        func.push_inst(
            bb2,
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(7), imm(0)]),
        );
        func.push_inst(
            bb2,
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(8), vreg(7)]),
        );
        func.push_inst(
            bb2,
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(8), imm(5)]),
        );
        func.push_inst(
            bb2,
            X86ISelInst::new(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::E),
                    X86ISelOperand::Block(bb7),
                ],
            ),
        );

        // The entry def lives ONLY in the taken arm.
        func.blocks.get_mut(&bb7).unwrap().successors = vec![bb8];
        func.push_inst(
            bb7,
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(20), vreg(1)]),
        );
        func.push_inst(
            bb7,
            X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(bb8)]),
        );

        // bb8: inner preheader (join).
        func.blocks.get_mut(&bb8).unwrap().successors = vec![bb3];
        func.push_inst(
            bb8,
            X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(bb3)]),
        );

        func.blocks.get_mut(&bb3).unwrap().successors = vec![bb4, bb5];
        func.push_inst(
            bb3,
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(8), imm(10)]),
        );
        func.push_inst(
            bb3,
            X86ISelInst::new(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::AE),
                    X86ISelOperand::Block(bb5),
                ],
            ),
        );

        func.blocks.get_mut(&bb4).unwrap().successors = vec![bb3];
        func.push_inst(
            bb4,
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(21), vreg(20)]),
        );
        func.push_inst(
            bb4,
            X86ISelInst::new(X86Opcode::ImulRR, vec![vreg(4), vreg(21), vreg(2)]),
        );
        func.push_inst(
            bb4,
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(9), vreg(8), vreg(3)]),
        );
        func.push_inst(
            bb4,
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(8), vreg(9)]),
        );
        func.push_inst(
            bb4,
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(20), vreg(21)]),
        );
        func.push_inst(
            bb4,
            X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(bb3)]),
        );

        func.blocks.get_mut(&bb5).unwrap().successors = vec![bb1];
        func.push_inst(
            bb5,
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(6), vreg(1), vreg(3)]),
        );
        func.push_inst(
            bb5,
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(1), vreg(6)]),
        );
        func.push_inst(
            bb5,
            X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(bb1)]),
        );

        func.push_inst(bb6, X86ISelInst::new(X86Opcode::Ret, vec![]));

        let mut pass = X86StrengthReduce::new(admit_all);
        assert!(
            !pass.run_on_function(&mut func),
            "an entry def in a conditional arm must fail the must-cover dataflow"
        );
        assert_eq!(count_opcode(&func, X86Opcode::ImulRR), 1);
    }

    #[test]
    fn mutual_param_cycle_is_rejected() {
        // Two multi-def vregs copying each other with no root at the IV: the
        // resolution stack must reject the mutual cycle (fail-safe).
        let mut func = make_passthrough_param_loop();
        {
            let ph = &mut func.blocks.get_mut(&Block(2)).unwrap().insts;
            // bb2: v22 = mov v20; v20 = mov v22 (entry defs of the cycle).
            ph[2] = X86ISelInst::new(X86Opcode::MovRR, vec![vreg(22), vreg(20)]);
            ph.insert(
                3,
                X86ISelInst::new(X86Opcode::MovRR, vec![vreg(20), vreg(22)]),
            );
        }
        {
            let body = &mut func.blocks.get_mut(&Block(4)).unwrap().insts;
            // bb4: v22 = mov v20; v20 = mov v22 (back-edge defs of the cycle).
            body[4] = X86ISelInst::new(X86Opcode::MovRR, vec![vreg(22), vreg(20)]);
            body.insert(
                5,
                X86ISelInst::new(X86Opcode::MovRR, vec![vreg(20), vreg(22)]),
            );
        }
        let mut pass = X86StrengthReduce::new(admit_all);
        assert!(
            !pass.run_on_function(&mut func),
            "a mutual param cycle with no IV root must be rejected"
        );
        assert_eq!(count_opcode(&func, X86Opcode::ImulRR), 1);
    }

    #[test]
    fn param_redefined_inside_loop_body_is_rejected() {
        // An EXTRA in-body def of the param copying an unrelated (loop
        // invariant defined OUTSIDE the body) value: not a pass-through of
        // the IV — must reject.
        let mut func = make_passthrough_param_loop();
        {
            let ph = &mut func.blocks.get_mut(&Block(0)).unwrap().insts;
            ph.insert(
                4,
                X86ISelInst::new(X86Opcode::MovRI, vec![vreg(30), imm(7)]),
            );
        }
        {
            let hdr = &mut func.blocks.get_mut(&Block(3)).unwrap().insts;
            hdr.insert(
                0,
                X86ISelInst::new(X86Opcode::MovRR, vec![vreg(20), vreg(30)]),
            );
        }
        let mut pass = X86StrengthReduce::new(admit_all);
        assert!(
            !pass.run_on_function(&mut func),
            "a param redefinition with a non-IV source must be rejected"
        );
        assert_eq!(count_opcode(&func, X86Opcode::ImulRR), 1);
    }

    #[test]
    fn stale_param_read_after_writeback_is_rejected() {
        // The multiply moves to the OUTER latch AFTER the IV writeback,
        // still reading the pre-update param snapshot: one step stale.
        let mut func = make_passthrough_param_loop();
        let mul = {
            let body = &mut func.blocks.get_mut(&Block(4)).unwrap().insts;
            body.remove(1)
        };
        {
            let latch = &mut func.blocks.get_mut(&Block(5)).unwrap().insts;
            latch.insert(2, mul); // after `v1 = mov v6`
        }
        let mut pass = X86StrengthReduce::new(admit_all);
        assert!(
            !pass.run_on_function(&mut func),
            "a param-chain read after the IV writeback must be rejected as stale"
        );
        assert_eq!(count_opcode(&func, X86Opcode::ImulRR), 1);
    }
}
