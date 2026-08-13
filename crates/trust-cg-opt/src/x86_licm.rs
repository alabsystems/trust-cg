// trust-cg-opt - x86-64 Loop-Invariant Code Motion
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Loop-Invariant Code Motion (LICM) for x86-64 ISel-output functions.
//!
//! This is the x86 counterpart of [`crate::licm::LoopInvariantCodeMotion`],
//! which operates on the AArch64-shaped `trust_cg_ir::MachFunction`. The x86
//! pass-manager surface ([`crate::x86_pass_manager`]) consumes the distinct
//! [`X86ISelFunction`] IR (blocks carry their instructions inline, there is no
//! shared `InstId` arena, and there is no predecessor list or dominator tree on
//! the function). The hoisting *logic* and every safety precondition below are
//! ported verbatim from the verified AArch64 LICM; only the IR plumbing differs.
//!
//! # What it does
//!
//! Hoists provably loop-invariant, side-effect-free computations out of a loop
//! body into the loop's preheader so they execute once instead of every
//! iteration. The canonical win is constant materialization (`mov reg, imm`):
//! the same `movl $0x9e3779b1` / `movl $0x11e1a300` re-emitted on every
//! iteration of a tight integer kernel is hoisted to the preheader.
//!
//! # Safety preconditions (identical to the AArch64 pass)
//!
//! An instruction is hoisted ONLY when ALL of the following hold:
//!
//! 1. **Pure.** [`x86_inst_effect`] classifies it `Pure` — no loads, stores,
//!    calls, or barriers. Loads may observe a different value each iteration;
//!    stores/calls have effects that must run each iteration.
//! 2. **Speculatively safe.** It cannot trap. We therefore additionally exclude
//!    integer division (`Idiv`/`Div`) and the multi-result `Mul`, whose RDX:RAX
//!    fixed-register results are not modeled here. `mov`/`lea`/`add`/`shl`/...
//!    never trap.
//! 3. **No flag dependence.** It neither writes nor reads RFLAGS
//!    ([`x86_writes_flags`]/[`x86_reads_flags`]). Hoisting a flag writer past
//!    later in-loop flag consumers (a `cmp`+`jcc`) corrupts control flow;
//!    hoisting a flag reader reads flags from the wrong dynamic point. This is
//!    why almost every x86 arithmetic op (which sets RFLAGS) stays put — only
//!    the flag-free movers/`lea` are eligible, which is exactly the high-value
//!    set.
//! 4. **Produces a single SSA value in a virtual register.** Operand 0 is a
//!    `VReg`, and that VReg is defined exactly once across the whole function.
//!    Multi-def VRegs are path-sensitive carriers, not SSA values; hoisting one
//!    is unsound.
//! 5. **No fixed-register / relocation / pseudo coupling.** No `PReg` operand,
//!    no implicit fixed-register dependency opcode, no symbol/const-pool/stack
//!    operand, not a `Phi`/`StackAlloc`. This mirrors the AArch64 pass's refusal
//!    to move call glue (`x16 <- target`) or `adrp` address material.
//! 6. **Not a branch/terminator.**
//! 7. **All source operands are loop-invariant** — an immediate, a VReg defined
//!    outside the loop, or a VReg already proven invariant (transitive closure).
//!
//! # CFG preconditions
//!
//! The loop must have a *natural preheader*: a unique predecessor of the header
//! that is not in the loop body, ending in a control-flow terminator we can
//! insert before. We never synthesize a preheader (CFG/Phi mutation is not
//! sound here), exactly matching the AArch64 pass's conservatism.
//!
//! # Invariant-load tier (opt-in, O2+)
//!
//! On top of the pure tier, [`X86LoopInvariantCodeMotion::with_invariant_load_hoisting`]
//! additionally hoists **provably invariant, provably non-trapping stack-slot
//! loads** out of loops whose entire memory traffic is statically accounted
//! for. The full safety argument lives on `LoadTierAnalysis` and
//! `hoistable_invariant_load`; the summary:
//!
//! 1. **Every store in the loop must resolve to a fixed stack slot** (directly
//!    `[StackSlot]`-addressed, or through a pointer chain
//!    `resolve_frame_address` resolves). One unresolved store, call, atomic,
//!    volatile access, or fence anywhere in the loop disables the tier for the
//!    whole loop — hoist NOTHING is the fail-safe default.
//! 2. **The hoisted load's slot is disjoint** (slot-granular) from every slot
//!    stored in the loop, so the loaded value cannot change across iterations.
//! 3. **The load is provably non-trapping**: its address resolves to
//!    `[fixed-size slot + offset]` with the full access in bounds of the slot,
//!    and frame slots resolve to `RBP`-relative addresses that are mapped for
//!    the function's whole lifetime. It is therefore safe to execute in the
//!    preheader even when the loop body runs zero iterations (the value is
//!    simply dead), in a conditional preheader, and ahead of any in-loop trap.
//! 4. **Atomics/volatile/fences never participate**: any instruction carrying
//!    an `X86ProofOrigin` (the atomic/volatile lowering marker) anywhere in the
//!    loop disables the tier, and a marked load is never a candidate.
//!
//! # Reference
//!
//! LLVM `LICM.cpp`; trust-cg `crates/trust-cg-opt/src/licm.rs` (AArch64).

use std::collections::{HashMap, HashSet};

use trust_cg_ir::function::StackSlotAllocationKind;
use trust_cg_ir::x86_64_regs::{RAX, X86PReg};
use trust_cg_ir::{InstFlags, VReg, X86CondCode, X86Opcode};
use trust_cg_lower::function::StackSlotInfo;
use trust_cg_lower::instructions::Block;
use trust_cg_lower::{X86ISelFunction, X86ISelInst, X86ISelOperand};

use crate::effects::{
    MemoryEffect, x86_inst_effect, x86_produces_value, x86_reads_flags, x86_writes_flags,
};
use crate::mach_view;
use crate::x86_pass_manager::X86MachinePass;
use trust_cg_ir::regs::RegClass;

/// Loop-Invariant Code Motion for x86-64 ISel-output machine functions.
pub struct X86LoopInvariantCodeMotion {
    /// Enable the invariant stack-slot load tier (O2+ pipelines only). The
    /// pure tier always runs.
    hoist_invariant_loads: bool,
    /// Enable the invariant flag-writing-arithmetic tier (Lever B; O2+). Hoists
    /// provably invariant, non-trapping `imul` (the `i*n` index product) whose
    /// written RFLAGS is provably dead — see [`hoistable_flag_arith`] and
    /// [`rflags_dead_after_site`]/[`preheader_flag_hoist_safe`].
    hoist_flag_arith: bool,
    guarded_hoist: bool,
}

impl X86LoopInvariantCodeMotion {
    /// Pure-computation hoisting only (the historical policy; O1 uses this).
    pub fn pure_only() -> Self {
        Self {
            hoist_invariant_loads: false,
            hoist_flag_arith: false,
            guarded_hoist: false,
        }
    }

    /// Pure hoisting plus the invariant stack-slot load tier AND the invariant
    /// flag-writing-arithmetic tier (O2/O3).
    pub fn with_invariant_load_hoisting() -> Self {
        Self {
            hoist_invariant_loads: true,
            hoist_flag_arith: true,
            guarded_hoist: std::env::var_os("TCG_X86_LICM_GUARDED_HOIST").is_some(),
        }
    }

    /// Override the flag-writing-arithmetic tier (Lever B kill switch). The load
    /// tier is unaffected.
    pub fn with_flag_arith(mut self, enabled: bool) -> Self {
        self.hoist_flag_arith = enabled;
        self
    }

    /// Run x86 LICM directly on an ISel function.
    pub fn run_on_function(&mut self, func: &mut X86ISelFunction) -> bool {
        run_impl(
            func,
            self.hoist_invariant_loads,
            self.hoist_flag_arith,
            self.guarded_hoist,
        )
    }
}

impl X86MachinePass for X86LoopInvariantCodeMotion {
    fn name(&self) -> &str {
        "x86-licm"
    }

    fn run(&mut self, func: &mut X86ISelFunction) -> bool {
        run_impl(
            func,
            self.hoist_invariant_loads,
            self.hoist_flag_arith,
            self.guarded_hoist,
        )
    }
}

// ===========================================================================
// Driver
// ===========================================================================

fn run_impl(
    func: &mut X86ISelFunction,
    hoist_invariant_loads: bool,
    hoist_flag_arith: bool,
    guarded_hoist: bool,
) -> bool {
    // Need at least one back-edge to have a loop. A single block can have no
    // natural loop with a preheader, so bail fast in the common case.
    if func.block_order.len() < 2 {
        return false;
    }

    let mut preds = mach_view::predecessor_map(func);
    let mut idom = compute_idom(func, &preds);
    let mut loops = find_natural_loops(func, &preds, &idom);
    if loops.is_empty() {
        return false;
    }

    // S4 Region-LICM — Stage 1: DETECTION + TRACE ONLY. Gated on
    // TCG_REGION_LICM_DEBUG so the default compile pays ZERO cost; prints one
    // verdict line per (inner, outer) nesting (docs/region-licm-design-2026-07-16.md).
    if std::env::var_os("TCG_REGION_LICM_DEBUG").is_some() {
        region_licm_scan(func, &preds, &idom, &loops);
    }

    let mut changed = false;

    // S4 Region-LICM — Stage 2: hoist provably outer-invariant inner LOOPS out
    // of their enclosing loop (design §8 v2). DEFAULT-ON at O1+ (this pass does
    // not run at O0); kill switch `TCG_NO_REGION_LICM`. The transform is
    // fail-safe by construction (every legality miss DECLINES to the correct
    // original) and was certified before the default-ON flip by: b03 (29x) /
    // b01 (24x) native == LLVM; all 18 perf benches ON-vs-OFF 0-mismatch; a
    // ~24-program nested-loop differential vs LLVM x O2/O3 (invariant-inner +
    // break/continue/inner-call/i128/sibling-loops/3-deep/outer-varying-init/
    // inner-modifies-accumulator near-misses) 0-mismatch; and
    // bridge_differential_x86 with the pass forced ON, 0-mismatch. Runs BEFORE
    // the instruction tiers so their dominator/loop analyses see the final CFG;
    // the CFG is recomputed after each hoist (bounded — one hoist per nesting).
    if std::env::var_os("TCG_NO_REGION_LICM").is_none() {
        let mut guard = 0;
        while region_licm_hoist(func, &loops, &preds, &idom) {
            changed = true;
            guard += 1;
            if guard > 64 {
                break;
            }
            preds = mach_view::predecessor_map(func);
            idom = compute_idom(func, &preds);
            loops = find_natural_loops(func, &preds, &idom);
        }
    }

    // Whole-function single-def map: a VReg defined more than once is not a
    // pure SSA value and must never be hoisted (matches AArch64 LICM).
    let def_counts = build_def_counts(func);

    // Process innermost loops first (largest depth) so an inner-loop hoist can
    // feed an outer-loop hoist on the same run.
    let mut ordered: Vec<&NaturalLoop> = loops.iter().collect();
    ordered.sort_by_key(|lp| std::cmp::Reverse(lp.depth));

    for lp in ordered {
        if hoist_loop_invariants(
            func,
            lp,
            &def_counts,
            &idom,
            hoist_invariant_loads,
            hoist_flag_arith,
        ) {
            changed = true;
        }
    }

    // Pure-call cluster hoist tier (gated default-OFF behind `TCG_PURE_CALL_HOIST`;
    // this pass has NO translation-validation net, so it stays opt-in until its
    // `.fuzz-purecall/` adversarial corpus is differentially green). Hoists a
    // loop-invariant call to a proven-pure callee out of a loop PROVEN to run
    // >=1 time. Reuses the loops/idom/def_counts computed above — the existing
    // value-producer hoists move instructions between body and preheader but
    // never change the CFG or the whole-function def counts.
    if pure_call_hoist_enabled() {
        for lp in &loops {
            if hoist_pure_call_clusters(func, lp, &def_counts, &idom) {
                changed = true;
            }
        }
    }

    if guarded_hoist {
        for lp in &loops {
            if guarded_slice_hoist(func, lp) {
                changed = true;
            }
        }
    }

    changed
}

/// Gate for the pure-call cluster hoist tier. Default ON (opt-out kill switch
/// `TCG_NO_PURE_CALL_HOIST`). Landed default-on after a differential-fuzz
/// campaign: baseline vs both-on preserved exit codes across 354 program-pairs
/// (118 programs x -O0/-O2/-O3, x2-consistent, 0 mismatch), with the hoist
/// firing in 75/90 generated pure-fn-in-loop programs. The tier still has no
/// per-pass validation net, so the kill switch stays for fast rollback.
fn pure_call_hoist_enabled() -> bool {
    std::env::var_os("TCG_NO_PURE_CALL_HOIST").is_none()
}

// ===========================================================================
// Hoisting
// ===========================================================================

fn hoist_loop_invariants(
    func: &mut X86ISelFunction,
    lp: &NaturalLoop,
    def_counts: &HashMap<VReg, usize>,
    idom: &HashMap<Block, Block>,
    hoist_invariant_loads: bool,
    hoist_flag_arith: bool,
) -> bool {
    // Only hoist when a natural preheader exists. We never synthesize one:
    // rewiring CFG edges before proving any hoist is legal is exactly the
    // unsound shape the AArch64 pass refuses (join-heavy headers carrying
    // values from multiple predecessors).
    let Some(preheader) = lp.preheader else {
        return false;
    };

    // Lever-B (flag-writing-arithmetic tier) is admitted for this loop only when
    // the preheader insertion point is provably flag-dead: inserting a flag
    // writer there must be observationally invisible. This is a per-loop
    // property (preheader terminator + header prefix), so prove it once.
    let flag_arith_ok = hoist_flag_arith && preheader_flag_hoist_safe(func, preheader, lp.header);

    // Map VReg -> defining-block for definitions inside the loop body. Used to
    // tell "defined inside the loop" from "defined outside".
    let loop_defs = build_loop_defs(func, &lp.body);

    // Load-tier analysis. Positions (def sites, store sites) go stale once we
    // splice, so all of this is computed fresh per loop from the current
    // function and consumed before this loop's splice below.
    let load_tier: Option<LoadTierAnalysis> = if hoist_invariant_loads {
        LoadTierAnalysis::compute(func, lp, def_counts, idom)
    } else {
        None
    };

    // VRegs proven loop-invariant so far (transitive closure seed).
    let mut invariant_vregs: HashSet<VReg> = HashSet::new();

    // Instructions to hoist, identified by (source_block, index_within_block).
    // We resolve to concrete instructions at the end to avoid index churn while
    // iterating.
    let mut to_hoist: Vec<(Block, usize)> = Vec::new();
    let mut hoisted_set: HashSet<(Block, usize)> = HashSet::new();

    let mut found_new = true;
    while found_new {
        found_new = false;

        for &block_id in &func.block_order {
            if !lp.body.contains(&block_id) {
                continue;
            }
            let Some(block) = func.blocks.get(&block_id) else {
                continue;
            };

            for (idx, inst) in block.insts.iter().enumerate() {
                if hoisted_set.contains(&(block_id, idx)) {
                    continue;
                }

                let def = if let Some(def) = hoistable_def(inst, def_counts) {
                    // Pure tier: all source (non-def) operands must be
                    // loop-invariant.
                    let all_invariant = inst.operands[1..].iter().all(|op| {
                        is_operand_loop_invariant(op, &loop_defs, &invariant_vregs, def_counts)
                    });
                    if !all_invariant {
                        continue;
                    }
                    def
                } else if flag_arith_ok {
                    // Lever-B tier: provably invariant, non-trapping flag-writing
                    // arithmetic (the loop-invariant `imul` index product) whose
                    // written RFLAGS is provably dead at BOTH its original site
                    // (so removing the flag write changes nothing) and the
                    // preheader insertion point (checked once via
                    // `flag_arith_ok`). Falls through to the load tier when the
                    // opcode/shape is not a flag-arith candidate.
                    if let Some(def) = hoistable_flag_arith(inst, def_counts) {
                        let all_invariant = inst.operands[1..].iter().all(|op| {
                            is_operand_loop_invariant(op, &loop_defs, &invariant_vregs, def_counts)
                        });
                        if !all_invariant {
                            continue;
                        }
                        if !rflags_dead_after_site(func, block_id, idx) {
                            continue;
                        }
                        if std::env::var_os("TCG_X86_LICM_ALU_LOG").is_some() {
                            eprintln!(
                                "[licm-flag-arith] ACCEPT {:?} in `{}` block #{:?}",
                                inst.opcode, func.name, block_id.0,
                            );
                        }
                        def
                    } else if let Some(tier) = &load_tier {
                        let Some(def) = hoistable_invariant_load(
                            func,
                            inst,
                            tier,
                            &loop_defs,
                            &invariant_vregs,
                            def_counts,
                            idom,
                        ) else {
                            continue;
                        };
                        def
                    } else {
                        continue;
                    }
                } else if let Some(tier) = &load_tier {
                    // Load tier: provably invariant, non-trapping stack-slot
                    // load in a loop whose stores are all accounted for.
                    let Some(def) = hoistable_invariant_load(
                        func,
                        inst,
                        tier,
                        &loop_defs,
                        &invariant_vregs,
                        def_counts,
                        idom,
                    ) else {
                        continue;
                    };
                    def
                } else {
                    continue;
                };

                invariant_vregs.insert(def);
                to_hoist.push((block_id, idx));
                hoisted_set.insert((block_id, idx));
                found_new = true;
            }
        }
    }

    if to_hoist.is_empty() {
        return false;
    }

    // Materialize the hoist. Extract the chosen instructions (preserving their
    // discovery order, which respects intra-loop data dependencies because the
    // transitive closure only marks an instruction once its operands are
    // invariant) and remove them from their source blocks, then splice them
    // into the preheader just before its terminator.
    //
    // Removal is done per source block from the highest index downward so the
    // remaining indices stay valid.
    let mut hoisted_insts: Vec<(usize, X86ISelInst)> = Vec::with_capacity(to_hoist.len());
    let mut by_block: HashMap<Block, Vec<usize>> = HashMap::new();
    for (order, (block_id, idx)) in to_hoist.iter().enumerate() {
        by_block.entry(*block_id).or_default().push(*idx);
        // Placeholder filled in below; we need the instruction value, captured
        // before removal.
        let inst = func.blocks[block_id].insts[*idx].clone();
        hoisted_insts.push((order, inst));
    }
    // Keep discovery order so dependent invariants follow their producers.
    hoisted_insts.sort_by_key(|(order, _)| *order);

    for idxs in by_block.values_mut() {
        idxs.sort_unstable_by(|a, b| b.cmp(a)); // descending
    }
    for (block_id, idxs) in &by_block {
        let block = func.blocks.get_mut(block_id).expect("source block exists");
        for &idx in idxs {
            block.insts.remove(idx);
        }
    }

    // Splice into the preheader before its terminator.
    let ph = func
        .blocks
        .get_mut(&preheader)
        .expect("preheader block exists");
    let insert_pos = preheader_insert_pos(ph);
    for (offset, (_order, inst)) in hoisted_insts.into_iter().enumerate() {
        ph.insts.insert(insert_pos + offset, inst);
    }

    // X5 value-level net: verify the hoist introduced no use-before-def in the
    // preheader (fail-closed; single-def VRegs only). Closes the long-standing
    // "x86_licm has no validation net" silent-miscompile surface.
    verify_preheader_defs_precede_uses(func, preheader, def_counts);

    true
}

/// Compute the splice point in the preheader: immediately before the trailing
/// terminator, if any. Hoisted instructions are pure and value-producing, so
/// they must precede the control transfer to the header.
fn preheader_insert_pos(block: &trust_cg_lower::X86ISelBlock) -> usize {
    match block.insts.last() {
        Some(last) if last.flags.is_terminator() || last.flags.is_branch() => block.insts.len() - 1,
        _ => block.insts.len(),
    }
}

// ===========================================================================
// Pure-call cluster hoist tier (Piece 2 — the ackermann invariant-call lever)
//
// Hoists a loop-invariant call to a proven-pure callee (its arg-setup register
// moves + the CALL + the result copy) out of a loop into the preheader, but
// ONLY when the loop is proven to execute at least once. A pure callee may
// still DIVERGE or trap, so executing it once in the preheader of a loop that
// would otherwise run zero times introduces non-termination/traps the source
// never had — the >=1-trip proof is a hard soundness precondition, not a
// heuristic. The tier fails safe: any deviation from the exact recognized shape
// declines the hoist.
// ===========================================================================

/// The contiguous instruction range `[start ..= end]` of a pure-call cluster in
/// `block` (arg-setup register moves, the CALL at `call_idx`, and the result
/// copy), or `None` if the call at `call_idx` is not a hoistable cluster.
fn recognize_pure_call_cluster(
    block: &trust_cg_lower::X86ISelBlock,
    call_idx: usize,
    loop_defs: &HashMap<VReg, Block>,
    invariant_vregs: &HashSet<VReg>,
    def_counts: &HashMap<VReg, usize>,
) -> Option<(usize, usize)> {
    let call = &block.insts[call_idx];

    // Single scalar GPR return in RAX. Rejects void/sret/aggregate returns
    // (empty or multi result regs), narrow Movzx/MovzxW returns, i128 GprPair
    // (RAX+RDX), and XMM/FP returns.
    let result_regs = call.call_result_regs.as_ref()?;
    if result_regs.len() != 1 || result_regs[0].reg != RAX {
        return None;
    }

    // Result copy: the instruction immediately after the CALL must be a plain
    // register copy `MovRR/MovRR32 [VReg(dst), PReg(RAX)]` whose dst is a genuine
    // single-def SSA value (its in-loop uses are what the hoisted value feeds).
    let result_idx = call_idx.checked_add(1)?;
    let res = block.insts.get(result_idx)?;
    if !matches!(res.opcode, X86Opcode::MovRR | X86Opcode::MovRR32) {
        return None;
    }
    let [X86ISelOperand::VReg(dst), X86ISelOperand::PReg(src)] = res.operands.as_slice() else {
        return None;
    };
    if *src != RAX || def_counts.get(dst).copied().unwrap_or(0) != 1 {
        return None;
    }

    // Arg-setup moves: the `n_args` instructions immediately before the CALL
    // must be register copies into exactly the CALL's implicit argument
    // registers (`call_arg_regs`), each from a loop-invariant source. A variadic
    // AL-count `MovRI`, a stack-arg store, or an intervening RSP adjust all break
    // this shape -> the cluster is declined (fail-safe). IS_CALL_ARG_SETUP is
    // never set on the x86 ISel stream, so the cluster is recognized purely
    // structurally against the reliable `call_arg_regs` set.
    let arg_regs = &call.call_arg_regs;
    let n_args = arg_regs.len();
    let start = call_idx.checked_sub(n_args)?;
    let mut expected: HashSet<X86PReg> = arg_regs.iter().map(|a| a.reg).collect();
    if expected.len() != n_args {
        return None; // duplicate arg registers desync the accounting
    }
    for i in start..call_idx {
        let m = &block.insts[i];
        if !matches!(m.opcode, X86Opcode::MovRR | X86Opcode::MovRR32) {
            return None;
        }
        let [X86ISelOperand::PReg(dest), source] = m.operands.as_slice() else {
            return None;
        };
        if !expected.remove(dest) {
            return None; // dest is not one of this call's arg regs (or a dup)
        }
        if !is_operand_loop_invariant(source, loop_defs, invariant_vregs, def_counts) {
            return None;
        }
    }
    if !expected.is_empty() {
        return None; // some argument register was not populated by these moves
    }

    Some((start, result_idx))
}

/// Evaluate the x86 condition `cc` on the flag-setting compare operands
/// `(a, b)` (i.e. the flags of `CMP a, b`). Restricted to operands in
/// `[0, i32::MAX]` so signed/unsigned comparisons coincide and the 32-vs-64 bit
/// compare width cannot change the result; `None` (unknown) outside that range
/// or for non-comparison condition codes.
fn eval_cc(cc: X86CondCode, a: i64, b: i64) -> Option<bool> {
    const MAXV: i64 = i32::MAX as i64;
    if !(0..=MAXV).contains(&a) || !(0..=MAXV).contains(&b) {
        return None;
    }
    match cc {
        X86CondCode::B | X86CondCode::L => Some(a < b),
        X86CondCode::AE | X86CondCode::GE => Some(a >= b),
        X86CondCode::BE | X86CondCode::LE => Some(a <= b),
        X86CondCode::A | X86CondCode::G => Some(a > b),
        X86CondCode::E => Some(a == b),
        X86CondCode::NE => Some(a != b),
        _ => None,
    }
}

/// Forward constant-propagation over one block into `vals`. Records the value of
/// each vreg it can prove constant AND in `[0, i32::MAX]` (values outside that
/// range, or with unknown inputs, are left unknown so downstream evaluation
/// fails safe). Handles only the small opcode set the frontend's counted-loop
/// guard lowering uses; every other opcode leaves its def unknown.
fn interp_const_defs(block: &trust_cg_lower::X86ISelBlock, vals: &mut HashMap<VReg, i64>) {
    const MAXV: i64 = i32::MAX as i64;
    let record = |vals: &mut HashMap<VReg, i64>, d: VReg, v: i64| {
        if (0..=MAXV).contains(&v) {
            vals.insert(d, v);
        } else {
            vals.remove(&d);
        }
    };
    for m in &block.insts {
        let ops = m.operands.as_slice();
        match m.opcode {
            X86Opcode::MovRI => {
                if let [X86ISelOperand::VReg(d), X86ISelOperand::Imm(c)] = ops {
                    record(vals, *d, *c);
                }
            }
            // Register copies and zero-extensions: value-preserving for the
            // in-range non-negative values we track.
            X86Opcode::MovRR | X86Opcode::MovRR32 | X86Opcode::Movzx | X86Opcode::MovzxW => {
                if let [X86ISelOperand::VReg(d), X86ISelOperand::VReg(s)] = ops {
                    match vals.get(s).copied() {
                        Some(v) => record(vals, *d, v),
                        None => {
                            vals.remove(d);
                        }
                    }
                }
            }
            X86Opcode::AndRI => {
                if let [
                    X86ISelOperand::VReg(d),
                    X86ISelOperand::VReg(s),
                    X86ISelOperand::Imm(m2),
                ] = ops
                {
                    match vals.get(s).copied() {
                        Some(v) => record(vals, *d, v & *m2),
                        None => {
                            vals.remove(d);
                        }
                    }
                }
            }
            _ => {
                // Any other producing opcode makes its def unknown.
                if let Some(d) = defined_vreg(m) {
                    vals.remove(&d);
                }
            }
        }
    }
}

/// Prove the loop executes at least once by CONCRETELY evaluating its entry
/// guard on the loop-entry constant state. Returns `false` (not proven) whenever
/// any needed value is unknown — a false negative merely skips the hoist, but a
/// false positive is a miscompile, so the guard is evaluated by faithful
/// interpretation (no polarity juggling) and the branch DIRECTION is decided by
/// loop-body membership of the concretely-taken successor.
///
/// The frontend lowers `while rep < K` to a materialized boolean at LICM time
/// (branch fusion runs later): `CMP rep,K; SETcc bool; ...; CMP bool,0; Jcc`.
/// The interpreter seeds constants from the entry-path (idom chain up to the
/// preheader — this pins the counter to its INIT value, the first-iteration
/// value) then walks the header, tracking the last compare's operands as flags,
/// and reports whether control concretely enters the loop body.
fn loop_runs_at_least_once(
    func: &X86ISelFunction,
    lp: &NaturalLoop,
    preheader: Block,
    idom: &HashMap<Block, Block>,
) -> bool {
    let dbg = std::env::var_os("TCG_PURE_CALL_HOIST_DEBUG").is_some();
    macro_rules! decline {
        ($($a:tt)*) => {{ if dbg { eprintln!("[pure-call-hoist]   >=1-trip decline: {}", format!($($a)*)); } return false; }};
    }
    if !dominates(preheader, lp.header, idom) {
        decline!(
            "preheader {:?} does not dominate header {:?}",
            preheader,
            lp.header
        );
    }

    // Seed constants from the entry path: the idom chain from the preheader up to
    // the entry, interpreted entry-first. Blocks INSIDE the loop are never on
    // this chain, so a loop-carried counter is pinned to its preheader init
    // (its value on the FIRST header visit).
    let mut chain: Vec<Block> = Vec::new();
    let mut b = preheader;
    loop {
        chain.push(b);
        let Some(&up) = idom.get(&b) else { break };
        if up == b {
            break;
        }
        b = up;
    }
    chain.reverse();
    let mut vals: HashMap<VReg, i64> = HashMap::new();
    for blk in &chain {
        if let Some(bb) = func.blocks.get(blk) {
            interp_const_defs(bb, &mut vals);
        }
    }

    let Some(header) = func.blocks.get(&lp.header) else {
        decline!("header block {:?} missing", lp.header);
    };
    // Walk the header, extending `vals` and tracking the last compare's operands
    // as `flags`, until the conditional branch resolves concretely.
    let mut flags: Option<(i64, i64)> = None;
    for m in &header.insts {
        let ops = m.operands.as_slice();
        match m.opcode {
            X86Opcode::CmpRR => {
                let [X86ISelOperand::VReg(a), X86ISelOperand::VReg(bb)] = ops else {
                    decline!("CmpRR operands unexpected: {:?}", ops);
                };
                match (vals.get(a).copied(), vals.get(bb).copied()) {
                    (Some(x), Some(y)) => flags = Some((x, y)),
                    _ => decline!("CmpRR operand value unknown: {:?}", ops),
                }
            }
            X86Opcode::CmpRI | X86Opcode::CmpRI8 => {
                let [X86ISelOperand::VReg(a), X86ISelOperand::Imm(c)] = ops else {
                    decline!("CmpRI operands unexpected: {:?}", ops);
                };
                match vals.get(a).copied() {
                    Some(x) => flags = Some((x, *c)),
                    None => decline!("CmpRI operand value unknown: {:?}", ops),
                }
            }
            X86Opcode::Setcc => {
                let [X86ISelOperand::VReg(d), X86ISelOperand::CondCode(cc)] = ops else {
                    decline!("Setcc operands unexpected: {:?}", ops);
                };
                let Some((x, y)) = flags else {
                    decline!("Setcc with no preceding compare");
                };
                match eval_cc(*cc, x, y) {
                    Some(t) => {
                        vals.insert(*d, if t { 1 } else { 0 });
                    }
                    None => decline!("Setcc cc {:?} on ({}, {}) not evaluable", cc, x, y),
                }
            }
            X86Opcode::Jcc => {
                let [X86ISelOperand::CondCode(cc), X86ISelOperand::Block(t)] = ops else {
                    decline!("Jcc operands unexpected: {:?}", ops);
                };
                let Some((x, y)) = flags else {
                    decline!("Jcc with no preceding compare");
                };
                let taken = match eval_cc(*cc, x, y) {
                    Some(v) => v,
                    None => decline!("Jcc cc {:?} on ({}, {}) not evaluable", cc, x, y),
                };
                // The other successor is the fall-through / explicit-Jmp target.
                if header.successors.len() != 2 {
                    decline!("header has {} successors (want 2)", header.successors.len());
                }
                let other = header
                    .successors
                    .iter()
                    .copied()
                    .find(|s| s != t)
                    .unwrap_or(*t);
                let dest = if taken { *t } else { other };
                let enters = lp.body.contains(&dest);
                if dbg {
                    eprintln!(
                        "[pure-call-hoist]   guard resolved: taken={taken} dest={dest:?} enters_body={enters}"
                    );
                }
                return enters;
            }
            X86Opcode::Jmp | X86Opcode::Ret => {
                decline!("reached {:?} before a conditional branch", m.opcode);
            }
            // Value-producing guard-chain ops: fold constants forward.
            X86Opcode::MovRI
            | X86Opcode::MovRR
            | X86Opcode::MovRR32
            | X86Opcode::Movzx
            | X86Opcode::MovzxW
            | X86Opcode::AndRI => {
                // Reuse the single-block interpreter on just this instruction by
                // constructing a one-off — cheaper: inline the same logic.
                match (m.opcode, ops) {
                    (X86Opcode::MovRI, [X86ISelOperand::VReg(d), X86ISelOperand::Imm(c)]) => {
                        if (0..=i32::MAX as i64).contains(c) {
                            vals.insert(*d, *c);
                        } else {
                            vals.remove(d);
                        }
                    }
                    (
                        X86Opcode::MovRR
                        | X86Opcode::MovRR32
                        | X86Opcode::Movzx
                        | X86Opcode::MovzxW,
                        [X86ISelOperand::VReg(d), X86ISelOperand::VReg(s)],
                    ) => match vals.get(s).copied() {
                        Some(v) => {
                            vals.insert(*d, v);
                        }
                        None => {
                            vals.remove(d);
                        }
                    },
                    (
                        X86Opcode::AndRI,
                        [
                            X86ISelOperand::VReg(d),
                            X86ISelOperand::VReg(s),
                            X86ISelOperand::Imm(m2),
                        ],
                    ) => match vals.get(s).copied() {
                        Some(v) => {
                            vals.insert(*d, v & *m2);
                        }
                        None => {
                            vals.remove(d);
                        }
                    },
                    _ => {
                        if let Some(d) = defined_vreg(m) {
                            vals.remove(&d);
                        }
                    }
                }
            }
            _ => {
                // Unknown producing op: its def becomes unknown. If the guard
                // later needs it, evaluation fails safe.
                if let Some(d) = defined_vreg(m) {
                    vals.remove(&d);
                }
            }
        }
    }
    decline!("header had no resolvable conditional branch");
}

/// Hoist every loop-invariant pure-call cluster out of `lp` into its preheader,
/// when the loop is proven to run at least once. Returns whether anything moved.
fn hoist_pure_call_clusters(
    func: &mut X86ISelFunction,
    lp: &NaturalLoop,
    def_counts: &HashMap<VReg, usize>,
    idom: &HashMap<Block, Block>,
) -> bool {
    let dbg = std::env::var_os("TCG_PURE_CALL_HOIST_DEBUG").is_some();
    let n_pure_calls = |f: &X86ISelFunction| -> usize {
        lp.body
            .iter()
            .filter_map(|b| f.blocks.get(b))
            .flat_map(|b| b.insts.iter())
            .filter(|i| {
                i.opcode == X86Opcode::Call && i.flags.contains(InstFlags::PURE_CALL_HOISTABLE)
            })
            .count()
    };
    let Some(preheader) = lp.preheader else {
        if dbg && n_pure_calls(func) > 0 {
            eprintln!(
                "[pure-call-hoist] header={:?} DECLINE: no natural preheader ({} pure calls in body)",
                lp.header,
                n_pure_calls(func)
            );
        }
        return false;
    };
    // Soundness precondition: a pure call may diverge/trap, so it may only be
    // relocated ahead of a loop guaranteed to have executed it at least once.
    if !loop_runs_at_least_once(func, lp, preheader, idom) {
        if dbg && n_pure_calls(func) > 0 {
            eprintln!(
                "[pure-call-hoist] header={:?} DECLINE: >=1-trip NOT proven ({} pure calls in body)",
                lp.header,
                n_pure_calls(func)
            );
        }
        return false;
    }
    if dbg {
        eprintln!(
            "[pure-call-hoist] header={:?} >=1-trip PROVEN, {} pure call(s) in body",
            lp.header,
            n_pure_calls(func)
        );
    }

    let loop_defs = build_loop_defs(func, &lp.body);
    // v1 does not chain a hoisted cluster's result into a later cluster's
    // invariance, so the loop-defined-invariant seed stays empty: arg sources
    // must be defined OUTSIDE the loop.
    let invariant_vregs: HashSet<VReg> = HashSet::new();

    // Discover cluster instruction indices in discovery order (block order, then
    // ascending index). `claimed` guards against overlapping ranges.
    let mut to_hoist: Vec<(Block, usize)> = Vec::new();
    for &block_id in &func.block_order {
        if !lp.body.contains(&block_id) {
            continue;
        }
        let Some(block) = func.blocks.get(&block_id) else {
            continue;
        };
        let mut claimed: HashSet<usize> = HashSet::new();
        for idx in 0..block.insts.len() {
            let inst = &block.insts[idx];
            if inst.opcode != X86Opcode::Call
                || !inst.flags.contains(InstFlags::PURE_CALL_HOISTABLE)
            {
                continue;
            }
            let Some((start, end)) =
                recognize_pure_call_cluster(block, idx, &loop_defs, &invariant_vregs, def_counts)
            else {
                if dbg {
                    let call = &block.insts[idx];
                    eprintln!(
                        "[pure-call-hoist]   call@{:?}[{}] NOT recognized: {} arg_regs, result_regs={:?}, next_op={:?}",
                        block_id,
                        idx,
                        call.call_arg_regs.len(),
                        call.call_result_regs.as_ref().map(|r| r.len()),
                        block.insts.get(idx + 1).map(|i| i.opcode),
                    );
                }
                continue;
            };
            if (start..=end).any(|i| claimed.contains(&i)) {
                continue; // overlaps an already-claimed cluster — skip defensively
            }
            for i in start..=end {
                claimed.insert(i);
                to_hoist.push((block_id, i));
            }
        }
    }

    if to_hoist.is_empty() {
        return false;
    }

    if std::env::var_os("TCG_PURE_CALL_HOIST_DEBUG").is_some() {
        eprintln!(
            "[pure-call-hoist] loop header={:?} >=1-trip PROVEN, hoisting {} cluster instruction(s) to preheader {:?}",
            lp.header,
            to_hoist.len(),
            preheader
        );
    }

    // Extract in discovery order, remove from source blocks high-index-first so
    // remaining indices stay valid, then splice into the preheader before its
    // terminator. Mirrors the value-producer splice in `hoist_loop_invariants`,
    // kept separate to move contiguous multi-inst clusters as units.
    let mut hoisted: Vec<(usize, X86ISelInst)> = Vec::with_capacity(to_hoist.len());
    let mut by_block: HashMap<Block, Vec<usize>> = HashMap::new();
    for (order, (block_id, idx)) in to_hoist.iter().enumerate() {
        by_block.entry(*block_id).or_default().push(*idx);
        hoisted.push((order, func.blocks[block_id].insts[*idx].clone()));
    }
    hoisted.sort_by_key(|(order, _)| *order);
    for idxs in by_block.values_mut() {
        idxs.sort_unstable_by(|a, b| b.cmp(a)); // descending
    }
    for (block_id, idxs) in &by_block {
        let block = func
            .blocks
            .get_mut(block_id)
            .expect("cluster source block exists");
        for &idx in idxs {
            block.insts.remove(idx);
        }
    }
    let ph = func
        .blocks
        .get_mut(&preheader)
        .expect("preheader block exists");
    let insert_pos = preheader_insert_pos(ph);
    for (offset, (_order, inst)) in hoisted.into_iter().enumerate() {
        ph.insts.insert(insert_pos + offset, inst);
    }

    // X5 value-level net: fail-closed use-before-def check on the spliced cluster.
    verify_preheader_defs_precede_uses(func, preheader, def_counts);

    true
}

/// Returns the single SSA def VReg of `inst` iff `inst` satisfies every
/// machine-movement precondition (purity, no flag/memory/call/fixed-register
/// coupling, single whole-function def). Mirrors the AArch64 LICM gate set.
fn hoistable_def(inst: &X86ISelInst, def_counts: &HashMap<VReg, usize>) -> Option<VReg> {
    let flags = inst.flags;

    // Pure memory effect only (no load/store/call/barrier).
    if !x86_inst_effect(inst).is_pure() {
        return None;
    }
    // Must define a value.
    if !x86_produces_value(inst.opcode) {
        return None;
    }
    // No control flow.
    if flags.is_call() || flags.is_branch() || flags.is_terminator() || flags.is_return() {
        return None;
    }
    // No side effects / memory traffic at the flag level (belt and suspenders
    // on top of the effect classification).
    if flags.has_side_effects() || flags.reads_memory() || flags.writes_memory() {
        return None;
    }
    // No RFLAGS dependence in either direction.
    if x86_writes_flags(inst.opcode) || x86_reads_flags(inst.opcode) {
        return None;
    }
    // Exclude pseudos and trapping / fixed-register-result opcodes that the
    // effect table classifies "pure" but are not safe to relocate here.
    if !is_hoistable_opcode(inst.opcode) {
        return None;
    }
    // No fixed-register / relocation / pseudo operands.
    if inst_touches_fixed_or_abstract_operand(inst) {
        return None;
    }
    // Tied def-use opcodes read their destination; treating their other
    // operands as the only sources is unsound. Decline them.
    if first_operand_is_def_and_use(inst) {
        return None;
    }

    // Operand 0 must be a single-def VReg.
    let def = match inst.operands.first() {
        Some(X86ISelOperand::VReg(v)) => *v,
        _ => return None,
    };
    if def_counts.get(&def).copied().unwrap_or(0) != 1 {
        return None;
    }

    Some(def)
}

/// Allowlist of opcodes safe to hoist. Deliberately conservative: only flag-free,
/// non-trapping, single-result computations. This excludes division (traps),
/// the RDX:RAX `Mul`, and every flag-writing arithmetic/logical/shift op (those
/// are already rejected by `x86_writes_flags`, but the allowlist documents the
/// admitted set and guards against future opcode additions defaulting in).
fn is_hoistable_opcode(opcode: X86Opcode) -> bool {
    use X86Opcode::*;
    matches!(
        opcode,
        // Constant / register materialization and copies.
        MovRI | MovRR | MovRR32
        // Zero / sign extensions (flag-free, non-trapping).
        | Movzx | MovzxW | MovsxB | MovsxW | Movsx
        // Address computation (no memory access, no flags).
        | Lea | LeaSib | LeaRip
        // SSE register-register moves.
        | MovsdRR | MovssRR | MovdqaRR
        // GPR <-> XMM transfers (flag-free).
        | MovdToXmm | MovdFromXmm | MovqToXmm | MovqFromXmm
    )
}

/// True if any operand references a physical register, a symbol/relocation, a
/// stack slot, or a constant-pool entry — i.e. fixed machine state LICM does
/// not model as an SSA value.
fn inst_touches_fixed_or_abstract_operand(inst: &X86ISelInst) -> bool {
    inst.operands.iter().any(operand_is_fixed_or_abstract)
}

fn operand_is_fixed_or_abstract(operand: &X86ISelOperand) -> bool {
    match operand {
        X86ISelOperand::PReg(_)
        | X86ISelOperand::Symbol(_)
        | X86ISelOperand::StackSlot(_)
        | X86ISelOperand::ConstPoolEntry(_) => true,
        // A memory operand here would mean a load/store, already excluded by the
        // purity gate, but be defensive about fixed registers inside addresses.
        X86ISelOperand::MemAddr { base, .. } => operand_is_fixed_or_abstract(base),
        X86ISelOperand::SibMemAddr { base, index, .. } => {
            operand_is_fixed_or_abstract(base) || operand_is_fixed_or_abstract(index)
        }
        _ => false,
    }
}

/// Tied def-use opcodes whose operand 0 is both written and read. Their "source"
/// operands are not the whole input set, so the invariance test under-counts.
/// (These also all write flags and are rejected upstream, but be explicit.)
fn first_operand_is_def_and_use(inst: &X86ISelInst) -> bool {
    use X86Opcode::*;
    matches!(
        inst.opcode,
        Neg | Not
            | Inc
            | Dec
            | AddRI
            | SubRI
            | AndRI
            | OrRI
            | XorRI
            | AddRM
            | SubRM
            | ImulRM
            | ImulRMSib
            | ShlRI
            | ShrRI
            | SarRI
            | ShlRR
            | ShrRR
            | SarRR
            | AdcRR
            | SbbRR
    )
}

// ===========================================================================
// Lever-B: invariant flag-writing-arithmetic tier
//
// The pure tier refuses every RFLAGS-writing opcode (`hoistable_def` at the
// `x86_writes_flags` gate). That leaves the loop-invariant index product
// `imul i, n` (both operands invariant in the inner loop) recomputed every
// iteration. This tier hoists such a flag writer to the preheader — but ONLY
// when its written RFLAGS is provably DEAD, so the relocation is observationally
// invisible.
//
// # Soundness
//
// Moving flag writer `W` (invariant value, single SSA def) from the loop body to
// the preheader changes program behavior ONLY through the RFLAGS it writes, so
// it is sound iff no flag *reader* observes `W`'s flags at EITHER location:
//
// * **Removal site (condition a, [`rflags_dead_after_site`]).** Scanning forward
//   from `W` within its block, the first flag-relevant instruction must be a
//   *full* flag definer (`x86_fully_defines_flags` — architecturally writes all
//   six status flags, independent of prior state), reached before any flag
//   reader. Then every downstream reader observes that definer, never `W`.
//   Reaching the block end without a full definer is treated as "possibly live"
//   → refuse. (A partial writer such as another `imul`/shift is skipped, never
//   credited as covering.)
//
// * **Insertion site (condition b, [`preheader_flag_hoist_safe`]).** Symmetric:
//   the preheader terminator must not read flags, and the header — the
//   first-iteration successor — must reach a full flag definer before any
//   reader. Then the flags `W` writes just ahead of the terminator are
//   immediately overwritten on entry to the loop and never observed.
//
// Both scans rely on `x86_reads_flags` being COMPLETE (it lists every
// flag-reading opcode: Cmovcc/Cmovcc32/Setcc/Jcc/AdcRR/SbbRR — there are no
// rotate-through-carry opcodes in this backend), which is already a
// correctness-load-bearing predicate for the scheduler and the pure tier.
//
// Only non-trapping, 3-operand, pure-def-operand-0 flag writers are admitted
// (`imul r,r` / `imul r,r,imm`); division and the RDX:RAX `mul` are excluded, so
// speculation safety is unchanged from the pure tier.
// ===========================================================================

/// Allowlist of flag-WRITING opcodes safe to hoist under the Lever-B tier: the
/// non-trapping, 3-operand forms whose operand 0 is a pure def (not tied) and
/// whose only inputs are the source operands. Division and the RDX:RAX `mul`
/// are excluded, so speculation safety is unchanged from the pure tier.
///
/// `ImulRR` = `dst, src1, src2`; `ImulRRI` = `dst, src, imm`.
///
/// The three-address integer ALU forms belong here for exactly the same reason
/// and were simply never added: they are pure, non-trapping, produce a value in
/// operand 0, and — unlike `AdcRR`/`SbbRR` — never READ flags. The flag WRITE is
/// the only thing that ever kept them out, and `rflags_dead_after_site` plus
/// `preheader_flag_hoist_safe` are precisely the proof that the write is
/// unobservable at both ends. Nothing in that argument is `imul`-specific.
///
/// ⚑ Only the RR forms qualify. The immediate and shift forms (`AddRI`,
/// `OrRI`, `ShlRI`, `ShlRR`, `Neg`, `Not`, `Inc`, `Dec`, …) are TWO-ADDRESS at
/// ISel level — operand 0 is both def and use — and `first_operand_is_def_and_use`
/// rejects them. Listing them here would be dead weight that reads as coverage.
///
/// Kill switch `TCG_NO_X86_LICM_ALU` restores the imul-only behaviour so the
/// extension can be A/B'd inside ONE dylib.
fn is_hoistable_flag_arith_opcode(opcode: X86Opcode) -> bool {
    use X86Opcode::*;
    if matches!(opcode, ImulRR | ImulRRI) {
        return true;
    }
    licm_alu_hoist_enabled() && matches!(opcode, AddRR | SubRR | AndRR | OrRR | XorRR)
}

fn licm_alu_hoist_enabled() -> bool {
    std::env::var_os("TCG_NO_X86_LICM_ALU").is_none()
}

/// True iff `opcode` architecturally overwrites ALL six status flags
/// (OF/SF/ZF/AF/PF/CF) as a function of its inputs alone, independent of the
/// prior flag state. Such an instruction fully "covers" any earlier flag write:
/// every subsequent reader observes only this definer. Deliberately EXCLUDES
/// partial writers — `imul`/`mul` (leave SF/ZF/AF/PF undefined), `inc`/`dec`
/// (leave CF), shifts (OF defined only for count 1), `bt*` (CF only), and the
/// bit-scan/count ops — so the coverage argument never rests on an undefined or
/// preserved flag.
fn x86_fully_defines_flags(opcode: X86Opcode) -> bool {
    use X86Opcode::*;
    matches!(
        opcode,
        AddRR
            | AddRI
            | AddRM
            | SubRR
            | SubRI
            | SubRM
            | CmpRR
            | CmpRI
            | CmpRI8
            | CmpRM
            | TestRR
            | TestRI
            | TestRM
            | AndRR
            | AndRI
            | OrRR
            | OrRI
            | XorRR
            | XorRI
            | Neg
    )
}

/// Returns the single SSA def VReg of `inst` iff it is an admissible Lever-B
/// flag-writing-arithmetic candidate: a pure (memory-free), non-trapping,
/// 3-operand `imul` with a single-def virtual operand-0 destination, no fixed /
/// abstract operands, and no flag *read*. Flag WRITES are permitted here (unlike
/// [`hoistable_def`]); the caller additionally proves the written flags dead via
/// [`rflags_dead_after_site`] and [`preheader_flag_hoist_safe`].
fn hoistable_flag_arith(inst: &X86ISelInst, def_counts: &HashMap<VReg, usize>) -> Option<VReg> {
    let flags = inst.flags;

    if !is_hoistable_flag_arith_opcode(inst.opcode) {
        return None;
    }
    // Pure memory effect only (imul r,r / r,r,imm touch no memory).
    if !x86_inst_effect(inst).is_pure() {
        return None;
    }
    if !x86_produces_value(inst.opcode) {
        return None;
    }
    if flags.is_call() || flags.is_branch() || flags.is_terminator() || flags.is_return() {
        return None;
    }
    if flags.has_side_effects() || flags.reads_memory() || flags.writes_memory() {
        return None;
    }
    // Flag WRITES are the point of this tier; flag READS are never safe to
    // relocate (they would observe flags from the wrong dynamic point).
    if x86_reads_flags(inst.opcode) {
        return None;
    }
    if inst_touches_fixed_or_abstract_operand(inst) {
        return None;
    }
    // Belt-and-suspenders: never a tied def-use form (imul r,r / r,r,imm are
    // not, but guard against future opcode additions).
    if first_operand_is_def_and_use(inst) {
        return None;
    }

    let def = match inst.operands.first() {
        Some(X86ISelOperand::VReg(v)) => *v,
        _ => return None,
    };
    if def_counts.get(&def).copied().unwrap_or(0) != 1 {
        return None;
    }

    Some(def)
}

/// Condition (a): is the RFLAGS written by the instruction at `(block_id, idx)`
/// provably dead immediately after it? Scans forward within the same block: a
/// full flag definer ([`x86_fully_defines_flags`]) reached before any flag
/// reader ([`x86_reads_flags`]) proves death; a reader first, or reaching the
/// block end without a full definer, is treated as "possibly live" → not dead.
fn rflags_dead_after_site(func: &X86ISelFunction, block_id: Block, idx: usize) -> bool {
    let Some(block) = func.blocks.get(&block_id) else {
        return false;
    };
    for later in block.insts.iter().skip(idx + 1) {
        if x86_reads_flags(later.opcode) {
            return false;
        }
        if x86_fully_defines_flags(later.opcode) {
            return true;
        }
    }
    // Fell off the block end without a proven full re-definition: the flags may
    // be live-out into a successor. Refuse (conservative).
    false
}

/// Condition (b): is it safe to insert a flag writer at this loop's preheader
/// insertion point (just before its terminator)? Requires (1) the preheader
/// terminator not read flags, and (2) the header — the first-iteration successor
/// — reach a full flag definer before any flag reader, so the inserted flags are
/// overwritten on loop entry and never observed. Conservative: any ambiguity
/// (terminator reads flags, header reader-before-definer, header exhausted
/// without a full definer) refuses the whole tier for the loop.
fn preheader_flag_hoist_safe(func: &X86ISelFunction, preheader: Block, header: Block) -> bool {
    // (1) The preheader terminator (the instruction the hoist is spliced ahead
    //     of) must not consume the flags we are about to write.
    if let Some(ph) = func.blocks.get(&preheader) {
        if let Some(last) = ph.insts.last()
            && (last.flags.is_terminator() || last.flags.is_branch())
            && x86_reads_flags(last.opcode)
        {
            return false;
        }
    } else {
        return false;
    }

    // (2) The header must clobber flags (full definer) before any reader on the
    //     path entered from the preheader.
    let Some(hdr) = func.blocks.get(&header) else {
        return false;
    };
    for inst in &hdr.insts {
        if x86_reads_flags(inst.opcode) {
            return false;
        }
        if x86_fully_defines_flags(inst.opcode) {
            return true;
        }
    }
    // Header exhausted without a full flag definer: flags may reach a reader in
    // a successor. Refuse (conservative).
    false
}

/// Is `operand` loop-invariant? An immediate is; a VReg is invariant iff it is a
/// whole-function single def AND (defined outside the loop OR already proven
/// invariant). A memory-address operand is invariant iff its register
/// components are (this only ever gates `Lea`/`LeaSib`, which compute pure
/// address arithmetic — actual loads/stores are rejected by the purity gate
/// before operand invariance is consulted). Anything else (PReg, symbol,
/// stack slot, block, ...) is not.
fn is_operand_loop_invariant(
    operand: &X86ISelOperand,
    loop_defs: &HashMap<VReg, Block>,
    invariant_vregs: &HashSet<VReg>,
    def_counts: &HashMap<VReg, usize>,
) -> bool {
    match operand {
        X86ISelOperand::VReg(v) => {
            is_vreg_loop_invariant(*v, loop_defs, invariant_vregs, def_counts)
        }
        X86ISelOperand::Imm(_) | X86ISelOperand::FImm(_) => true,
        X86ISelOperand::MemAddr { base, .. } => {
            is_operand_loop_invariant(base, loop_defs, invariant_vregs, def_counts)
        }
        X86ISelOperand::SibMemAddr { base, index, .. } => {
            is_operand_loop_invariant(base, loop_defs, invariant_vregs, def_counts)
                && is_operand_loop_invariant(index, loop_defs, invariant_vregs, def_counts)
        }
        _ => false,
    }
}

fn is_vreg_loop_invariant(
    v: VReg,
    loop_defs: &HashMap<VReg, Block>,
    invariant_vregs: &HashSet<VReg>,
    def_counts: &HashMap<VReg, usize>,
) -> bool {
    if def_counts.get(&v).copied().unwrap_or(0) != 1 {
        return false;
    }
    if loop_defs.contains_key(&v) {
        invariant_vregs.contains(&v)
    } else {
        // Defined outside the loop body (or never defined: an entry/arg
        // value) — invariant relative to this loop.
        true
    }
}

// ===========================================================================
// Invariant-load tier
//
// Hoists plain stack-slot loads whose value provably cannot change across any
// iteration of the loop, and whose execution provably cannot trap, so they are
// safe to execute once in the preheader — even speculatively (zero-iteration
// loops, conditional preheaders, ahead of in-loop traps).
//
// # Soundness argument
//
// A load `dst = [slot s + off]` (with `[off, off+width)` inside the fixed-size
// slot `s`) hoisted from loop `L` to `L`'s preheader is sound because:
//
// 1. **Same address every iteration.** Stack slots resolve to constant
//    RBP-relative frame offsets during frame lowering (`RBP` is established in
//    the prologue and never moves), so the address is a per-function constant.
//
// 2. **Same value as every in-loop execution.** The tier is enabled for `L`
//    only when EVERY memory-writing instruction in `L` is a plain store whose
//    target resolves to a fixed stack slot (directly `[StackSlot]`-addressed,
//    or through a single-def pointer chain of `MovRR` copies, `Lea` address
//    arithmetic, and one-hop store-to-load forwarding through a non-escaped
//    slot), and no in-loop store targets `s`. Calls, fences, atomics and
//    volatile accesses (any `proof_origin` marker), `Push`, dynamic
//    `StackAlloc`, SIB-addressed stores, and stores through unresolvable
//    pointers all disable the tier for the whole loop: hoist NOTHING is the
//    fail-safe default. (`Pop` needs no veto: it reads `[RSP]` and cannot
//    write a slot, and slots are RBP-relative so RSP motion cannot re-alias
//    them.) Cross-thread interference without an in-loop synchronization
//    point (which would disable the tier) on a stack slot would be a data
//    race, hence UB in the source model.
//
// 3. **Cannot trap.** The access is fully in bounds of a fixed-size slot in
//    the function's own frame, which is mapped for the function's whole
//    lifetime. Executing it in the preheader when the loop would run zero
//    iterations (or ahead of an in-loop trap) allocates no side effect and
//    produces a value that is simply dead — plain loads are effect-free, and
//    the hoisted load is proven not to be an atomic/volatile carrier.
//
// # Store-to-load forwarding (pointer resolution through a slot)
//
// The frontend cells reference locals into stack slots: the pointer value is
// stored to slot `q` once and re-loaded wherever it is used. To resolve the
// target of a store through such a re-loaded pointer, the resolver forwards
// through `q` only when ALL of the following hold:
//
// * `q` is never address-taken (no `Lea` of `q` anywhere in the function, no
//   bare `StackSlot(q)` operand, no SIB-index use). Frame addresses enter the
//   value world ONLY via address materialization, so a never-materialized
//   slot has no aliases: its only possible writers are directly
//   `[StackSlot(q)]`-addressed stores, all of which are statically visible.
// * Exactly ONE such direct store to `q` exists in the whole function, it is
//   a full-width (`MovMR`, 8-byte) store at exactly the loaded offset, and it
//   dominates the load being resolved. The forwarded value is then the
//   store's source vreg, resolved recursively.
// ===========================================================================

/// Fuel bound for pointer-chain resolution (copies + leas + forwarding hops).
const FRAME_RESOLVE_FUEL: u32 = 16;

/// Byte width of the loads the invariant-load tier will consider.
///
/// Deliberately excludes:
/// * `MovdqaRM` — traps on unaligned addresses; hoisting may execute it
///   speculatively, so only trap-free opcodes are admitted.
/// * `MovRMSib` — SIB-indexed loads vary with the index by construction.
/// * `MovRipRel`/`Pop`/flag-writing RM forms (`AddRM`, `CmpRM`, ...) — not
///   plain stack-slot value loads.
fn invariant_load_width(opcode: X86Opcode) -> Option<i64> {
    use X86Opcode::*;
    match opcode {
        MovRM8 => Some(1),
        MovRM16 => Some(2),
        MovRM32 => Some(4),
        MovRM => Some(8),
        MovssRM => Some(4),
        MovsdRM => Some(8),
        MovdquRM => Some(16),
        _ => None,
    }
}

/// Plain stores the loop-store scan can attribute to a stack slot. Anything
/// that writes memory and is NOT in this set (Push, StackAlloc, Xchg,
/// Cmpxchg, CAS loops, SIB stores, ...) disables the load tier for the loop.
fn plain_store_width(opcode: X86Opcode) -> Option<i64> {
    use X86Opcode::*;
    match opcode {
        MovMR8 => Some(1),
        MovMR16 => Some(2),
        MovMR32 => Some(4),
        MovMR => Some(8),
        MovssMR => Some(4),
        MovsdMR => Some(8),
        MovdquMR | MovdqaMR => Some(16),
        _ => None,
    }
}

/// Per-loop facts backing the invariant-load tier. Positions go stale on
/// splice, so this is computed fresh for each loop and consumed before that
/// loop's hoist is materialized.
struct LoadTierAnalysis {
    /// Slots written by at least one in-loop store (slot-granular).
    stored_slots: HashSet<u32>,
    /// Slots whose address is ever materialized (function-wide).
    escaped_slots: HashSet<u32>,
    /// Whole-function def sites (only meaningful for single-def vregs).
    def_sites: HashMap<VReg, (Block, usize)>,
    /// Whole-function directly `[StackSlot]`-addressed stores, per slot.
    direct_slot_stores: HashMap<u32, Vec<(Block, usize)>>,
}

impl LoadTierAnalysis {
    /// Analyze `lp` for load hoisting. Returns `None` (tier disabled — hoist
    /// nothing) unless every memory-writing instruction in the loop is a plain
    /// store to a resolvable fixed stack slot and the loop is free of calls,
    /// fences, atomics, and volatile accesses.
    fn compute(
        func: &X86ISelFunction,
        lp: &NaturalLoop,
        def_counts: &HashMap<VReg, usize>,
        idom: &HashMap<Block, Block>,
    ) -> Option<Self> {
        let def_sites = build_def_sites(func);
        let escaped_slots = compute_escaped_slots(func);
        let direct_slot_stores = build_direct_slot_stores(func);

        let mut analysis = LoadTierAnalysis {
            stored_slots: HashSet::new(),
            escaped_slots,
            def_sites,
            direct_slot_stores,
        };

        // Scan every instruction of the loop body. Any single instruction we
        // cannot account for disables the tier for the whole loop.
        let mut stored_slots: HashSet<u32> = HashSet::new();
        for block_id in &func.block_order {
            if !lp.body.contains(block_id) {
                continue;
            }
            let block = func.blocks.get(block_id)?;
            for inst in &block.insts {
                // Atomic/volatile/fence lowering carriers order memory; a
                // hoisted load must never move across one.
                if inst.proof_origin.is_some() {
                    return None;
                }
                let effect = x86_inst_effect(inst);
                if matches!(effect, MemoryEffect::Call) || inst.flags.is_call() {
                    return None;
                }
                if effect.writes_memory() {
                    let slot = resolve_plain_store_slot(func, inst, def_counts, idom, &analysis)?;
                    stored_slots.insert(slot);
                }
            }
        }

        analysis.stored_slots = stored_slots;
        Some(analysis)
    }
}

/// Resolve the stack slot written by an in-loop store, or `None` if the store
/// cannot be attributed to a fixed slot (which disables the tier).
fn resolve_plain_store_slot(
    func: &X86ISelFunction,
    inst: &X86ISelInst,
    def_counts: &HashMap<VReg, usize>,
    idom: &HashMap<Block, Block>,
    analysis: &LoadTierAnalysis,
) -> Option<u32> {
    let width = plain_store_width(inst.opcode)?;
    // Plain stores are `[mem], src`.
    let mem = inst.operands.first()?;
    let (slot, off) = match mem {
        X86ISelOperand::MemAddr { base, disp } => match base.as_ref() {
            X86ISelOperand::StackSlot(s) => (*s, i64::from(*disp)),
            X86ISelOperand::VReg(r) => {
                let (s, o) = resolve_frame_address(
                    func,
                    *r,
                    def_counts,
                    idom,
                    analysis,
                    FRAME_RESOLVE_FUEL,
                )?;
                (s, o.checked_add(i64::from(*disp))?)
            }
            _ => return None,
        },
        _ => return None,
    };
    // The written slot must be a real fixed-size frame slot AND the access
    // must be fully in bounds of it: the slot-granular disjointness argument
    // needs the store to be physically unable to cross into a neighboring
    // slot, and we prove that here rather than lean on out-of-bounds stores
    // being source-level UB.
    let info: &StackSlotInfo = func.stack_slots.get(slot as usize)?;
    if info.allocation != StackSlotAllocationKind::Fixed {
        return None;
    }
    if off < 0 || off.checked_add(width)? > i64::from(info.size) {
        return None;
    }
    Some(slot)
}

/// Resolve the frame address held in `v` to `(slot, byte offset)`, walking
/// single-def `MovRR` copies, `Lea` address arithmetic, and one-hop
/// store-to-load forwarding through non-escaped slots. Returns `None` when
/// the value cannot be proven to be a specific frame address.
fn resolve_frame_address(
    func: &X86ISelFunction,
    v: VReg,
    def_counts: &HashMap<VReg, usize>,
    idom: &HashMap<Block, Block>,
    analysis: &LoadTierAnalysis,
    fuel: u32,
) -> Option<(u32, i64)> {
    if fuel == 0 {
        return None;
    }
    // Multi-def vregs are path-sensitive carriers, not values.
    if def_counts.get(&v).copied().unwrap_or(0) != 1 {
        return None;
    }
    let &(block_id, idx) = analysis.def_sites.get(&v)?;
    let inst = func.blocks.get(&block_id)?.insts.get(idx)?;
    // Defensive: the recorded def site must actually define `v` at operand 0.
    match inst.operands.first() {
        Some(X86ISelOperand::VReg(d)) if *d == v => {}
        _ => return None,
    }

    match inst.opcode {
        X86Opcode::MovRR => match inst.operands.get(1)? {
            X86ISelOperand::VReg(src) => {
                resolve_frame_address(func, *src, def_counts, idom, analysis, fuel - 1)
            }
            _ => None,
        },
        X86Opcode::Lea => match inst.operands.get(1)? {
            X86ISelOperand::MemAddr { base, disp } => match base.as_ref() {
                X86ISelOperand::StackSlot(s) => Some((*s, i64::from(*disp))),
                X86ISelOperand::VReg(r) => {
                    let (s, off) =
                        resolve_frame_address(func, *r, def_counts, idom, analysis, fuel - 1)?;
                    Some((s, off.checked_add(i64::from(*disp))?))
                }
                _ => None,
            },
            _ => None,
        },
        X86Opcode::MovRM => {
            // Pointer-width re-load of a celled pointer: resolve the loaded
            // slot, then forward through it.
            if inst.proof_origin.is_some() {
                return None;
            }
            let (q, qoff) = match inst.operands.get(1)? {
                X86ISelOperand::MemAddr { base, disp } => match base.as_ref() {
                    X86ISelOperand::StackSlot(s) => (*s, i64::from(*disp)),
                    X86ISelOperand::VReg(r) => {
                        let (s, off) =
                            resolve_frame_address(func, *r, def_counts, idom, analysis, fuel - 1)?;
                        (s, off.checked_add(i64::from(*disp))?)
                    }
                    _ => return None,
                },
                _ => return None,
            };
            forward_pointer_through_slot(
                func,
                q,
                qoff,
                (block_id, idx),
                def_counts,
                idom,
                analysis,
                fuel - 1,
            )
        }
        _ => None,
    }
}

/// One-hop store-to-load forwarding: the pointer value loaded from
/// `[slot q + qoff]` equals the source of the unique dominating full-width
/// direct store to that location, provided nothing else can write `q`.
#[allow(clippy::too_many_arguments)]
fn forward_pointer_through_slot(
    func: &X86ISelFunction,
    q: u32,
    qoff: i64,
    load_site: (Block, usize),
    def_counts: &HashMap<VReg, usize>,
    idom: &HashMap<Block, Block>,
    analysis: &LoadTierAnalysis,
    fuel: u32,
) -> Option<(u32, i64)> {
    let info: &StackSlotInfo = func.stack_slots.get(q as usize)?;
    if info.allocation != StackSlotAllocationKind::Fixed {
        return None;
    }
    // The forwarded pointer-width location must be fully inside the cell.
    if qoff < 0 || qoff.checked_add(8)? > i64::from(info.size) {
        return None;
    }
    // A never-address-taken slot has no aliases: frame addresses enter the
    // value world only via address materialization (`Lea`), so the only
    // possible writers are the directly `[StackSlot(q)]`-addressed stores
    // collected below.
    if analysis.escaped_slots.contains(&q) {
        return None;
    }
    let stores = analysis.direct_slot_stores.get(&q)?;
    if stores.len() != 1 {
        return None;
    }
    let (store_block, store_idx) = stores[0];
    let store = func.blocks.get(&store_block)?.insts.get(store_idx)?;
    if store.proof_origin.is_some() {
        return None;
    }
    // Full pointer width at exactly the loaded offset — no partial overlap.
    if store.opcode != X86Opcode::MovMR {
        return None;
    }
    let (X86ISelOperand::MemAddr { base, disp }, Some(X86ISelOperand::VReg(w))) =
        (store.operands.first()?, store.operands.get(1))
    else {
        return None;
    };
    match base.as_ref() {
        X86ISelOperand::StackSlot(s) if *s == q => {}
        _ => return None,
    }
    if i64::from(*disp) != qoff {
        return None;
    }
    // The store must have executed before the load on every path.
    if !site_dominates((store_block, store_idx), load_site, idom) {
        return None;
    }
    resolve_frame_address(func, *w, def_counts, idom, analysis, fuel)
}

/// Does instruction site `a` dominate site `b`?
fn site_dominates(a: (Block, usize), b: (Block, usize), idom: &HashMap<Block, Block>) -> bool {
    if a.0 == b.0 {
        return a.1 < b.1;
    }
    // Strict block dominance: a.0 dominates b.0 and they differ.
    dominates(a.0, b.0, idom)
}

/// The invariant-load candidate gate. Returns the destination vreg iff `inst`
/// is a plain, effect-free, provably in-bounds fixed-slot load whose slot is
/// disjoint from every slot stored in the loop, and whose address operands
/// are available at the preheader.
fn hoistable_invariant_load(
    func: &X86ISelFunction,
    inst: &X86ISelInst,
    tier: &LoadTierAnalysis,
    loop_defs: &HashMap<VReg, Block>,
    invariant_vregs: &HashSet<VReg>,
    def_counts: &HashMap<VReg, usize>,
    idom: &HashMap<Block, Block>,
) -> Option<VReg> {
    let width = invariant_load_width(inst.opcode)?;
    // Never move an atomic/volatile lowering carrier.
    if inst.proof_origin.is_some() {
        return None;
    }
    let flags = inst.flags;
    if flags.is_call() || flags.is_branch() || flags.is_terminator() || flags.is_return() {
        return None;
    }
    if flags.has_side_effects() || flags.writes_memory() {
        return None;
    }
    if x86_writes_flags(inst.opcode) || x86_reads_flags(inst.opcode) {
        return None;
    }
    if inst.operands.len() != 2 {
        return None;
    }
    // Destination: single-def vreg (same SSA discipline as the pure tier).
    let dst = match inst.operands.first() {
        Some(X86ISelOperand::VReg(d)) => *d,
        _ => return None,
    };
    if def_counts.get(&dst).copied().unwrap_or(0) != 1 {
        return None;
    }

    // Address: a fixed stack slot plus a static offset.
    let (slot, off) = match inst.operands.get(1)? {
        X86ISelOperand::MemAddr { base, disp } => match base.as_ref() {
            X86ISelOperand::StackSlot(s) => (*s, i64::from(*disp)),
            X86ISelOperand::VReg(r) => {
                // The base register must remain available (and unchanged) at
                // the preheader insertion point: defined outside the loop, or
                // itself proven invariant and hoisted ahead of this load.
                if !is_vreg_loop_invariant(*r, loop_defs, invariant_vregs, def_counts) {
                    return None;
                }
                let (s, o) =
                    resolve_frame_address(func, *r, def_counts, idom, tier, FRAME_RESOLVE_FUEL)?;
                (s, o.checked_add(i64::from(*disp))?)
            }
            _ => return None,
        },
        _ => return None,
    };

    // Provably non-trapping: fully in bounds of a fixed-size frame slot.
    let info: &StackSlotInfo = func.stack_slots.get(slot as usize)?;
    if info.allocation != StackSlotAllocationKind::Fixed {
        return None;
    }
    if off < 0 || off.checked_add(width)? > i64::from(info.size) {
        return None;
    }

    // Invariant: nothing in the loop writes this slot.
    if tier.stored_slots.contains(&slot) {
        return None;
    }

    Some(dst)
}

/// Whole-function def sites. Only consulted for single-def vregs; for
/// multi-def vregs the recorded (last) site is never used because callers
/// check `def_counts` first.
fn build_def_sites(func: &X86ISelFunction) -> HashMap<VReg, (Block, usize)> {
    let mut sites: HashMap<VReg, (Block, usize)> = HashMap::new();
    for block_id in &func.block_order {
        let Some(block) = func.blocks.get(block_id) else {
            continue;
        };
        for (idx, inst) in block.insts.iter().enumerate() {
            if let Some(def) = defined_vreg(inst) {
                sites.insert(def, (*block_id, idx));
            }
        }
    }
    sites
}

/// Slots whose address is ever materialized into the value world. A slot
/// referenced only as the direct base of load/store memory operands never has
/// its address taken; `Lea` of the slot (or any non-memory-access appearance)
/// escapes it. Conservative: unknown shapes escape.
fn compute_escaped_slots(func: &X86ISelFunction) -> HashSet<u32> {
    let mut escaped: HashSet<u32> = HashSet::new();
    for block_id in &func.block_order {
        let Some(block) = func.blocks.get(block_id) else {
            continue;
        };
        for inst in &block.insts {
            let effect = x86_inst_effect(inst);
            // `Call` reads+writes memory but a `[StackSlot]` operand on e.g.
            // CallM is still an access of the slot's contents, not an address
            // materialization; the call itself disables the tier via the
            // loop scan when inside the loop, and cannot write a non-escaped
            // slot from outside the visible store set.
            let is_memory_access = effect.reads_memory() || effect.writes_memory();
            for operand in &inst.operands {
                mark_escaping_slots(operand, is_memory_access, &mut escaped);
            }
        }
    }
    escaped
}

fn mark_escaping_slots(
    operand: &X86ISelOperand,
    is_memory_access: bool,
    escaped: &mut HashSet<u32>,
) {
    match operand {
        // A bare slot operand is an address use (frame-address
        // materialization or unknown pseudo plumbing): escape.
        X86ISelOperand::StackSlot(s) => {
            escaped.insert(*s);
        }
        X86ISelOperand::MemAddr { base, .. } => match base.as_ref() {
            X86ISelOperand::StackSlot(s) => {
                // `Lea dst, [slot]` (memory-pure) materializes the address;
                // `mov dst, [slot]` / `mov [slot], src` merely access it.
                if !is_memory_access {
                    escaped.insert(*s);
                }
            }
            other => mark_escaping_slots(other, is_memory_access, escaped),
        },
        X86ISelOperand::SibMemAddr { base, index, .. } => {
            match base.as_ref() {
                X86ISelOperand::StackSlot(s) => {
                    if !is_memory_access {
                        escaped.insert(*s);
                    }
                }
                other => mark_escaping_slots(other, is_memory_access, escaped),
            }
            // A slot as the *index* is nonsensical address plumbing: escape.
            if let X86ISelOperand::StackSlot(s) = index.as_ref() {
                escaped.insert(*s);
            }
        }
        _ => {}
    }
}

/// Whole-function directly `[StackSlot]`-addressed stores, per slot. These are
/// the only possible writers of a non-escaped slot.
fn build_direct_slot_stores(func: &X86ISelFunction) -> HashMap<u32, Vec<(Block, usize)>> {
    let mut stores: HashMap<u32, Vec<(Block, usize)>> = HashMap::new();
    for block_id in &func.block_order {
        let Some(block) = func.blocks.get(block_id) else {
            continue;
        };
        for (idx, inst) in block.insts.iter().enumerate() {
            if !x86_inst_effect(inst).writes_memory() {
                continue;
            }
            for operand in &inst.operands {
                let slot = match operand {
                    X86ISelOperand::MemAddr { base, .. } => match base.as_ref() {
                        X86ISelOperand::StackSlot(s) => Some(*s),
                        _ => None,
                    },
                    X86ISelOperand::SibMemAddr { base, .. } => match base.as_ref() {
                        X86ISelOperand::StackSlot(s) => Some(*s),
                        _ => None,
                    },
                    _ => None,
                };
                if let Some(s) = slot {
                    stores.entry(s).or_default().push((*block_id, idx));
                }
            }
        }
    }
    stores
}

// ===========================================================================
// Def maps
// ===========================================================================

fn build_def_counts(func: &X86ISelFunction) -> HashMap<VReg, usize> {
    let mut counts: HashMap<VReg, usize> = HashMap::new();
    for block_id in &func.block_order {
        let Some(block) = func.blocks.get(block_id) else {
            continue;
        };
        for inst in &block.insts {
            if let Some(def) = defined_vreg(inst) {
                *counts.entry(def).or_insert(0) += 1;
            }
        }
    }
    counts
}

fn build_loop_defs(func: &X86ISelFunction, body: &HashSet<Block>) -> HashMap<VReg, Block> {
    let mut defs: HashMap<VReg, Block> = HashMap::new();
    for block_id in &func.block_order {
        if !body.contains(block_id) {
            continue;
        }
        let Some(block) = func.blocks.get(block_id) else {
            continue;
        };
        for inst in &block.insts {
            if let Some(def) = defined_vreg(inst) {
                defs.insert(def, *block_id);
            }
        }
    }
    defs
}

fn defined_vreg(inst: &X86ISelInst) -> Option<VReg> {
    if !x86_produces_value(inst.opcode) {
        return None;
    }
    // Proof-only guard carriers (TrapBoundsCheckExact etc.) carry the checked
    // vreg in operand[0] but never write a register, so they must not count as
    // defs — otherwise every bounds-checked index copy is multi-def and the
    // single-def invariance gates reject exactly the hot checked loops.
    // Pass-local exclusion; the global x86_produces_value stays untouched.
    if trust_cg_ir::guard_target::classify_x86_carrier(inst.opcode).is_some() {
        return None;
    }
    match inst.operands.first() {
        Some(X86ISelOperand::VReg(v)) => Some(*v),
        _ => None,
    }
}

// ===========================================================================
// CFG / dominators / natural loops — delegated to the shared arch-neutral
// analyses in `crate::mach_view` (predecessor_map / compute_rpo / compute_idom
// / dominates / find_natural_loops, the same dom.rs + loops.rs algorithms
// written once over the MachIrView facade). This pass previously carried a
// full private re-port; only the pass-local `NaturalLoop` cache struct and
// the historical loop-set ORDER contract (see `find_natural_loops` below)
// remain here.
// ===========================================================================

/// A natural loop on the x86 ISel CFG. Pass-local cache struct, filled from
/// [`crate::mach_view::GenericLoop`]; this pass never consumes per-latch
/// information, so `GenericLoop::latches` is dropped in the conversion.
struct NaturalLoop {
    /// Loop header (the back-edge target; the sole in-body successor of the
    /// preheader). Entered from the preheader on the first iteration.
    header: Block,
    body: HashSet<Block>,
    /// Unique non-loop predecessor of the header, if one exists.
    preheader: Option<Block>,
    /// Nesting depth (outermost = 1); larger = more deeply nested.
    depth: u32,
}

/// Immediate dominators via Cooper/Harvey/Kennedy, keyed by block. Entry maps
/// to itself. Thin wrapper over [`crate::mach_view::compute_idom`] — the same
/// algorithm the deleted private re-port mirrored from `dom.rs`, over the RPO
/// from [`crate::mach_view::compute_rpo`] (whose entry block is
/// `block_order[0]`, exactly as before).
fn compute_idom(
    func: &X86ISelFunction,
    preds: &HashMap<Block, Vec<Block>>,
) -> HashMap<Block, Block> {
    let rpo = mach_view::compute_rpo(func);
    mach_view::compute_idom(func, preds, &rpo)
}

/// S4 Region-LICM Stage 1: report every (inner loop, innermost-enclosing outer
/// loop) nesting with its L1–L6 legality verdicts (docs/region-licm-design-
/// 2026-07-16.md). READ-ONLY — no transform. Gated by the caller on
/// `TCG_REGION_LICM_DEBUG`. The verdicts:
///   L1  inner has a preheader inside the outer body
///   L2  every instruction in the inner loop's blocks is memory-Pure
///       (`x86_inst_effect`: no store/load/call — v1 excludes loads entirely)
///   L3  external reads split into OUTER-INVARIANT (no def anywhere in the
///       outer body — legal as-is) vs INIT-PREFIX candidates (defined in the
///       outer body outside the inner loop — must be constant-cluster-hoistable
///       in stage 2); reads with defs OUTSIDE both classifications don't exist
///       (a def is either in outer\inner, in inner, or outside outer).
///   L4  exactly ONE distinct successor outside the inner body (the single
///       exit), and it lies inside the outer body
///   L5  the inner header dominates every outer latch (the region runs on
///       every outer iteration)
///   L6  the outer loop provably runs ≥1 time (`loop_runs_at_least_once` — the
///       pure-call hoist's mini-interpreter, reused verbatim)
fn region_licm_scan(
    func: &X86ISelFunction,
    preds: &HashMap<Block, Vec<Block>>,
    idom: &HashMap<Block, Block>,
    loops: &[NaturalLoop],
) {
    use crate::effects::{MemoryEffect, x86_inst_effect, x86_produces_value};
    for inner in loops {
        // The innermost enclosing outer loop = the smallest strict superset body.
        let Some(outer) = loops
            .iter()
            .filter(|o| o.header != inner.header && inner.body.is_subset(&o.body))
            .min_by_key(|o| o.body.len())
        else {
            continue; // top-level loop — nothing to hoist out of.
        };
        let tag = format!(
            "[region-licm] fn={} inner={:?}({} blocks) outer={:?}({} blocks)",
            func.name,
            inner.header,
            inner.body.len(),
            outer.header,
            outer.body.len()
        );

        // L1: inner preheader present and inside the outer body.
        let l1 = matches!(inner.preheader, Some(p) if outer.body.contains(&p));

        // L2: memory purity of every inner-loop instruction.
        let mut l2_bad: Option<(Block, X86Opcode, MemoryEffect)> = None;
        'l2: for b in &inner.body {
            let Some(bb) = func.blocks.get(b) else {
                continue;
            };
            for i in &bb.insts {
                let e = x86_inst_effect(i);
                if e != MemoryEffect::Pure {
                    l2_bad = Some((*b, i.opcode, e));
                    break 'l2;
                }
            }
        }

        // L4: distinct successors outside the inner body.
        let mut exits: HashSet<Block> = HashSet::new();
        for b in &inner.body {
            let Some(bb) = func.blocks.get(b) else {
                continue;
            };
            for s in &bb.successors {
                if !inner.body.contains(s) {
                    exits.insert(*s);
                }
            }
        }
        let l4 = exits.len() == 1 && exits.iter().all(|e| outer.body.contains(e));

        // L3: external reads. Defs inside the inner body; then every VReg READ
        // in the inner body but not defined there, classified by where its defs
        // live: in outer\inner (init-prefix candidate) vs outside the outer
        // body entirely (outer-invariant).
        let mut inner_defs: HashSet<VReg> = HashSet::new();
        for b in &inner.body {
            let Some(bb) = func.blocks.get(b) else {
                continue;
            };
            for i in &bb.insts {
                if x86_produces_value(i.opcode)
                    && let Some(X86ISelOperand::VReg(d)) = i.operands.first()
                {
                    inner_defs.insert(*d);
                }
            }
        }
        let mut ext_reads: HashSet<VReg> = HashSet::new();
        for b in &inner.body {
            let Some(bb) = func.blocks.get(b) else {
                continue;
            };
            for i in &bb.insts {
                let produces = x86_produces_value(i.opcode);
                for (oi, op) in i.operands.iter().enumerate() {
                    if produces && oi == 0 {
                        continue;
                    }
                    collect_operand_vregs(op, &mut |v| {
                        if !inner_defs.contains(&v) {
                            ext_reads.insert(v);
                        }
                    });
                }
            }
        }
        let mut invariant = 0usize;
        let mut init_prefix = 0usize;
        for v in &ext_reads {
            let mut def_in_outer = false;
            for b in &outer.body {
                if inner.body.contains(b) {
                    continue;
                }
                let Some(bb) = func.blocks.get(b) else {
                    continue;
                };
                for i in &bb.insts {
                    if x86_produces_value(i.opcode)
                        && matches!(i.operands.first(), Some(X86ISelOperand::VReg(d)) if d == v)
                    {
                        def_in_outer = true;
                        break;
                    }
                }
                if def_in_outer {
                    break;
                }
            }
            if def_in_outer {
                init_prefix += 1;
            } else {
                invariant += 1;
            }
        }

        // L5: the inner header dominates every outer latch.
        let latches: Vec<Block> = preds
            .get(&outer.header)
            .map(|v| {
                v.iter()
                    .copied()
                    .filter(|p| outer.body.contains(p))
                    .collect()
            })
            .unwrap_or_default();
        let l5 = !latches.is_empty() && latches.iter().all(|l| dominates(inner.header, *l, idom));

        // L6: the outer loop provably runs at least once.
        let l6 = outer
            .preheader
            .map(|p| loop_runs_at_least_once(func, outer, p, idom))
            .unwrap_or(false);

        let candidate = l1 && l2_bad.is_none() && l4 && l5 && l6;
        eprintln!(
            "{tag} L1={} L2={} L4(exits={})={} L3(ext={}: invariant={}, init-prefix={}) L5={} L6={} => {}",
            l1,
            match &l2_bad {
                None => "pure".to_owned(),
                Some((b, op, e)) => format!("IMPURE({op:?}@{b:?}={e:?})"),
            },
            exits.len(),
            l4,
            ext_reads.len(),
            invariant,
            init_prefix,
            l5,
            l6,
            if candidate { "CANDIDATE" } else { "decline" },
        );
    }
}

/// Retarget every CFG edge `block -> old` to `block -> new` — both the
/// terminator's `Block` operand(s) and the parallel `successors` list. Used by
/// the region-LICM surgery (§4 of the design). No-op if `block` is absent.
fn retarget_block_edge(func: &mut X86ISelFunction, block: Block, old: Block, new: Block) {
    if let Some(bb) = func.blocks.get_mut(&block) {
        for inst in &mut bb.insts {
            for op in &mut inst.operands {
                if let X86ISelOperand::Block(t) = op
                    && *t == old
                {
                    *t = new;
                }
            }
        }
        for s in &mut bb.successors {
            if *s == old {
                *s = new;
            }
        }
    }
}

/// The single VReg an instruction defines, if it is a value-producer whose first
/// operand is a plain VReg (the local convention used by the region scan).
fn region_def_of(inst: &X86ISelInst) -> Option<VReg> {
    if !crate::effects::x86_produces_value(inst.opcode) {
        return None;
    }
    match inst.operands.first() {
        Some(X86ISelOperand::VReg(d)) => Some(*d),
        _ => None,
    }
}

/// Fail-closed VALUE-LEVEL LICM net (X5, x86 lane — closes the documented
/// "x86_licm has NO validation net" gap): after any hoist into `preheader`,
/// verify no instruction READS a VReg that is DEFINED LATER in that same block —
/// a use-before-def the motion would have introduced. Mirrors the aarch64
/// `licm.rs::verify_preheader_defs_precede_uses`.
///
/// SOUND + false-positive-free by restricting to SINGLE-DEF VRegs: the X86ISel IR
/// is not strict SSA here (block-argument copies reuse a VReg along paths), so a
/// VReg defined BOTH in a dominating block AND the preheader could legitimately
/// read the dominating def before a redef. A `def_counts == 1` VReg has its one
/// def as its ONLY def, so any occurrence strictly before that def-site is an
/// unambiguous use-before-def — exactly the class LICM ever hoists (the
/// invariance gates already require `def_counts == 1`). Panics on violation: a
/// transform bug must fail closed, never ship a miscompiled hoist.
fn verify_preheader_defs_precede_uses(
    func: &X86ISelFunction,
    preheader: Block,
    def_counts: &HashMap<VReg, usize>,
) {
    let insts = &func
        .blocks
        .get(&preheader)
        .expect("preheader block exists")
        .insts;
    let mut def_pos: HashMap<VReg, usize> = HashMap::new();
    for (i, inst) in insts.iter().enumerate() {
        if let Some(d) = region_def_of(inst)
            && def_counts.get(&d).copied().unwrap_or(0) == 1
        {
            def_pos.entry(d).or_insert(i); // earliest def wins
        }
    }
    for (i, inst) in insts.iter().enumerate() {
        for op in &inst.operands {
            // Address operands are recursive: `MemAddr` carries a base and
            // `SibMemAddr` carries both a base and an index.  Looking only for a
            // top-level `VReg` leaves exactly the address-producing LICM class
            // (`Lea`/`LeaSib`, plus any admitted load form) outside the X5 net.
            collect_operand_vregs(op, &mut |v| {
                if let Some(&dp) = def_pos.get(&v) {
                    assert!(
                        i >= dp,
                        "x86 LICM preheader use-before-def in fn `{}`: single-def vreg {v:?} used at \
                         index {i} but defined at index {dp} in preheader {preheader:?} — a hoist \
                         reordered a def below its use (fail-closed)",
                        func.name
                    );
                }
            });
        }
    }
}

/// S4 Region-LICM — Stage 2 (instruction-cluster hoist, design §8 v2). Hoist an
/// entire OUTER-invariant inner loop out of its enclosing outer loop so it runs
/// ONCE instead of every outer iteration. Gated `TCG_REGION_LICM` (default-OFF):
/// this is a no-TV-net CFG surgery, so it ships disabled until the
/// `.fuzz-regionlicm/` corpus certifies a default-ON flip (design §5-6).
///
/// Handles the shape rustc emits (design §1): the inner loop's carried-register
/// INIT constants and the outer-carried SNAPSHOTS are FUSED into one inner
/// preheader block `ip`. v1's whole-block move was inert because moving `ip`
/// would compute the per-iteration snapshots once (a miscompile). v2 SPLITS
/// `ip`: the INIT cluster (the inner loop's live-in definitions) moves into a
/// synthesized preheader that runs once before the outer loop, the inner-loop
/// blocks move with it, and the SNAPSHOTS stay in `ip` reading the current
/// outer-iteration values.
///
/// SOUNDNESS (all must hold; any failure DECLINES to the correct original):
///   L1  inner nested in outer, `ip = inner.preheader` inside outer.body.
///   L2  every inner-loop instruction is memory-Pure (no load/store/call).
///   L4  the inner loop has exactly ONE exit block, inside outer.body.
///   L5  inner.header dominates every outer latch (region runs each iteration).
///   L6  the outer loop provably runs >= 1 time (`loop_runs_at_least_once`).
///   P   outer.preheader exists and ends in an explicit `Jmp outer.header`;
///       `ip` ends in an explicit `Jmp inner.header`. (Explicit terminators →
///       layout-order independence for the moved blocks.)
///   INIT  every inner live-in is EITHER defined in `ip` by a `MovRI`
///       (constant) / `MovRR`-of-outer-invariant (the INIT cluster), OR itself
///       outer-invariant (no def anywhere in outer.body).
///   SEP  no non-INIT instruction in `ip` reads an INIT def (the split is clean).
///   INV  no register defined in the REGION (INIT defs ∪ inner defs) is
///       redefined ELSEWHERE in outer.body. With L2 (pure) + INIT (closed
///       inputs) this makes every region def OUTER-INVARIANT, so an outside read
///       sees the identical value whether the region runs once (hoisted) or
///       every iteration (original) — the equivalence in design §3.
fn region_licm_hoist(
    func: &mut X86ISelFunction,
    loops: &[NaturalLoop],
    preds: &HashMap<Block, Vec<Block>>,
    idom: &HashMap<Block, Block>,
) -> bool {
    let dbg = std::env::var_os("TCG_REGION_LICM_DEBUG").is_some();
    macro_rules! decline {
        ($($a:tt)*) => {{ if dbg { eprintln!("[region-licm-hoist] decline: {}", format!($($a)*)); } }};
    }

    for inner in loops {
        // Smallest strictly-enclosing outer loop.
        let Some(outer) = loops
            .iter()
            .filter(|o| o.header != inner.header && inner.body.is_subset(&o.body))
            .min_by_key(|o| o.body.len())
        else {
            continue;
        };

        // L1: preheader present, inside the outer body.
        let Some(ip) = inner.preheader.filter(|p| outer.body.contains(p)) else {
            continue;
        };
        // P: outer preheader present.
        let Some(op_pre) = outer.preheader else {
            continue;
        };

        // L2: every inner-loop instruction is memory-Pure.
        let l2_ok = inner.body.iter().all(|b| {
            func.blocks
                .get(b)
                .map(|bb| {
                    bb.insts
                        .iter()
                        .all(|i| crate::effects::x86_inst_effect(i).is_pure())
                })
                .unwrap_or(false)
        });
        if !l2_ok {
            decline!("inner {:?} not pure", inner.header);
            continue;
        }

        // L4: exactly one exit block, inside the outer body.
        let mut exits: HashSet<Block> = HashSet::new();
        for b in &inner.body {
            if let Some(bb) = func.blocks.get(b) {
                for s in &bb.successors {
                    if !inner.body.contains(s) {
                        exits.insert(*s);
                    }
                }
            }
        }
        if exits.len() != 1 {
            continue;
        }
        let exit_blk = *exits.iter().next().unwrap();
        if !outer.body.contains(&exit_blk) {
            continue;
        }

        // L5: inner.header dominates every outer latch.
        let latches: Vec<Block> = preds
            .get(&outer.header)
            .map(|v| {
                v.iter()
                    .copied()
                    .filter(|p| outer.body.contains(p))
                    .collect()
            })
            .unwrap_or_default();
        if latches.is_empty() || !latches.iter().all(|l| dominates(inner.header, *l, idom)) {
            continue;
        }

        // L6: outer runs >= 1 time.
        if !loop_runs_at_least_once(func, outer, op_pre, idom) {
            decline!("outer {:?} not proven >=1-trip", outer.header);
            continue;
        }

        // P: explicit unconditional Jmp terminators on `op_pre -> outer.header`
        // and `ip -> inner.header`.
        let ends_with_jmp_to = |blk: Block, target: Block| -> bool {
            func.blocks.get(&blk).and_then(|bb| bb.insts.last()).is_some_and(|t| {
                t.opcode == X86Opcode::Jmp
                    && matches!(t.operands.first(), Some(X86ISelOperand::Block(b)) if *b == target)
            })
        };
        if !ends_with_jmp_to(op_pre, outer.header) {
            decline!("outer preheader {:?} lacks explicit Jmp to header", op_pre);
            continue;
        }
        if !ends_with_jmp_to(ip, inner.header) {
            decline!(
                "inner preheader {:?} lacks explicit Jmp to inner header",
                ip
            );
            continue;
        }

        // Region defs / inner live-ins.
        let mut inner_defs: HashSet<VReg> = HashSet::new();
        for b in &inner.body {
            if let Some(bb) = func.blocks.get(b) {
                for i in &bb.insts {
                    if let Some(d) = region_def_of(i) {
                        inner_defs.insert(d);
                    }
                }
            }
        }
        let mut inner_reads: HashSet<VReg> = HashSet::new();
        for b in &inner.body {
            if let Some(bb) = func.blocks.get(b) {
                for i in &bb.insts {
                    let produces = crate::effects::x86_produces_value(i.opcode);
                    for (oi, op) in i.operands.iter().enumerate() {
                        if produces && oi == 0 {
                            continue;
                        }
                        collect_operand_vregs(op, &mut |v| {
                            if !inner_defs.contains(&v) {
                                inner_reads.insert(v);
                            }
                        });
                    }
                }
            }
        }

        // A vreg is OUTER-INVARIANT iff it has no def anywhere in outer.body.
        let defined_in_outer = |v: VReg| -> bool {
            outer.body.iter().any(|b| {
                func.blocks
                    .get(b)
                    .map(|bb| bb.insts.iter().any(|i| region_def_of(i) == Some(v)))
                    .unwrap_or(false)
            })
        };

        // The INIT cluster = the transitive backward closure, WITHIN `ip`, of
        // the inner loop's live-in / carried-register initializers. rustc lowers
        // these as a COPY CHAIN (`carried = MovRR const; const = MovRI imm`), so
        // a relocatable INIT source may itself be another INIT-cluster def in
        // `ip`; only a source defined in the outer body OUTSIDE `ip` (a real
        // outer-varying value, e.g. a snapshot's `acc`/`rep`) makes an
        // instruction non-invariant and declines the hoist.
        let Some(ip_blk) = func.blocks.get(&ip) else {
            continue;
        };
        let mut ip_def_idx: HashMap<VReg, usize> = HashMap::new();
        for (idx, inst) in ip_blk.insts.iter().enumerate() {
            if let Some(d) = region_def_of(inst) {
                ip_def_idx.entry(d).or_insert(idx);
            }
        }
        // Seed: `ip` defs of a vreg the inner body reads or carries (redefines).
        let mut init_set: HashSet<usize> = HashSet::new();
        let mut init_defs: HashSet<VReg> = HashSet::new();
        let mut worklist: Vec<usize> = Vec::new();
        for (idx, inst) in ip_blk.insts.iter().enumerate() {
            if let Some(d) = region_def_of(inst)
                && (inner_reads.contains(&d) || inner_defs.contains(&d))
            {
                worklist.push(idx);
            }
        }
        let mut init_bad = false;
        while let Some(idx) = worklist.pop() {
            if !init_set.insert(idx) {
                continue;
            }
            let inst = &ip_blk.insts[idx];
            let self_def = region_def_of(inst);
            let relocatable = match inst.opcode {
                X86Opcode::MovRI
                | X86Opcode::MovRR
                | X86Opcode::MovRR32
                | X86Opcode::Movzx
                | X86Opcode::MovzxW => true,
                // Self-XOR zeroing idiom (`xor d,d` → constant 0): value- and
                // flag-safe to relocate (RFLAGS dead into the inner header's
                // compare; no outer-loop instruction reads them).
                X86Opcode::XorRR => matches!(
                    inst.operands.as_slice(),
                    [X86ISelOperand::VReg(a), X86ISelOperand::VReg(b), X86ISelOperand::VReg(c)]
                        if a == b && b == c
                ),
                _ => false,
            };
            if !relocatable {
                init_bad = true;
                if dbg {
                    eprintln!(
                        "[region-licm-hoist]   non-relocatable INIT {:?} ops={:?}",
                        inst.opcode, inst.operands
                    );
                }
                break;
            }
            let mut src_bad = false;
            for (oi, op) in inst.operands.iter().enumerate() {
                if oi == 0 {
                    continue; // destination
                }
                collect_operand_vregs(op, &mut |s| {
                    if Some(s) == self_def {
                        return; // self-reference (the xor d,d idiom)
                    }
                    if let Some(&j) = ip_def_idx.get(&s) {
                        worklist.push(j); // chained INIT def within ip
                    } else if defined_in_outer(s) {
                        src_bad = true; // outer-varying source → not invariant
                    }
                });
            }
            if src_bad {
                init_bad = true;
                break;
            }
            if let Some(d) = self_def {
                init_defs.insert(d);
            }
        }
        let mut init_idx: Vec<usize> = init_set.iter().copied().collect();
        init_idx.sort_unstable();
        if dbg && let Some(bb) = func.blocks.get(&ip) {
            eprintln!(
                "[region-licm-hoist]   ip {:?} dump ({} insts):",
                ip,
                bb.insts.len()
            );
            for (i, inst) in bb.insts.iter().enumerate() {
                eprintln!("      [{i}] {:?} {:?}", inst.opcode, inst.operands);
            }
        }
        if init_bad {
            decline!("ip {:?} has a non-relocatable inner-live-in def", ip);
            continue;
        }

        // Every inner live-in must be an INIT def or outer-invariant.
        if inner_reads
            .iter()
            .any(|v| !init_defs.contains(v) && defined_in_outer(*v))
        {
            decline!(
                "inner {:?} reads an outer-varying value not in the INIT cluster",
                inner.header
            );
            continue;
        }

        // SEP: no non-INIT instruction in `ip` may read an INIT def.
        let mut sep_bad = false;
        for (idx, inst) in ip_blk.insts.iter().enumerate() {
            if init_set.contains(&idx) {
                continue;
            }
            let produces = crate::effects::x86_produces_value(inst.opcode);
            for (oi, op) in inst.operands.iter().enumerate() {
                if produces && oi == 0 {
                    continue;
                }
                collect_operand_vregs(op, &mut |v| {
                    if init_defs.contains(&v) {
                        sep_bad = true;
                    }
                });
            }
        }
        if sep_bad {
            decline!("ip {:?} split not clean (REST reads an INIT def)", ip);
            continue;
        }

        // INV: no region def (INIT defs ∪ inner defs) is redefined elsewhere in
        // outer.body (outside the INIT cluster and inner.body).
        let region_defs: HashSet<VReg> = init_defs.union(&inner_defs).copied().collect();
        let mut inv_bad = false;
        for b in &outer.body {
            if inner.body.contains(b) {
                continue;
            }
            if let Some(bb) = func.blocks.get(b) {
                for (idx, inst) in bb.insts.iter().enumerate() {
                    if *b == ip && init_set.contains(&idx) {
                        continue; // the INIT defs themselves
                    }
                    if let Some(d) = region_def_of(inst)
                        && region_defs.contains(&d)
                    {
                        inv_bad = true;
                    }
                }
            }
        }
        if inv_bad {
            decline!("a region def is redefined elsewhere in the outer loop");
            continue;
        }

        // ---- All legality holds — perform the surgery. -------------------
        // Extract the INIT instructions out of `ip` (high-index-first).
        let mut init_insts: Vec<X86ISelInst> = Vec::with_capacity(init_idx.len());
        {
            let ipb = func.blocks.get_mut(&ip).expect("ip exists");
            let mut idxs = init_idx.clone();
            idxs.sort_unstable_by(|a, b| b.cmp(a));
            // collect in ORIGINAL order first
            for &i in &init_idx {
                init_insts.push(ipb.insts[i].clone());
            }
            for i in idxs {
                ipb.insts.remove(i);
            }
        }

        // Synthesize the run-once preheader `sp` = INIT cluster + Jmp(inner.header).
        let sp = Block(func.block_order.iter().map(|b| b.0).max().unwrap_or(0) + 1);
        let mut sp_insts = init_insts;
        sp_insts.push(X86ISelInst::new(
            X86Opcode::Jmp,
            vec![X86ISelOperand::Block(inner.header)],
        ));
        func.blocks.insert(
            sp,
            trust_cg_lower::X86ISelBlock {
                insts: sp_insts,
                successors: vec![inner.header],
            },
        );

        // Edge surgery:
        //   op_pre -> outer.header      becomes  op_pre -> sp
        //   ip     -> inner.header      becomes  ip     -> exit_blk
        //   inner.header -> exit_blk    becomes  inner.header -> outer.header
        retarget_block_edge(func, op_pre, outer.header, sp);
        retarget_block_edge(func, ip, inner.header, exit_blk);
        retarget_block_edge(func, inner.header, exit_blk, outer.header);

        // Layout: pull the inner-loop blocks out and place [sp, <inner blocks in
        // their prior relative order>] immediately after `op_pre`. All moved
        // blocks carry explicit terminators, so only fall-through elision (a
        // perf detail) depends on order.
        let inner_seq: Vec<Block> = func
            .block_order
            .iter()
            .copied()
            .filter(|b| inner.body.contains(b))
            .collect();
        func.block_order.retain(|b| !inner.body.contains(b));
        let at = func
            .block_order
            .iter()
            .position(|b| *b == op_pre)
            .map(|p| p + 1)
            .unwrap_or(func.block_order.len());
        let mut insert_seq = vec![sp];
        insert_seq.extend(inner_seq);
        for (off, b) in insert_seq.into_iter().enumerate() {
            func.block_order.insert(at + off, b);
        }

        if dbg {
            eprintln!(
                "[region-licm-hoist] HOISTED inner {:?} out of outer {:?} (sp={:?}, {} INIT insts, exit={:?})",
                inner.header,
                outer.header,
                sp,
                init_defs.len(),
                exit_blk
            );
        }
        return true; // one hoist per invocation; the pass re-runs.
    }
    false
}

/// Invoke `f` on every `VReg` referenced by `op` (incl. memory-address bases /
/// indices). Stage-1 helper for the region scan's read collection.
fn collect_operand_vregs(op: &X86ISelOperand, f: &mut impl FnMut(VReg)) {
    match op {
        X86ISelOperand::VReg(v) => f(*v),
        X86ISelOperand::MemAddr { base, .. } => collect_operand_vregs(base, f),
        X86ISelOperand::SibMemAddr { base, index, .. } => {
            collect_operand_vregs(base, f);
            collect_operand_vregs(index, f);
        }
        _ => {}
    }
}

/// `a` dominates `b` iff walking `b` up the idom chain reaches `a` (reflexive).
/// Thin wrapper over [`crate::mach_view::dominates`].
fn dominates(a: Block, b: Block, idom: &HashMap<Block, Block>) -> bool {
    mach_view::dominates(a, b, idom)
}

/// Identify natural loops by back-edges (latch -> header where header dominates
/// latch), compute each body via reverse reachability, find a natural preheader,
/// and assign nesting depth. Merges multiple back-edges into one loop per header.
///
/// Discovery is delegated to [`crate::mach_view::find_natural_loops`] — the
/// same back-edge scan / reverse-reachability body / unique-preheader /
/// strict-superset depth computation this pass used to re-port privately.
///
/// ORDER contract: the loop set is returned SORTED BY HEADER BLOCK INDEX,
/// exactly as `mach_view` produces it.
///
/// 🛑 THIS REPLACES A DELIBERATE `HashMap` ROUND-TRIP, AND THE REASONING BEHIND
/// THAT ROUND-TRIP WAS WRONG. It previously re-keyed the sorted result through
/// a per-call `HashMap` and returned `into_values()`, documented as keeping the
/// analysis swap "behavior-preserving" by giving consumers "the same
/// (unspecified) order-semantics class as before the migration".
///
/// You cannot preserve behaviour by preserving a RANDOMLY SEEDED order.
/// `std::collections::HashMap`'s hasher is seeded per PROCESS, so that
/// round-trip did not pin an order — it re-randomised the order on every
/// compile. The observable consequence: this pass hoists into preheaders in
/// loop-processing order, so the emitted instruction order, then register
/// allocation, then the BYTES varied between two compiles of identical input.
/// `v2_memfill` built two different (both valid) binaries roughly 40/60 across
/// runs, which made its runtime look like +/-79% "measurement noise" and moved
/// the suite geomean by up to 5.4% BETWEEN RUNS AT THE SAME COMMIT.
///
/// ⚑ This IS a behaviour change, and deliberately so: the order-sensitivity the
/// old comment describes is real (`run_impl` applies only a STABLE depth sort
/// for the instruction tiers, iterates the raw order for the pure-call tier,
/// and `region_licm_hoist` takes the first eligible nesting per invocation), so
/// overlapping / nested loop shapes CAN hoist differently now. The difference
/// is that they now do so the SAME WAY EVERY TIME. Header order is total and
/// stable; a verified compiler must be reproducible.
///
/// Do not reintroduce the map. `find_natural_loops_is_deterministically_ordered`
/// pins this.
fn find_natural_loops(
    func: &X86ISelFunction,
    preds: &HashMap<Block, Vec<Block>>,
    idom: &HashMap<Block, Block>,
) -> Vec<NaturalLoop> {
    // ⚑ DETERMINISM: return the upstream order DIRECTLY. This used to collect
    // into a `HashMap<Block, NaturalLoop>` and return `by_header.into_values()`,
    // which yields loops in HASH order — and Rust's default hasher is seeded per
    // PROCESS, so the loop processing order varied between two compiles of
    // identical input. LICM hoists into preheaders in loop-processing order, so
    // that leaked into the emitted instruction order, then into register
    // allocation, then into the BYTES: `v2_memfill` compiled to two different
    // (both valid) binaries roughly 40/60 across builds.
    //
    // The map was pure overhead: `mach_view::find_natural_loops` is backed by a
    // `BTreeMap` keyed by header (see the DETERMINISM note on
    // `LoopForest::loops` in `loops.rs`), so headers are ALREADY unique and
    // ALREADY in a total, stable order. The round-trip only destroyed it.
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

// ===========================================================================
// Guarded-slot-containment load hoist (opt-in TCG_X86_LICM_GUARDED_HOIST).
//
// STATUS (2026-07-20): EXPERIMENTAL, default-OFF. SOUND and unit-validated on
// the canonical guarded-nested-loop pattern (fires + correct transform; see
// the `gh_nested_*` tests), and SAFE when enabled (90-program nested-matmul
// differential vs LLVM, 0 mismatch). KNOWN INCOMPLETENESS: it does NOT yet
// fire on the real post-unroll b05 structure — the store-side nested-guard
// containment proves (`roots={2}`) but the load-side term-guard scan and the
// real merged-block guard/index layout don't yet connect. This is a
// COMPLETENESS gap (it declines to optimize), never a correctness risk: one
// unproven store/term disables the tier for the loop, fail-closed. The
// remaining firing work + full design rationale: see
// `docs/x86-guarded-hoist-design-2026-07-20.md`.
//
// Transform (load→COPY, the validated soundness fix): a load whose address is
// loop-invariant and provably disjoint from every in-loop store
// (slot-containment via bounds-check guards) is loaded ONCE in the preheader
// into a fresh vreg H; the in-loop load is replaced IN PLACE by `dst = MovRR
// H` — dst keeps its name and every use, so there is NO reader rewiring (the
// rewire was the sole source of the earlier miscompile) — and the now-dead
// in-loop address chain is swept by DCE.
// ===========================================================================

fn ghoist_trace() -> bool {
    std::env::var_os("TCG_X86_LICM_GUARDED_TRACE").is_some()
}

macro_rules! ghtrace {
    ($($arg:tt)*) => {
        if ghoist_trace() {
            eprintln!("[guarded-hoist] {}", format!($($arg)*));
        }
    };
}

/// Symbolic frame address: `slot + base_const + Σ terms[i].root · terms[i].scale`.
#[derive(Debug, Clone)]
struct GhSymAddr {
    slot: u32,
    base_const: i64,
    /// (root index vreg, scale, position-of-consumption in its block).
    terms: Vec<(VReg, i64, usize)>,
}

fn gh_defines(inst: &X86ISelInst) -> Option<VReg> {
    if !x86_produces_value(inst.opcode) {
        return None;
    }
    match inst.operands.first() {
        Some(X86ISelOperand::VReg(v)) => Some(*v),
        _ => None,
    }
}

fn gh_hidden_def(op: X86Opcode) -> bool {
    matches!(
        op,
        X86Opcode::Xchg | X86Opcode::Cmpxchg | X86Opcode::Cmpxchg8 | X86Opcode::Cmpxchg16
    )
}

fn gh_nearest_local_def(
    block: &trust_cg_lower::X86ISelBlock,
    upto: usize,
    v: VReg,
) -> Option<(usize, &X86ISelInst)> {
    let lim = upto.min(block.insts.len());
    for i in (0..lim).rev() {
        if gh_defines(&block.insts[i]) == Some(v) {
            return Some((i, &block.insts[i]));
        }
    }
    None
}

fn gh_exact_copy(inst: &X86ISelInst) -> Option<(VReg, VReg)> {
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

/// Resolve `v` (read at `block[upto]`) through nearest-local-def exact copies.
fn gh_resolve_copies(
    block: &trust_cg_lower::X86ISelBlock,
    mut upto: usize,
    v: VReg,
) -> (VReg, usize) {
    let mut cur = v;
    for _ in 0..8 {
        match gh_nearest_local_def(block, upto, cur) {
            Some((i, inst)) => match gh_exact_copy(inst) {
                Some((_, s)) => {
                    cur = s;
                    upto = i;
                }
                None => return (cur, upto),
            },
            None => return (cur, upto),
        }
    }
    (cur, upto)
}

/// The compile-time constant `v` provably holds at `block[upto]`: a nearest
/// local `MovRI`, or a whole-function single-def `MovRI` for a live-in.
fn gh_const_of(
    func: &X86ISelFunction,
    block: &trust_cg_lower::X86ISelBlock,
    upto: usize,
    v: VReg,
    def_counts: &HashMap<VReg, usize>,
    def_sites: &HashMap<VReg, (Block, usize)>,
) -> Option<i64> {
    let (cur, pos) = gh_resolve_copies(block, upto, v);
    match gh_nearest_local_def(block, pos, cur) {
        Some((_, inst)) => match (inst.opcode, inst.operands.as_slice()) {
            (X86Opcode::MovRI, [_, X86ISelOperand::Imm(k)]) => Some(*k),
            _ => None,
        },
        None => {
            if def_counts.get(&cur).copied().unwrap_or(0) != 1 {
                return None;
            }
            let &(db, di) = def_sites.get(&cur)?;
            let dinst = func.blocks.get(&db)?.insts.get(di)?;
            match (dinst.opcode, dinst.operands.as_slice()) {
                (X86Opcode::MovRI, [X86ISelOperand::VReg(d), X86ISelOperand::Imm(k)])
                    if *d == cur =>
                {
                    Some(*k)
                }
                _ => None,
            }
        }
    }
}

/// Interpret `v` (read at `block[upto]`) as a scaled-index term.
fn gh_term_of(
    func: &X86ISelFunction,
    block: &trust_cg_lower::X86ISelBlock,
    upto: usize,
    v: VReg,
    def_counts: &HashMap<VReg, usize>,
    def_sites: &HashMap<VReg, (Block, usize)>,
) -> (VReg, i64, usize) {
    let (cur, pos) = gh_resolve_copies(block, upto, v);
    // Local def, else the single-def site for a live-in (value fixed there).
    let local = gh_nearest_local_def(block, pos, cur);
    let (site_block, i, inst) = match local {
        Some((i, inst)) => (block, i, inst),
        None => {
            if def_counts.get(&cur).copied().unwrap_or(0) == 1 {
                if let Some(&(db, di)) = def_sites.get(&cur) {
                    if let Some(dblk) = func.blocks.get(&db) {
                        if let Some(dinst) = dblk.insts.get(di) {
                            if gh_defines(dinst) == Some(cur) {
                                (dblk, di, dinst)
                            } else {
                                return (cur, 1, pos);
                            }
                        } else {
                            return (cur, 1, pos);
                        }
                    } else {
                        return (cur, 1, pos);
                    }
                } else {
                    return (cur, 1, pos);
                }
            } else {
                return (cur, 1, pos);
            }
        }
    };
    let out_pos = |rpos: usize| if local.is_some() { rpos } else { pos };
    match (inst.opcode, inst.operands.as_slice()) {
        (
            X86Opcode::ImulRRI,
            [
                X86ISelOperand::VReg(_),
                X86ISelOperand::VReg(s),
                X86ISelOperand::Imm(k),
            ],
        ) if *k > 0 => {
            let (root, rpos) = gh_resolve_copies(site_block, i, *s);
            (root, *k, out_pos(rpos))
        }
        (
            X86Opcode::ShlRI,
            [
                X86ISelOperand::VReg(_),
                X86ISelOperand::VReg(s),
                X86ISelOperand::Imm(k),
            ],
        ) if (0..=16).contains(k) => {
            let (root, rpos) = gh_resolve_copies(site_block, i, *s);
            (root, 1i64 << k, out_pos(rpos))
        }
        (
            X86Opcode::ImulRR,
            [
                X86ISelOperand::VReg(_),
                X86ISelOperand::VReg(s1),
                X86ISelOperand::VReg(s2),
            ],
        ) => {
            if let Some(k) = gh_const_of(func, site_block, i, *s2, def_counts, def_sites)
                && k > 0
            {
                let (root, rpos) = gh_resolve_copies(site_block, i, *s1);
                return (root, k, out_pos(rpos));
            }
            if let Some(k) = gh_const_of(func, site_block, i, *s1, def_counts, def_sites)
                && k > 0
            {
                let (root, rpos) = gh_resolve_copies(site_block, i, *s2);
                return (root, k, out_pos(rpos));
            }
            (cur, 1, pos)
        }
        _ => (cur, 1, pos),
    }
}

/// Resolve the frame address held in `v`, read at `block_id[upto]`, into a
/// symbolic form. Nearest-local-def within the block; a live-in falls back
/// to whole-function single-def resolution (the def then dominates the use).
fn gh_resolve_sym_addr(
    func: &X86ISelFunction,
    block_id: Block,
    upto: usize,
    v: VReg,
    def_counts: &HashMap<VReg, usize>,
    def_sites: &HashMap<VReg, (Block, usize)>,
    fuel: u32,
) -> Option<GhSymAddr> {
    if fuel == 0 {
        return None;
    }
    let block = func.blocks.get(&block_id)?;
    let (site_block, site_idx, inst) = match gh_nearest_local_def(block, upto, v) {
        Some((i, inst)) => (block_id, i, inst),
        None => {
            if def_counts.get(&v).copied().unwrap_or(0) != 1 {
                return None;
            }
            let &(db, di) = def_sites.get(&v)?;
            let dinst = func.blocks.get(&db)?.insts.get(di)?;
            if gh_defines(dinst) != Some(v) {
                return None;
            }
            (db, di, dinst)
        }
    };
    let recurse = |vv: VReg, at: usize, f: u32| {
        gh_resolve_sym_addr(func, site_block, at, vv, def_counts, def_sites, f)
    };
    match (inst.opcode, inst.operands.as_slice()) {
        (X86Opcode::MovRR, [X86ISelOperand::VReg(d), X86ISelOperand::VReg(s)])
            if d.class == s.class =>
        {
            recurse(*s, site_idx, fuel - 1)
        }
        (X86Opcode::Lea, [_, X86ISelOperand::MemAddr { base, disp }]) => match base.as_ref() {
            X86ISelOperand::StackSlot(s) => Some(GhSymAddr {
                slot: *s,
                base_const: i64::from(*disp),
                terms: Vec::new(),
            }),
            X86ISelOperand::VReg(r) => {
                let mut a = recurse(*r, site_idx, fuel - 1)?;
                a.base_const = a.base_const.checked_add(i64::from(*disp))?;
                Some(a)
            }
            _ => None,
        },
        (
            X86Opcode::Lea,
            [
                _,
                X86ISelOperand::SibMemAddr {
                    base,
                    index,
                    scale,
                    disp,
                },
            ],
        ) => {
            if site_block != block_id {
                return None;
            }
            let base_v = match base.as_ref() {
                X86ISelOperand::VReg(r) => *r,
                _ => return None,
            };
            let idx_v = match index.as_ref() {
                X86ISelOperand::VReg(r) => *r,
                _ => return None,
            };
            let mut a = recurse(base_v, site_idx, fuel - 1)?;
            let sb = func.blocks.get(&site_block)?;
            let (root, rpos) = gh_resolve_copies(sb, site_idx, idx_v);
            a.terms.push((root, i64::from(*scale), rpos));
            a.base_const = a.base_const.checked_add(i64::from(*disp))?;
            Some(a)
        }
        (
            X86Opcode::AddRI,
            [
                X86ISelOperand::VReg(_),
                X86ISelOperand::VReg(s),
                X86ISelOperand::Imm(k),
            ],
        ) => {
            let mut a = recurse(*s, site_idx, fuel - 1)?;
            a.base_const = a.base_const.checked_add(*k)?;
            Some(a)
        }
        (X86Opcode::AddRI, [X86ISelOperand::VReg(d), X86ISelOperand::Imm(k)]) => {
            let mut a = recurse(*d, site_idx, fuel - 1)?;
            a.base_const = a.base_const.checked_add(*k)?;
            Some(a)
        }
        (
            X86Opcode::AddRR,
            [
                X86ISelOperand::VReg(_),
                X86ISelOperand::VReg(s1),
                X86ISelOperand::VReg(s2),
            ],
        ) => {
            if site_block != block_id {
                return None;
            }
            if let Some(mut a) = recurse(*s1, site_idx, fuel - 1) {
                let t = gh_term_of(func, block, site_idx, *s2, def_counts, def_sites);
                a.terms.push(t);
                return Some(a);
            }
            if let Some(mut a) = recurse(*s2, site_idx, fuel - 1) {
                let t = gh_term_of(func, block, site_idx, *s1, def_counts, def_sites);
                a.terms.push(t);
                return Some(a);
            }
            None
        }
        (X86Opcode::AddRR, [X86ISelOperand::VReg(d), X86ISelOperand::VReg(s)]) => {
            if site_block != block_id {
                return None;
            }
            if let Some(mut a) = recurse(*d, site_idx, fuel - 1) {
                let t = gh_term_of(func, block, site_idx, *s, def_counts, def_sites);
                a.terms.push(t);
                return Some(a);
            }
            None
        }
        _ => None,
    }
}

/// Reaching-def hop for a value BODY-INVARIANT w.r.t. `lp`: single in-body
/// predecessor; else the loop preheader when at `lp.header` (both in-edges
/// carry the same invariant value); else the single function-wide predecessor
/// in the pre-loop region. Returns None at a genuine merge.
fn gh_reach_pred(
    lp: &NaturalLoop,
    preds: &HashMap<Block, Vec<Block>>,
    b: Block,
    body_inv: bool,
) -> Option<Block> {
    if let Some(ps) = preds.get(&b) {
        // In-body single predecessor.
        let in_body: Vec<Block> = ps.iter().copied().filter(|p| lp.body.contains(p)).collect();
        if b == lp.header {
            return lp.preheader;
        }
        if let [only] = ps.as_slice() {
            return Some(*only);
        }
        if let [only] = in_body.as_slice() {
            return Some(*only);
        }
        // Internal merge (the bounds-check trap diamonds create these): for a
        // BODY-INVARIANT value, nothing in the loop body redefines it, so its
        // value is identical on every in-edge — cross via any in-body pred.
        // Deterministic: lowest block index.
        if body_inv {
            let mut c = in_body.clone();
            c.sort_by_key(|x| x.0);
            if let Some(first) = c.first() {
                return Some(*first);
            }
        }
    }
    None
}

/// Chase `v` (read at `at_block[upto]`, BODY-INVARIANT w.r.t. `lp`) to its
/// reaching-def TERMINAL, following exact copies and invariance-gated hops
/// (gh_reach_pred). Two body-invariant values are EQUAL iff terminals match.
fn gh_chain_terminal(
    func: &X86ISelFunction,
    lp: &NaturalLoop,
    preds: &HashMap<Block, Vec<Block>>,
    at_block: Block,
    upto: usize,
    v: VReg,
    body_inv: bool,
) -> (VReg, Block, usize) {
    let mut cur = v;
    let mut block_id = at_block;
    let mut limit = upto;
    for _ in 0..24 {
        let Some(block) = func.blocks.get(&block_id) else {
            return (cur, block_id, limit);
        };
        match gh_nearest_local_def(block, limit, cur) {
            Some((i, inst)) => match gh_exact_copy(inst) {
                Some((_, s)) => {
                    cur = s;
                    limit = i;
                }
                None => return (cur, block_id, i),
            },
            None => {
                let Some(p) = gh_reach_pred(lp, preds, block_id, body_inv) else {
                    return (cur, block_id, usize::MAX);
                };
                block_id = p;
                limit = func.blocks.get(&p).map(|b| b.insts.len()).unwrap_or(0);
            }
        }
    }
    (cur, block_id, limit)
}

enum GhGuard {
    Bound(u64),
    Redefined,
}

/// Scan one block backwards from `scan_from` for a `TrapBoundsCheckExact`
/// whose index equals `root` (direct name; the reaching-def chain already
/// canonicalized copies before the call). `capture_at` (if the term was
/// captured in THIS block) requires no root redefinition in the
/// capture<->guard window.
fn gh_guard_in_block(
    block: &trust_cg_lower::X86ISelBlock,
    block_id: Block,
    scan_from: usize,
    capture_at: Option<usize>,
    root: VReg,
    matches: &dyn Fn(VReg, Block, usize) -> bool,
) -> Option<GhGuard> {
    let lim = scan_from.min(block.insts.len());
    for i in (0..lim).rev() {
        let inst = &block.insts[i];
        if gh_hidden_def(inst.opcode) {
            return Some(GhGuard::Redefined);
        }
        if inst.opcode == X86Opcode::TrapBoundsCheckExact {
            if let [_, X86ISelOperand::VReg(idx), X86ISelOperand::Imm(bound)] =
                inst.operands.as_slice()
                && (*idx == root || matches(*idx, block_id, i))
            {
                if let Some(cap) = capture_at {
                    let (lo, hi) = if cap <= i { (cap, i) } else { (i, cap) };
                    let hi_c = hi.min(block.insts.len());
                    let redef = block.insts[lo..hi_c]
                        .iter()
                        .any(|it| gh_defines(it) == Some(root));
                    if redef {
                        return Some(GhGuard::Redefined);
                    }
                }
                return u64::try_from(*bound)
                    .ok()
                    .map(GhGuard::Bound)
                    .or(Some(GhGuard::Redefined));
            }
            continue;
        }
        if gh_defines(inst) == Some(root) {
            return Some(GhGuard::Redefined);
        }
    }
    None
}

/// Guard-proven unsigned bound of `root` consumed at `start_block[scan_from]`.
/// Scans the start block, then hops the in-loop straight-line chain (single
/// in-body pred), and finally — for a body-invariant root — the preheader
/// ancestor chain (single pred). Fail-closed.
struct GhCfgAnalysis<'a> {
    preds: &'a HashMap<Block, Vec<Block>>,
    idom: &'a HashMap<Block, Block>,
}

fn gh_bound(
    func: &X86ISelFunction,
    lp: &NaturalLoop,
    cfg: &GhCfgAnalysis<'_>,
    start_block: Block,
    scan_from: usize,
    capture_at: usize,
    root: VReg,
) -> Option<u64> {
    let root_inv = gh_body_invariant(func, lp, root);
    // Terminal-equality matcher (sound only for body-invariant values): a
    // guard names ROOT iff their invariance-gated reaching-def terminals
    // coincide.
    let root_term = if root_inv {
        Some(gh_chain_terminal(
            func,
            lp,
            cfg.preds,
            start_block,
            capture_at,
            root,
            true,
        ))
    } else {
        None
    };
    let matches = |idx: VReg, gb: Block, gp: usize| -> bool {
        match root_term {
            Some(rt) => {
                gh_body_invariant(func, lp, idx)
                    && gh_chain_terminal(func, lp, cfg.preds, gb, gp, idx, true) == rt
            }
            None => false,
        }
    };
    // DOMINANCE scan: any guard in a block that DOMINATES the access executes
    // before it on every path (dominance is merge-aware, unlike a single-pred
    // hop that stops at the bounds-check trap-diamond merges). Walk the idom
    // chain from the access block to the entry; in the access block scan
    // before the access (capture-window redef check applies), in every
    // strict dominator scan the whole block. A Redefined verdict (the root or
    // a hidden-def between guard and use) fails closed.
    let mut cur = start_block;
    let mut first = true;
    for _ in 0..64 {
        let block = func.blocks.get(&cur)?;
        let (scan, cap) = if first {
            (scan_from, Some(capture_at))
        } else {
            (block.insts.len(), None)
        };
        if let Some(g) = gh_guard_in_block(block, cur, scan, cap, root, &matches) {
            return match g {
                GhGuard::Bound(b) => Some(b),
                GhGuard::Redefined => None,
            };
        }
        first = false;
        match cfg.idom.get(&cur) {
            Some(&d) if d != cur => cur = d,
            _ => break, // entry (idom of entry is itself)
        }
    }
    None
}

/// Containment: the maximal address `sym` can reach lies inside its slot,
/// under guard-proven per-term bounds.
fn gh_contained(
    func: &X86ISelFunction,
    lp: &NaturalLoop,
    cfg: &GhCfgAnalysis<'_>,
    at_block: Block,
    access_at: usize,
    sym: &GhSymAddr,
    access_width: i64,
) -> bool {
    let Some(info) = func.stack_slots.get(sym.slot as usize) else {
        return false;
    };
    if info.allocation != StackSlotAllocationKind::Fixed || sym.base_const < 0 {
        return false;
    }
    let mut max_reach = sym.base_const;
    for &(root, scale, consumed_at) in &sym.terms {
        if scale <= 0 {
            return false;
        }
        // Guard scan starts at the ACCESS; the capture is the term's
        // recorded position when captured in the access block, else the
        // access itself.
        let capture = consumed_at.min(access_at);
        let Some(bound) = gh_bound(func, lp, cfg, at_block, access_at, capture, root) else {
            ghtrace!("  term v{} scale={}: NO DOMINATING GUARD", root.id, scale);
            return false;
        };
        if bound == 0 {
            return false;
        }
        let Ok(bm1) = i64::try_from(bound - 1) else {
            return false;
        };
        let Some(tmax) = bm1.checked_mul(scale) else {
            return false;
        };
        let Some(nx) = max_reach.checked_add(tmax) else {
            return false;
        };
        max_reach = nx;
    }
    let Some(end) = max_reach.checked_add(access_width) else {
        return false;
    };
    end <= i64::from(info.size)
}

/// A term root is loop-value-invariant iff it has NO def inside THIS loop's
/// body (multi-def globally is fine — at the preheader exactly one def
/// reaches, and the vreg is live-in). The preheader rebuild reads `root`
/// directly (it is live at the preheader end).
fn gh_body_invariant(func: &X86ISelFunction, lp: &NaturalLoop, root: VReg) -> bool {
    func.block_order.iter().all(|b| {
        !lp.body.contains(b)
            || func
                .blocks
                .get(b)
                .map(|blk| {
                    blk.insts
                        .iter()
                        .all(|it| gh_defines(it) != Some(root) && !gh_hidden_def(it.opcode))
                })
                .unwrap_or(false)
    })
}

struct GhCandidate {
    block: Block,
    load_idx: usize,
    dst: VReg,
    sym: GhSymAddr,
}

/// The guarded-slot-containment tier driver for one loop (load→copy).
fn guarded_slice_hoist(func: &mut X86ISelFunction, lp: &NaturalLoop) -> bool {
    let Some(preheader) = lp.preheader else {
        return false;
    };
    let def_counts = build_def_counts(func);
    let def_sites = build_def_sites(func);
    let preds = mach_view::predecessor_map(func);
    let idom = compute_idom(func, &preds);
    let gh_cfg = GhCfgAnalysis {
        preds: &preds,
        idom: &idom,
    };

    // Store containment: ONE unproven store disables the tier.
    let mut store_roots: HashSet<u32> = HashSet::new();
    for block_id in &func.block_order {
        if !lp.body.contains(block_id) {
            continue;
        }
        let Some(block) = func.blocks.get(block_id) else {
            return false;
        };
        for (i, inst) in block.insts.iter().enumerate() {
            if inst.proof_origin.is_some()
                || inst.flags.is_call()
                || gh_hidden_def(inst.opcode)
                || matches!(x86_inst_effect(inst), MemoryEffect::Call)
            {
                return false;
            }
            if x86_inst_effect(inst).writes_memory() {
                let Some(width) = plain_store_width(inst.opcode) else {
                    return false;
                };
                let mut sib_term: Option<(VReg, i64, usize)> = None;
                let (base_v, disp) = match inst.operands.first() {
                    Some(X86ISelOperand::MemAddr { base, disp }) => match base.as_ref() {
                        X86ISelOperand::VReg(r) => (*r, *disp),
                        X86ISelOperand::StackSlot(_) => continue,
                        _ => return false,
                    },
                    Some(X86ISelOperand::SibMemAddr {
                        base,
                        index,
                        scale,
                        disp,
                    }) => {
                        let (X86ISelOperand::VReg(b), X86ISelOperand::VReg(ix)) =
                            (base.as_ref(), index.as_ref())
                        else {
                            return false;
                        };
                        let (root, rpos) = gh_resolve_copies(block, i, *ix);
                        sib_term = Some((root, i64::from(*scale), rpos));
                        (*b, *disp)
                    }
                    _ => return false,
                };
                let Some(mut sym) =
                    gh_resolve_sym_addr(func, *block_id, i, base_v, &def_counts, &def_sites, 12)
                else {
                    ghtrace!("disable: store addr unresolved {:?}[{}]", block_id, i);
                    return false;
                };
                if let Some(term) = sib_term {
                    sym.terms.push(term);
                }
                let Some(bc) = sym.base_const.checked_add(i64::from(disp)) else {
                    return false;
                };
                sym.base_const = bc;
                if !gh_contained(func, lp, &gh_cfg, *block_id, i, &sym, width) {
                    ghtrace!(
                        "disable: store not contained (slot {} terms {})",
                        sym.slot,
                        sym.terms.len()
                    );
                    return false;
                }
                store_roots.insert(sym.slot);
            }
        }
    }

    ghtrace!(
        "loop header={:?}: stores contained, roots={:?}",
        lp.header,
        store_roots
    );
    // Candidate loads: MovRM via a vreg base; contained address in a slot
    // disjoint from store roots; every term root body-invariant.
    let mut cands: Vec<GhCandidate> = Vec::new();
    for block_id in &func.block_order {
        if !lp.body.contains(block_id) {
            continue;
        }
        let Some(block) = func.blocks.get(block_id) else {
            continue;
        };
        for (i, inst) in block.insts.iter().enumerate() {
            if inst.opcode != X86Opcode::MovRM || inst.proof_origin.is_some() {
                continue;
            }
            let (dst, base_v, disp) = match inst.operands.as_slice() {
                [
                    X86ISelOperand::VReg(d),
                    X86ISelOperand::MemAddr { base, disp },
                ] => match base.as_ref() {
                    X86ISelOperand::VReg(r) => (*d, *r, *disp),
                    _ => continue,
                },
                _ => continue,
            };
            let Some(mut sym) =
                gh_resolve_sym_addr(func, *block_id, i, base_v, &def_counts, &def_sites, 12)
            else {
                continue;
            };
            let Some(bc) = sym.base_const.checked_add(i64::from(disp)) else {
                continue;
            };
            sym.base_const = bc;
            if store_roots.contains(&sym.slot) {
                ghtrace!(
                    "load {:?}[{}]: slot {} is a store root",
                    block_id,
                    i,
                    sym.slot
                );
                continue;
            }
            if !gh_contained(func, lp, &gh_cfg, *block_id, i, &sym, 8) {
                ghtrace!(
                    "load {:?}[{}]: not contained (slot {} terms {})",
                    block_id,
                    i,
                    sym.slot,
                    sym.terms.len()
                );
                continue;
            }
            if !sym
                .terms
                .iter()
                .all(|&(r, _, _)| gh_body_invariant(func, lp, r))
            {
                ghtrace!("load {:?}[{}]: term not body-invariant", block_id, i);
                continue;
            }
            ghtrace!(
                "ACCEPT load {:?}[{}] slot {} terms {}",
                block_id,
                i,
                sym.slot,
                sym.terms.len()
            );
            cands.push(GhCandidate {
                block: *block_id,
                load_idx: i,
                dst,
                sym,
            });
            if cands.len() >= 64 {
                break;
            }
        }
    }
    if cands.is_empty() {
        return false;
    }

    // Apply load->copy: preheader rebuild + load into H; in-loop load
    // becomes `dst = MovRR H`. Descending load_idx per block keeps indices
    // valid (in-place replace, not delete).
    cands.sort_by_key(|c| (c.block.0, std::cmp::Reverse(c.load_idx)));
    let mut changed = false;
    for c in cands {
        // Preheader address rebuild with fresh vregs (reads the body-
        // invariant term roots directly — live at the preheader end).
        let addr = {
            let id = func.next_vreg;
            func.next_vreg += 1;
            VReg {
                id,
                class: RegClass::Gpr64,
            }
        };
        let disp_i32 = match i32::try_from(c.sym.base_const) {
            Ok(d) => d,
            Err(_) => continue,
        };
        let mut new_insts: Vec<X86ISelInst> = vec![X86ISelInst::new(
            X86Opcode::Lea,
            vec![
                X86ISelOperand::VReg(addr),
                X86ISelOperand::MemAddr {
                    base: Box::new(X86ISelOperand::StackSlot(c.sym.slot)),
                    disp: disp_i32,
                },
            ],
        )];
        let mut ok = true;
        for &(root, scale, _) in &c.sym.terms {
            if root.class != RegClass::Gpr64 {
                ok = false;
                break;
            }
            let prod = {
                let id = func.next_vreg;
                func.next_vreg += 1;
                VReg {
                    id,
                    class: RegClass::Gpr64,
                }
            };
            new_insts.push(X86ISelInst::new(
                X86Opcode::ImulRRI,
                vec![
                    X86ISelOperand::VReg(prod),
                    X86ISelOperand::VReg(root),
                    X86ISelOperand::Imm(scale),
                ],
            ));
            new_insts.push(X86ISelInst::new(
                X86Opcode::AddRR,
                vec![
                    X86ISelOperand::VReg(addr),
                    X86ISelOperand::VReg(addr),
                    X86ISelOperand::VReg(prod),
                ],
            ));
        }
        if !ok {
            continue;
        }
        let hoisted = {
            let id = func.next_vreg;
            func.next_vreg += 1;
            VReg {
                id,
                class: c.dst.class,
            }
        };
        new_insts.push(X86ISelInst::new(
            X86Opcode::MovRM,
            vec![
                X86ISelOperand::VReg(hoisted),
                X86ISelOperand::MemAddr {
                    base: Box::new(X86ISelOperand::VReg(addr)),
                    disp: 0,
                },
            ],
        ));
        // Insert before the preheader's trailing terminator run.
        {
            let Some(ph) = func.blocks.get_mut(&preheader) else {
                continue;
            };
            let at = {
                let mut p = ph.insts.len();
                while p > 0
                    && (ph.insts[p - 1].flags.is_terminator() || ph.insts[p - 1].flags.is_branch())
                {
                    p -= 1;
                }
                p
            };
            for (k, ni) in new_insts.into_iter().enumerate() {
                ph.insts.insert(at + k, ni);
            }
        }
        // In-loop: replace the load IN PLACE with `dst = MovRR hoisted`.
        {
            let Some(blk) = func.blocks.get_mut(&c.block) else {
                continue;
            };
            if c.load_idx >= blk.insts.len() {
                continue;
            }
            blk.insts[c.load_idx] = X86ISelInst::new(
                X86Opcode::MovRR,
                vec![X86ISelOperand::VReg(c.dst), X86ISelOperand::VReg(hoisted)],
            );
        }
        changed = true;
    }
    changed
}

#[cfg(test)]
mod tests {
    use super::*;

    use trust_cg_ir::regs::{RegClass, VReg};
    use trust_cg_ir::x86_64_regs::RAX;
    use trust_cg_lower::function::Signature;
    use trust_cg_lower::types::Type;

    use crate::X86PassManager;

    fn vreg(id: u32) -> X86ISelOperand {
        X86ISelOperand::VReg(VReg::new(id, RegClass::Gpr64))
    }
    fn imm(v: i64) -> X86ISelOperand {
        X86ISelOperand::Imm(v)
    }

    /// Build a 3-block loop:
    ///
    /// ```text
    ///   bb0 (preheader): jmp bb1
    ///   bb1 (header)  <--+ : <body> ; jmp bb1 (self-loop latch)
    ///   bb2 (exit)       : ret
    /// ```
    /// Here we use a self-loop header (bb0 -> bb1, bb1 -> bb1, bb1 -> bb2) so the
    /// natural preheader is bb0. The body insts are supplied by the caller.
    /// DETERMINISM REGRESSION GUARD. `find_natural_loops` must return loops in a
    /// TOTAL, STABLE order (sorted by header block index).
    ///
    /// This pass hoists into preheaders in loop-processing order, so a
    /// nondeterministic loop order leaks all the way to the emitted BYTES. A
    /// `HashMap` round-trip here — which is exactly what this replaced — makes
    /// the compiler emit different (both valid) binaries for identical input,
    /// because Rust's default hasher is seeded per process.
    ///
    /// Build two disjoint self-loops and assert the headers come back ascending.
    #[test]
    fn find_natural_loops_is_deterministically_ordered() {
        let sig = Signature {
            params: vec![],
            returns: vec![Type::I64],
        };
        let mut func = X86ISelFunction::new("two_loops".to_string(), sig);
        // entry -> L1(header b1, latch b2) -> mid -> L2(header b4, latch b5) -> exit
        let bs: Vec<Block> = (0..7).map(Block).collect();
        for b in &bs {
            func.ensure_block(*b);
        }
        func.next_vreg = 64;
        let jmp = |t: Block| X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(t)]);
        let jcc = |t: Block| {
            X86ISelInst::new(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::E),
                    X86ISelOperand::Block(t),
                ],
            )
        };
        // b0 -> b1
        func.blocks.get_mut(&bs[0]).unwrap().successors = vec![bs[1]];
        func.push_inst(bs[0], jmp(bs[1]));
        // b1 -> b2 (loop 1 header)
        func.blocks.get_mut(&bs[1]).unwrap().successors = vec![bs[2]];
        func.push_inst(bs[1], jmp(bs[2]));
        // b2 -> b1 (back edge) | b3
        func.blocks.get_mut(&bs[2]).unwrap().successors = vec![bs[1], bs[3]];
        func.push_inst(bs[2], jcc(bs[1]));
        func.push_inst(bs[2], jmp(bs[3]));
        // b3 -> b4
        func.blocks.get_mut(&bs[3]).unwrap().successors = vec![bs[4]];
        func.push_inst(bs[3], jmp(bs[4]));
        // b4 -> b5 (loop 2 header)
        func.blocks.get_mut(&bs[4]).unwrap().successors = vec![bs[5]];
        func.push_inst(bs[4], jmp(bs[5]));
        // b5 -> b4 (back edge) | b6
        func.blocks.get_mut(&bs[5]).unwrap().successors = vec![bs[4], bs[6]];
        func.push_inst(bs[5], jcc(bs[4]));
        func.push_inst(bs[5], jmp(bs[6]));
        func.push_inst(bs[6], X86ISelInst::new(X86Opcode::Ret, vec![]));
        func.block_order = bs.clone();

        let preds = mach_view::predecessor_map(&func);
        let idom = compute_idom(&func, &preds);
        let loops = find_natural_loops(&func, &preds, &idom);
        assert!(
            loops.len() >= 2,
            "fixture must produce two natural loops, got {}",
            loops.len()
        );
        let headers: Vec<u32> = loops.iter().map(|l| l.header.0).collect();
        let mut sorted = headers.clone();
        sorted.sort_unstable();
        assert_eq!(
            headers, sorted,
            "loop order must be TOTAL and STABLE (sorted by header). A HashMap \
             round-trip here re-randomises it every process and leaks into the \
             emitted bytes."
        );
        // EXACT contract, not a coincidence: with only two loops a randomly
        // ordered result would still be sorted half the time, so also pin the
        // order to the upstream analysis element-for-element.
        let upstream: Vec<u32> = mach_view::find_natural_loops(&func, &preds, &idom)
            .iter()
            .map(|l| l.header.0)
            .collect();
        assert_eq!(
            headers, upstream,
            "this pass must hand consumers mach_view's order UNCHANGED; any \
             re-keying through a hash container reintroduces the nondeterminism"
        );
    }

    fn make_self_loop(body: Vec<X86ISelInst>) -> X86ISelFunction {
        let sig = Signature {
            params: vec![],
            returns: vec![Type::I64],
        };
        let mut func = X86ISelFunction::new("x86_licm_test".to_string(), sig);
        let bb0 = Block(0);
        let bb1 = Block(1);
        let bb2 = Block(2);
        func.ensure_block(bb0);
        func.ensure_block(bb1);
        func.ensure_block(bb2);
        func.next_vreg = 64;

        // bb0 -> bb1
        func.blocks.get_mut(&bb0).unwrap().successors = vec![bb1];
        func.push_inst(
            bb0,
            X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(bb1)]),
        );

        // bb1 body, then conditional self-loop: jcc bb1 / fallthrough bb2.
        // Successors: both bb1 (back-edge) and bb2 (exit).
        func.blocks.get_mut(&bb1).unwrap().successors = vec![bb1, bb2];
        for inst in body {
            func.push_inst(bb1, inst);
        }
        func.push_inst(
            bb1,
            X86ISelInst::new(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(trust_cg_ir::X86CondCode::B),
                    X86ISelOperand::Block(bb1),
                ],
            ),
        );

        // bb2 exit
        func.push_inst(bb2, X86ISelInst::new(X86Opcode::Ret, vec![]));

        func
    }

    fn block_insts(func: &X86ISelFunction, b: Block) -> &[X86ISelInst] {
        &func.blocks.get(&b).unwrap().insts
    }

    #[test]
    fn x86_licm_hoists_invariant_constant_materialization() {
        // v10 = movl $0x9e3779b1 is loop-invariant (immediate source only).
        let body = vec![X86ISelInst::new(
            X86Opcode::MovRI,
            vec![vreg(10), imm(0x9e37_79b1)],
        )];
        let mut func = make_self_loop(body);
        let mut pass = X86LoopInvariantCodeMotion::pure_only();

        assert!(pass.run_on_function(&mut func), "constant mov should hoist");

        // bb1 (header) should now contain only the terminator.
        let header = block_insts(&func, Block(1));
        assert_eq!(header.len(), 1, "movl const hoisted out of header");
        assert_eq!(header[0].opcode, X86Opcode::Jcc);

        // bb0 (preheader) should contain the hoisted movl before its jmp.
        let ph = block_insts(&func, Block(0));
        assert_eq!(ph.len(), 2);
        assert_eq!(ph[0].opcode, X86Opcode::MovRI);
        assert_eq!(ph[0].operands, vec![vreg(10), imm(0x9e37_79b1)]);
        assert_eq!(ph[1].opcode, X86Opcode::Jmp);
    }

    #[test]
    fn x86_licm_hoists_transitively_invariant_chain() {
        // v10 = movl $7 (invariant); v11 = lea [v10 + 8] (invariant via v10).
        // Both should hoist, with the lea following its producer.
        let lea = X86ISelInst::new(X86Opcode::Lea, vec![vreg(11), vreg(10), imm(8)]);
        let body = vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(10), imm(7)]),
            lea,
        ];
        let mut func = make_self_loop(body);
        let mut pass = X86LoopInvariantCodeMotion::pure_only();

        assert!(pass.run_on_function(&mut func));

        let header = block_insts(&func, Block(1));
        assert_eq!(
            header.len(),
            1,
            "both invariants hoisted; only terminator left"
        );

        let ph = block_insts(&func, Block(0));
        // movl, lea, jmp
        assert_eq!(ph.len(), 3);
        assert_eq!(ph[0].opcode, X86Opcode::MovRI);
        assert_eq!(ph[1].opcode, X86Opcode::Lea);
        assert_eq!(ph[2].opcode, X86Opcode::Jmp);
    }

    #[test]
    fn x86_licm_declines_non_invariant_instruction() {
        // v10 is defined in the loop by a non-invariant op (an in-loop add that
        // writes flags), and v11 = mov v10 depends on it. The mov's source is
        // loop-variant, so it must NOT hoist.
        let body = vec![
            // v10 = v10 + 1 (multi-def carrier, flag writer) — not hoistable.
            X86ISelInst::new(X86Opcode::AddRI, vec![vreg(10), imm(1)]),
            // v11 = mov v10 — source defined in loop and not invariant.
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(11), vreg(10)]),
        ];
        let mut func = make_self_loop(body);
        let before = block_insts(&func, Block(1)).len();
        let mut pass = X86LoopInvariantCodeMotion::pure_only();

        assert!(!pass.run_on_function(&mut func), "nothing is invariant");
        assert_eq!(block_insts(&func, Block(1)).len(), before);
        // Preheader unchanged (just its jmp).
        assert_eq!(block_insts(&func, Block(0)).len(), 1);
    }

    #[test]
    fn x86_licm_declines_side_effecting_store() {
        // A store has side effects and must never hoist even with invariant
        // operands.
        let store = X86ISelInst::new(
            X86Opcode::MovMR,
            vec![
                X86ISelOperand::MemAddr {
                    base: Box::new(vreg(20)),
                    disp: 0,
                },
                vreg(21),
            ],
        );
        let body = vec![store];
        let mut func = make_self_loop(body);
        let before = block_insts(&func, Block(1)).len();
        let mut pass = X86LoopInvariantCodeMotion::pure_only();

        assert!(!pass.run_on_function(&mut func), "store must not hoist");
        assert_eq!(block_insts(&func, Block(1)).len(), before);
    }

    #[test]
    fn x86_licm_declines_flag_writer_even_with_invariant_operands() {
        // imul v10 = v11 * v12 writes RFLAGS. Even if both sources are invariant,
        // hoisting it can clobber flags consumed by a later in-loop cmp/jcc.
        let body = vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(11), imm(3)]),
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(12), imm(5)]),
            X86ISelInst::new(X86Opcode::ImulRR, vec![vreg(10), vreg(11), vreg(12)]),
        ];
        let mut func = make_self_loop(body);
        let mut pass = X86LoopInvariantCodeMotion::pure_only();

        // The two movs ARE invariant and will hoist; the imul must stay.
        let changed = pass.run_on_function(&mut func);
        assert!(changed, "the invariant constant movs hoist");

        let header = block_insts(&func, Block(1));
        // imul + jcc remain.
        assert_eq!(header.len(), 2);
        assert_eq!(
            header[0].opcode,
            X86Opcode::ImulRR,
            "flag writer stays in loop"
        );
        assert_eq!(header[1].opcode, X86Opcode::Jcc);
    }

    #[test]
    fn x86_licm_declines_fixed_physical_register_operand() {
        // mov v10, RAX reads a fixed physical register (call return glue shape).
        // LICM does not model PReg dataflow and must not move it.
        let body = vec![X86ISelInst::new(
            X86Opcode::MovRR,
            vec![vreg(10), X86ISelOperand::PReg(RAX)],
        )];
        let mut func = make_self_loop(body);
        let before = block_insts(&func, Block(1)).len();
        let mut pass = X86LoopInvariantCodeMotion::pure_only();

        assert!(!pass.run_on_function(&mut func), "PReg glue must not hoist");
        assert_eq!(block_insts(&func, Block(1)).len(), before);
    }

    #[test]
    fn x86_licm_declines_multi_def_vreg() {
        // v10 is defined twice in the loop (path-sensitive carrier). Even though
        // each def's source is an immediate, the VReg is not SSA, so hoisting is
        // unsound.
        let body = vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(10), imm(1)]),
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(10), imm(2)]),
        ];
        let mut func = make_self_loop(body);
        let before = block_insts(&func, Block(1)).len();
        let mut pass = X86LoopInvariantCodeMotion::pure_only();

        assert!(
            !pass.run_on_function(&mut func),
            "multi-def vreg must not hoist"
        );
        assert_eq!(block_insts(&func, Block(1)).len(), before);
    }

    #[test]
    fn x86_licm_declines_when_no_natural_preheader() {
        // Header with two non-loop predecessors -> no natural preheader. Even a
        // pure invariant constant must not be hoisted (we never synthesize a
        // preheader).
        let sig = Signature {
            params: vec![],
            returns: vec![Type::I64],
        };
        let mut func = X86ISelFunction::new("x86_licm_no_ph".to_string(), sig);
        let bb0 = Block(0); // entry, branches to header and to bb1
        let bb1 = Block(1); // second non-loop entry to header
        let bb2 = Block(2); // header
        let bb3 = Block(3); // latch
        let bb4 = Block(4); // exit
        for b in [bb0, bb1, bb2, bb3, bb4] {
            func.ensure_block(b);
        }
        func.next_vreg = 64;

        func.blocks.get_mut(&bb0).unwrap().successors = vec![bb1, bb2];
        func.push_inst(
            bb0,
            X86ISelInst::new(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(trust_cg_ir::X86CondCode::E),
                    X86ISelOperand::Block(bb1),
                ],
            ),
        );

        func.blocks.get_mut(&bb1).unwrap().successors = vec![bb2];
        func.push_inst(
            bb1,
            X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(bb2)]),
        );

        func.blocks.get_mut(&bb2).unwrap().successors = vec![bb3, bb4];
        func.push_inst(
            bb2,
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(10), imm(99)]),
        );
        func.push_inst(
            bb2,
            X86ISelInst::new(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(trust_cg_ir::X86CondCode::B),
                    X86ISelOperand::Block(bb3),
                ],
            ),
        );

        func.blocks.get_mut(&bb3).unwrap().successors = vec![bb2];
        func.push_inst(
            bb3,
            X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(bb2)]),
        );

        func.push_inst(bb4, X86ISelInst::new(X86Opcode::Ret, vec![]));

        let header_before = block_insts(&func, bb2).to_vec();
        let mut pass = X86LoopInvariantCodeMotion::pure_only();

        assert!(
            !pass.run_on_function(&mut func),
            "no natural preheader -> no hoist"
        );
        assert_eq!(
            block_insts(&func, bb2).len(),
            header_before.len(),
            "header instructions unchanged"
        );
    }

    #[test]
    fn x86_licm_noop_without_loops() {
        // Straight-line function: nothing to hoist.
        let sig = Signature {
            params: vec![],
            returns: vec![Type::I64],
        };
        let mut func = X86ISelFunction::new("x86_licm_no_loop".to_string(), sig);
        let bb0 = Block(0);
        func.ensure_block(bb0);
        func.next_vreg = 64;
        func.push_inst(
            bb0,
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(10), imm(1)]),
        );
        func.push_inst(bb0, X86ISelInst::new(X86Opcode::Ret, vec![]));

        let mut pass = X86LoopInvariantCodeMotion::pure_only();
        assert!(!pass.run_on_function(&mut func));
    }

    #[test]
    fn x86_licm_then_copy_prop_through_pass_manager() {
        // End-to-end through the x86 pass manager: a const mov hoists, and the
        // manager runs to completion without panicking.
        let body = vec![X86ISelInst::new(X86Opcode::MovRI, vec![vreg(10), imm(42)])];
        let mut func = make_self_loop(body);
        let mut pm =
            X86PassManager::new().with_pass(Box::new(X86LoopInvariantCodeMotion::pure_only()));

        assert!(pm.run_once(&mut func));
        let ph = block_insts(&func, Block(0));
        assert!(ph.iter().any(|i| i.opcode == X86Opcode::MovRI));
    }

    // =======================================================================
    // Invariant-load tier
    // =======================================================================

    use trust_cg_lower::function::StackSlotInfo;
    use trust_cg_lower::x86_64_isel::X86ProofOrigin;

    fn mem_slot(slot: u32, disp: i32) -> X86ISelOperand {
        X86ISelOperand::MemAddr {
            base: Box::new(X86ISelOperand::StackSlot(slot)),
            disp,
        }
    }

    fn mem_vreg(id: u32, disp: i32) -> X86ISelOperand {
        X86ISelOperand::MemAddr {
            base: Box::new(vreg(id)),
            disp,
        }
    }

    fn load(dst: u32, mem: X86ISelOperand) -> X86ISelInst {
        X86ISelInst::new(X86Opcode::MovRM, vec![vreg(dst), mem])
    }

    fn store(mem: X86ISelOperand, src: u32) -> X86ISelInst {
        X86ISelInst::new(X86Opcode::MovMR, vec![mem, vreg(src)])
    }

    fn count_opcode(insts: &[X86ISelInst], opcode: X86Opcode) -> usize {
        insts.iter().filter(|i| i.opcode == opcode).count()
    }

    #[test]
    fn x86_licm_load_tier_hoists_invariant_slot_load_store_free_loop() {
        // Store/call-free loop, in-bounds fixed-slot load: hoists. The same
        // load must NOT hoist under the pure-only policy (O1).
        let body = vec![load(10, mem_slot(0, 0))];

        let mut func = make_self_loop(body.clone());
        func.stack_slots = vec![StackSlotInfo::new(8, 8)];
        let mut pass = X86LoopInvariantCodeMotion::pure_only();
        assert!(
            !pass.run_on_function(&mut func),
            "pure-only policy must not move loads"
        );

        let mut func = make_self_loop(body);
        func.stack_slots = vec![StackSlotInfo::new(8, 8)];
        let mut pass = X86LoopInvariantCodeMotion::with_invariant_load_hoisting();
        assert!(pass.run_on_function(&mut func), "invariant load hoists");
        assert_eq!(
            count_opcode(block_insts(&func, Block(1)), X86Opcode::MovRM),
            0
        );
        let ph = block_insts(&func, Block(0));
        assert_eq!(count_opcode(ph, X86Opcode::MovRM), 1);
        assert_eq!(ph[0].operands, vec![vreg(10), mem_slot(0, 0)]);
    }

    #[test]
    fn x86_licm_load_tier_refuses_out_of_bounds_access() {
        // [slot0 + 4] with an 8-byte load in an 8-byte slot overhangs the
        // slot: not provably non-trapping, must NOT hoist.
        let body = vec![load(10, mem_slot(0, 4))];
        let mut func = make_self_loop(body);
        func.stack_slots = vec![StackSlotInfo::new(8, 8)];
        let mut pass = X86LoopInvariantCodeMotion::with_invariant_load_hoisting();
        assert!(!pass.run_on_function(&mut func));
        assert_eq!(
            count_opcode(block_insts(&func, Block(1)), X86Opcode::MovRM),
            1
        );
    }

    #[test]
    fn x86_licm_load_tier_refuses_load_from_stored_slot() {
        // REFUTATION: in-loop store to the SAME slot the load reads. The
        // loaded value may change every iteration; must NOT hoist.
        let body = vec![store(mem_slot(0, 0), 20), load(10, mem_slot(0, 0))];
        let mut func = make_self_loop(body);
        func.stack_slots = vec![StackSlotInfo::new(8, 8)];
        let mut pass = X86LoopInvariantCodeMotion::with_invariant_load_hoisting();
        assert!(!pass.run_on_function(&mut func));
        let header = block_insts(&func, Block(1));
        assert_eq!(count_opcode(header, X86Opcode::MovRM), 1);
        assert_eq!(count_opcode(header, X86Opcode::MovMR), 1);
    }

    #[test]
    fn x86_licm_load_tier_refuses_partially_overlapping_stored_slot() {
        // REFUTATION: the store writes [slot0+0..1] and the load reads
        // [slot0+0..8]. Slot-granular disjointness must catch the overlap.
        let body = vec![
            X86ISelInst::new(X86Opcode::MovMR8, vec![mem_slot(0, 0), vreg(20)]),
            load(10, mem_slot(0, 0)),
        ];
        let mut func = make_self_loop(body);
        func.stack_slots = vec![StackSlotInfo::new(8, 8)];
        let mut pass = X86LoopInvariantCodeMotion::with_invariant_load_hoisting();
        assert!(!pass.run_on_function(&mut func));
        assert_eq!(
            count_opcode(block_insts(&func, Block(1)), X86Opcode::MovRM),
            1
        );
    }

    #[test]
    fn x86_licm_load_tier_refuses_everything_on_unresolvable_store() {
        // REFUTATION: a store through an unresolvable pointer could write ANY
        // escaped slot. Fail-safe: the tier disables for the whole loop —
        // even the load from a different, never-stored slot stays put.
        let body = vec![
            store(mem_vreg(30, 0), 20), // v30 has no def: unresolvable
            load(10, mem_slot(1, 0)),
        ];
        let mut func = make_self_loop(body);
        func.stack_slots = vec![StackSlotInfo::new(8, 8), StackSlotInfo::new(8, 8)];
        let mut pass = X86LoopInvariantCodeMotion::with_invariant_load_hoisting();
        assert!(!pass.run_on_function(&mut func));
        assert_eq!(
            count_opcode(block_insts(&func, Block(1)), X86Opcode::MovRM),
            1
        );
    }

    #[test]
    fn x86_licm_load_tier_hoists_load_disjoint_from_resolved_store() {
        // A store to slot1 (statically attributed) does not block hoisting a
        // load of never-stored slot0. The store itself stays in the loop.
        let body = vec![store(mem_slot(1, 0), 20), load(10, mem_slot(0, 0))];
        let mut func = make_self_loop(body);
        func.stack_slots = vec![StackSlotInfo::new(8, 8), StackSlotInfo::new(8, 8)];
        let mut pass = X86LoopInvariantCodeMotion::with_invariant_load_hoisting();
        assert!(pass.run_on_function(&mut func));
        let header = block_insts(&func, Block(1));
        assert_eq!(count_opcode(header, X86Opcode::MovRM), 0, "load hoisted");
        assert_eq!(count_opcode(header, X86Opcode::MovMR), 1, "store stays");
        assert_eq!(
            count_opcode(block_insts(&func, Block(0)), X86Opcode::MovRM),
            1
        );
    }

    #[test]
    fn x86_licm_load_tier_refuses_loop_with_call() {
        // REFUTATION: a call in the loop can write anything; hoist nothing.
        let body = vec![
            X86ISelInst::new(X86Opcode::Call, vec![X86ISelOperand::Symbol("f".into())]),
            load(10, mem_slot(0, 0)),
        ];
        let mut func = make_self_loop(body);
        func.stack_slots = vec![StackSlotInfo::new(8, 8)];
        let mut pass = X86LoopInvariantCodeMotion::with_invariant_load_hoisting();
        assert!(!pass.run_on_function(&mut func));
        assert_eq!(
            count_opcode(block_insts(&func, Block(1)), X86Opcode::MovRM),
            1
        );
    }

    #[test]
    fn x86_licm_load_tier_refuses_loop_with_fence() {
        // REFUTATION: a fence orders memory; no load may move across it.
        let body = vec![
            X86ISelInst::new(X86Opcode::Mfence, vec![]),
            load(10, mem_slot(0, 0)),
        ];
        let mut func = make_self_loop(body);
        func.stack_slots = vec![StackSlotInfo::new(8, 8)];
        let mut pass = X86LoopInvariantCodeMotion::with_invariant_load_hoisting();
        assert!(!pass.run_on_function(&mut func));
        assert_eq!(
            count_opcode(block_insts(&func, Block(1)), X86Opcode::MovRM),
            1
        );
    }

    #[test]
    fn x86_licm_load_tier_refuses_loop_with_atomic_or_volatile_marker() {
        // REFUTATION: an atomic/volatile load lowers to a plain MovRM with an
        // X86ProofOrigin marker. It must never hoist (a spin-wait would become
        // an infinite loop), and it disables the tier for the whole loop: the
        // OTHER plain load must not move above an acquire.
        let body = vec![
            load(11, mem_slot(1, 0)).with_proof_origin(X86ProofOrigin::AtomicLoad),
            load(10, mem_slot(0, 0)),
        ];
        let mut func = make_self_loop(body);
        func.stack_slots = vec![StackSlotInfo::new(8, 8), StackSlotInfo::new(8, 8)];
        let mut pass = X86LoopInvariantCodeMotion::with_invariant_load_hoisting();
        assert!(!pass.run_on_function(&mut func));
        assert_eq!(
            count_opcode(block_insts(&func, Block(1)), X86Opcode::MovRM),
            2
        );
    }

    #[test]
    fn x86_licm_load_tier_refuses_multi_def_destination() {
        // REFUTATION: two loads defining the same vreg are path-sensitive
        // carriers, not SSA values; neither may hoist.
        let body = vec![load(10, mem_slot(0, 0)), load(10, mem_slot(1, 0))];
        let mut func = make_self_loop(body);
        func.stack_slots = vec![StackSlotInfo::new(8, 8), StackSlotInfo::new(8, 8)];
        let mut pass = X86LoopInvariantCodeMotion::with_invariant_load_hoisting();
        assert!(!pass.run_on_function(&mut func));
        assert_eq!(
            count_opcode(block_insts(&func, Block(1)), X86Opcode::MovRM),
            2
        );
    }

    #[test]
    fn x86_licm_load_tier_refuses_aligned_vector_load() {
        // REFUTATION: MovdqaRM traps on unaligned addresses; the tier only
        // admits trap-free opcodes (speculation safety), so it stays put.
        let body = vec![X86ISelInst::new(
            X86Opcode::MovdqaRM,
            vec![
                X86ISelOperand::VReg(VReg::new(10, RegClass::Fpr128)),
                mem_slot(0, 0),
            ],
        )];
        let mut func = make_self_loop(body);
        func.stack_slots = vec![StackSlotInfo::new(16, 16)];
        let mut pass = X86LoopInvariantCodeMotion::with_invariant_load_hoisting();
        assert!(!pass.run_on_function(&mut func));
        assert_eq!(
            count_opcode(block_insts(&func, Block(1)), X86Opcode::MovdqaRM),
            1
        );
    }

    /// The h1_vec_push_sum shape: the pointer to a celled aggregate is stored
    /// once outside the loop, re-loaded inside the loop, and the aggregate's
    /// lanes are loaded through it.
    ///
    /// ```text
    ///   bb0: v1 = lea [slot1]        (aggregate address)
    ///        [slot0] = v1            (cell the pointer)
    ///        jmp bb1
    ///   bb1: v2 = mov [slot0]        (re-load celled pointer)   <- hoists
    ///        v3 = mov [v2 + 8]       (load aggregate lane)      <- hoists
    ///        jcc bb1 / fallthrough bb2
    /// ```
    fn make_celled_pointer_loop() -> X86ISelFunction {
        let body = vec![load(2, mem_slot(0, 0)), load(3, mem_vreg(2, 8))];
        let mut func = make_self_loop(body);
        func.stack_slots = vec![StackSlotInfo::new(8, 8), StackSlotInfo::new(24, 8)];
        // Prepend the celled-pointer setup to bb0 (before its jmp).
        let bb0 = Block(0);
        let setup = vec![
            X86ISelInst::new(X86Opcode::Lea, vec![vreg(1), mem_slot(1, 0)]),
            store(mem_slot(0, 0), 1),
        ];
        let ph = func.blocks.get_mut(&bb0).unwrap();
        for (i, inst) in setup.into_iter().enumerate() {
            ph.insts.insert(i, inst);
        }
        func
    }

    #[test]
    fn x86_licm_load_tier_forwards_celled_pointer_chain() {
        let mut func = make_celled_pointer_loop();
        let mut pass = X86LoopInvariantCodeMotion::with_invariant_load_hoisting();
        assert!(pass.run_on_function(&mut func));
        let header = block_insts(&func, Block(1));
        assert_eq!(
            count_opcode(header, X86Opcode::MovRM),
            0,
            "both the celled-pointer re-load and the lane load hoist"
        );
        let ph = block_insts(&func, Block(0));
        assert_eq!(count_opcode(ph, X86Opcode::MovRM), 2);
        // Discovery order respects the dependency: v2's load precedes v3's.
        let loads: Vec<&X86ISelInst> = ph.iter().filter(|i| i.opcode == X86Opcode::MovRM).collect();
        assert_eq!(loads[0].operands[0], vreg(2));
        assert_eq!(loads[1].operands[0], vreg(3));
    }

    #[test]
    fn x86_licm_load_tier_forwarding_requires_non_escaped_cell() {
        // REFUTATION: once the cell slot's address is materialized anywhere,
        // an unknown writer could exist between the celled store and the
        // loop, so the forwarded lane load must NOT hoist. (The direct
        // re-load of the never-stored-in-loop cell itself may still hoist:
        // with a store/call-free loop nothing can change it mid-loop.)
        let mut func = make_celled_pointer_loop();
        // Escape slot0 in the exit block.
        func.push_inst(
            Block(2),
            X86ISelInst::new(X86Opcode::Lea, vec![vreg(9), mem_slot(0, 0)]),
        );
        let mut pass = X86LoopInvariantCodeMotion::with_invariant_load_hoisting();
        pass.run_on_function(&mut func);
        let header = block_insts(&func, Block(1));
        assert!(
            header
                .iter()
                .any(|i| i.opcode == X86Opcode::MovRM && i.operands[0] == vreg(3)),
            "lane load through the escaped cell must stay in the loop"
        );
    }

    #[test]
    fn x86_licm_load_tier_forwarding_requires_unique_cell_store() {
        // REFUTATION: two direct stores to the cell slot make the forwarded
        // pointer value ambiguous; the lane load must NOT hoist.
        let mut func = make_celled_pointer_loop();
        // Second direct store to slot0 in the exit block (value irrelevant).
        func.push_inst(Block(2), store(mem_slot(0, 0), 1));
        let mut pass = X86LoopInvariantCodeMotion::with_invariant_load_hoisting();
        pass.run_on_function(&mut func);
        let header = block_insts(&func, Block(1));
        assert!(
            header
                .iter()
                .any(|i| i.opcode == X86Opcode::MovRM && i.operands[0] == vreg(3)),
            "lane load with ambiguous cell store must stay in the loop"
        );
    }

    #[test]
    fn x86_licm_load_tier_forwarded_lane_out_of_bounds_refused() {
        // REFUTATION: lane offset 24 with an 8-byte load overhangs the
        // 24-byte aggregate slot; not provably non-trapping.
        let body = vec![load(2, mem_slot(0, 0)), load(3, mem_vreg(2, 24))];
        let mut func = make_self_loop(body);
        func.stack_slots = vec![StackSlotInfo::new(8, 8), StackSlotInfo::new(24, 8)];
        let bb0 = Block(0);
        let setup = vec![
            X86ISelInst::new(X86Opcode::Lea, vec![vreg(1), mem_slot(1, 0)]),
            store(mem_slot(0, 0), 1),
        ];
        let ph = func.blocks.get_mut(&bb0).unwrap();
        for (i, inst) in setup.into_iter().enumerate() {
            ph.insts.insert(i, inst);
        }
        let mut pass = X86LoopInvariantCodeMotion::with_invariant_load_hoisting();
        pass.run_on_function(&mut func);
        let header = block_insts(&func, Block(1));
        assert!(
            header
                .iter()
                .any(|i| i.opcode == X86Opcode::MovRM && i.operands[0] == vreg(3)),
            "out-of-bounds lane load must stay in the loop"
        );
    }

    #[test]
    fn x86_licm_load_tier_runtime_sized_slot_refused() {
        // REFUTATION: runtime-sized slots have no static bound; never hoist.
        use trust_cg_ir::function::StackSlotSizeSource;
        let body = vec![load(10, mem_slot(0, 0))];
        let mut func = make_self_loop(body);
        func.stack_slots = vec![StackSlotInfo::new_dynamic(StackSlotSizeSource::Unknown, 8)];
        let mut pass = X86LoopInvariantCodeMotion::with_invariant_load_hoisting();
        assert!(!pass.run_on_function(&mut func));
        assert_eq!(
            count_opcode(block_insts(&func, Block(1)), X86Opcode::MovRM),
            1
        );
    }

    // =======================================================================
    // Lever-B: invariant flag-writing-arithmetic (imul) tier
    // =======================================================================

    fn imul_rr(dst: u32, a: u32, b: u32) -> X86ISelInst {
        X86ISelInst::new(X86Opcode::ImulRR, vec![vreg(dst), vreg(a), vreg(b)])
    }
    fn cmp_ri(r: u32, v: i64) -> X86ISelInst {
        X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(r), imm(v)])
    }

    #[test]
    fn x86_licm_flag_arith_hoists_invariant_imul_with_dead_flags() {
        // v11=3, v12=5 invariant; v10 = v11*v12 (imul, flag writer) invariant.
        // A `cmp` fully re-defines flags before the loop's `jcc`, so the imul's
        // written flags are provably dead (condition a) and the header clobbers
        // flags before its reader (condition b) -> the imul hoists.
        let body = vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(11), imm(3)]),
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(12), imm(5)]),
            imul_rr(10, 11, 12),
            cmp_ri(13, 0),
        ];
        let mut func = make_self_loop(body);
        let mut pass = X86LoopInvariantCodeMotion::with_invariant_load_hoisting();
        assert!(pass.run_on_function(&mut func));
        let header = block_insts(&func, Block(1));
        assert_eq!(
            count_opcode(header, X86Opcode::ImulRR),
            0,
            "invariant imul with dead flags hoisted out of the loop"
        );
        // cmp + jcc remain in the header.
        assert_eq!(count_opcode(header, X86Opcode::CmpRI), 1, "cmp stays");
        let ph = block_insts(&func, Block(0));
        assert_eq!(count_opcode(ph, X86Opcode::ImulRR), 1, "imul in preheader");
        // The hoisted imul must follow its (also-hoisted) invariant inputs.
        let imul_pos = ph
            .iter()
            .position(|i| i.opcode == X86Opcode::ImulRR)
            .unwrap();
        let mov_count_before = ph
            .iter()
            .take(imul_pos)
            .filter(|i| i.opcode == X86Opcode::MovRI)
            .count();
        assert_eq!(mov_count_before, 2, "both operand movs precede the imul");
    }

    /// The three-address integer ALU forms hoist under the SAME conditions as
    /// the `imul` above. `p8_closure_nest` recomputed a loop-invariant `17 | 1`
    /// on every iteration purely because `OrRR` was missing from the allowlist.
    #[test]
    fn x86_licm_flag_arith_hoists_invariant_alu_rr_forms() {
        for op in [
            X86Opcode::OrRR,
            X86Opcode::AndRR,
            X86Opcode::XorRR,
            X86Opcode::AddRR,
            X86Opcode::SubRR,
        ] {
            let body = vec![
                X86ISelInst::new(X86Opcode::MovRI, vec![vreg(11), imm(17)]),
                X86ISelInst::new(X86Opcode::MovRI, vec![vreg(12), imm(1)]),
                X86ISelInst::new(op, vec![vreg(10), vreg(11), vreg(12)]),
                cmp_ri(13, 0),
            ];
            let mut func = make_self_loop(body);
            let mut pass = X86LoopInvariantCodeMotion::with_invariant_load_hoisting();
            assert!(pass.run_on_function(&mut func), "{op:?} pass ran");
            assert_eq!(
                count_opcode(block_insts(&func, Block(1)), op),
                0,
                "invariant {op:?} with dead flags must leave the loop"
            );
            assert_eq!(
                count_opcode(block_insts(&func, Block(0)), op),
                1,
                "{op:?} must land in the preheader"
            );
        }
    }

    /// REFUTATION: the same ALU forms must obey the flag-liveness condition —
    /// with no full definer between them and the `jcc`, their flags are observed
    /// and they must stay. This is the condition that makes the tier sound, so
    /// it must hold for the newly-admitted opcodes and not just for `imul`.
    #[test]
    fn x86_licm_flag_arith_alu_refuses_when_flags_observed() {
        for op in [X86Opcode::OrRR, X86Opcode::AddRR, X86Opcode::XorRR] {
            let body = vec![
                X86ISelInst::new(X86Opcode::MovRI, vec![vreg(11), imm(17)]),
                X86ISelInst::new(X86Opcode::MovRI, vec![vreg(12), imm(1)]),
                X86ISelInst::new(op, vec![vreg(10), vreg(11), vreg(12)]),
            ];
            let mut func = make_self_loop(body);
            let mut pass = X86LoopInvariantCodeMotion::with_invariant_load_hoisting();
            pass.run_on_function(&mut func);
            assert_eq!(
                count_opcode(block_insts(&func, Block(1)), op),
                1,
                "{op:?} whose flags reach the jcc must stay in the loop"
            );
        }
    }

    /// REFUTATION: `AdcRR` READS CF. Relocating a flag reader would make it
    /// observe flags from the wrong dynamic point, so it must never hoist —
    /// `x86_reads_flags` is what keeps it out, and that guard has to survive
    /// the allowlist widening.
    #[test]
    fn x86_licm_flag_arith_refuses_flag_reader_adc() {
        let body = vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(11), imm(17)]),
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(12), imm(1)]),
            X86ISelInst::new(X86Opcode::AdcRR, vec![vreg(10), vreg(11), vreg(12)]),
            cmp_ri(13, 0),
        ];
        let mut func = make_self_loop(body);
        let mut pass = X86LoopInvariantCodeMotion::with_invariant_load_hoisting();
        pass.run_on_function(&mut func);
        assert_eq!(
            count_opcode(block_insts(&func, Block(1)), X86Opcode::AdcRR),
            1,
            "a flag READER must never be relocated"
        );
    }

    #[test]
    fn x86_licm_flag_arith_refuses_when_flags_observed_by_jcc() {
        // REFUTATION: no intervening full flag definer between the imul and the
        // loop's `jcc`, so the imul's flags are observed (it could BE the loop
        // condition). Condition (a)/(b) both fail -> the imul must NOT hoist.
        let body = vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(11), imm(3)]),
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(12), imm(5)]),
            imul_rr(10, 11, 12),
        ];
        let mut func = make_self_loop(body);
        let mut pass = X86LoopInvariantCodeMotion::with_invariant_load_hoisting();
        pass.run_on_function(&mut func);
        let header = block_insts(&func, Block(1));
        assert_eq!(
            count_opcode(header, X86Opcode::ImulRR),
            1,
            "imul whose flags reach the jcc must stay in the loop"
        );
    }

    #[test]
    fn x86_licm_flag_arith_refuses_variant_operand() {
        // REFUTATION: v11 is a multi-def carrier (loop-variant); the imul's input
        // is not invariant, so it must NOT hoist even with dead flags.
        let body = vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(11), imm(1)]),
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(11), imm(2)]), // multi-def
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(12), imm(5)]),
            imul_rr(10, 11, 12),
            cmp_ri(13, 0),
        ];
        let mut func = make_self_loop(body);
        let mut pass = X86LoopInvariantCodeMotion::with_invariant_load_hoisting();
        pass.run_on_function(&mut func);
        let header = block_insts(&func, Block(1));
        assert!(
            header.iter().any(|i| i.opcode == X86Opcode::ImulRR),
            "imul with a loop-variant operand must stay"
        );
    }

    #[test]
    fn x86_licm_flag_arith_kill_switch_keeps_imul() {
        // With the Lever-B tier disabled, an otherwise-hoistable invariant imul
        // stays in the loop (the load tier is unaffected).
        let body = vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(11), imm(3)]),
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(12), imm(5)]),
            imul_rr(10, 11, 12),
            cmp_ri(13, 0),
        ];
        let mut func = make_self_loop(body);
        let mut pass =
            X86LoopInvariantCodeMotion::with_invariant_load_hoisting().with_flag_arith(false);
        pass.run_on_function(&mut func);
        let header = block_insts(&func, Block(1));
        assert_eq!(
            count_opcode(header, X86Opcode::ImulRR),
            1,
            "kill switch: invariant imul stays in the loop"
        );
    }

    #[test]
    fn x86_licm_flag_arith_pure_only_keeps_imul() {
        // The pure-only (O1) policy never enables the flag-arith tier.
        let body = vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(11), imm(3)]),
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(12), imm(5)]),
            imul_rr(10, 11, 12),
            cmp_ri(13, 0),
        ];
        let mut func = make_self_loop(body);
        let mut pass = X86LoopInvariantCodeMotion::pure_only();
        pass.run_on_function(&mut func);
        let header = block_insts(&func, Block(1));
        assert_eq!(
            count_opcode(header, X86Opcode::ImulRR),
            1,
            "pure-only policy: invariant imul stays in the loop"
        );
    }

    // ---- X5 value-level net (verify_preheader_defs_precede_uses) -----------

    /// One-block function holding `insts` in order; drives the def-before-use net.
    fn one_block(insts: Vec<X86ISelInst>) -> (X86ISelFunction, Block) {
        let sig = Signature {
            params: vec![],
            returns: vec![Type::I64],
        };
        let mut func = X86ISelFunction::new("x5_x86_net".to_string(), sig);
        let bb = Block(0);
        func.ensure_block(bb);
        func.next_vreg = 64;
        for inst in insts {
            func.push_inst(bb, inst);
        }
        (func, bb)
    }

    #[test]
    fn x5_x86_net_accepts_def_before_use() {
        // movri v0,#5 ; movrr v2 <- v0  — v0 defined (idx 0) before its use (idx 1).
        let (func, bb) = one_block(vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(0), imm(5)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(2), vreg(0)]),
        ]);
        let dc = build_def_counts(&func);
        verify_preheader_defs_precede_uses(&func, bb, &dc); // must NOT panic
    }

    #[test]
    #[should_panic(expected = "use-before-def")]
    fn x5_x86_net_fires_on_use_before_def() {
        // movrr v2 <- v0 (reads v0 at idx 0) ; movri v0,#5 (its ONLY def at idx 1).
        let (func, bb) = one_block(vec![
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(2), vreg(0)]),
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(0), imm(5)]),
        ]);
        let dc = build_def_counts(&func);
        verify_preheader_defs_precede_uses(&func, bb, &dc); // must panic
    }

    #[test]
    fn x5_x86_net_skips_multi_def_vreg() {
        // v0 defined TWICE — multi-def, so a use at idx 0 is conservatively not
        // flagged (it may read a dominating-block def under the non-SSA IR).
        let (func, bb) = one_block(vec![
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(2), vreg(0)]),
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(0), imm(5)]),
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(0), imm(6)]),
        ]);
        let dc = build_def_counts(&func);
        verify_preheader_defs_precede_uses(&func, bb, &dc); // must NOT panic
    }

    #[test]
    fn x5_x86_net_accepts_nested_address_def_before_use() {
        // The base is nested inside a MemAddr, not a top-level operand.  A
        // definition before the load is the valid control for the recursive
        // walk used by the X5 net.
        let address = X86ISelOperand::MemAddr {
            base: Box::new(vreg(0)),
            disp: 8,
        };
        let (func, bb) = one_block(vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(0), imm(5)]),
            X86ISelInst::new(X86Opcode::MovRM, vec![vreg(2), address]),
        ]);
        let dc = build_def_counts(&func);
        verify_preheader_defs_precede_uses(&func, bb, &dc); // must NOT panic
    }

    #[test]
    #[should_panic(expected = "use-before-def")]
    fn x5_x86_net_fires_on_nested_memaddr_use_before_def() {
        // Before the recursive walk this escaped the net: v0 was hidden inside
        // MemAddr, so only its later MovRI definition was observed.
        let address = X86ISelOperand::MemAddr {
            base: Box::new(vreg(0)),
            disp: 8,
        };
        let (func, bb) = one_block(vec![
            X86ISelInst::new(X86Opcode::MovRM, vec![vreg(2), address]),
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(0), imm(5)]),
        ]);
        let dc = build_def_counts(&func);
        verify_preheader_defs_precede_uses(&func, bb, &dc); // must panic
    }

    #[test]
    #[should_panic(expected = "use-before-def")]
    fn x5_x86_net_fires_on_nested_sib_index_use_before_def() {
        // Exercise the other recursive arm independently: the base is an entry
        // value, while the SIB index has its sole definition after the use.
        let address = X86ISelOperand::SibMemAddr {
            base: Box::new(vreg(1)),
            index: Box::new(vreg(0)),
            scale: 4,
            disp: 16,
        };
        let (func, bb) = one_block(vec![
            X86ISelInst::new(X86Opcode::LeaSib, vec![vreg(2), address]),
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(0), imm(5)]),
        ]);
        let dc = build_def_counts(&func);
        verify_preheader_defs_precede_uses(&func, bb, &dc); // must panic
    }

    // ---- Nested-loop guarded-hoist fixture (the b05 shape) ----
    use trust_cg_lower::function::StackSlotInfo as GhSlot;

    fn gh_guarded_pass() -> X86LoopInvariantCodeMotion {
        X86LoopInvariantCodeMotion {
            hoist_invariant_loads: true,
            guarded_hoist: true,
            hoist_flag_arith: false,
        }
    }

    /// r-loop { r-guard(r<24); col-loop { col-guard; c[r][col]=..; s+=a[r][k0]; col++ } r++ }
    /// slot0='a' (loaded), slot1='c' (stored); both 4608 bytes. The inner
    /// (col) loop is the hoist target: a[r][k0] is col-invariant.
    /// `r_copy` inserts a MovRR copy of r captured across the inner header,
    /// so the guard names a copy (exercises the invariance-gated traversal).
    fn make_nested(r_copy: bool) -> X86ISelFunction {
        let sig = Signature {
            params: vec![],
            returns: vec![Type::I64],
        };
        let mut f = X86ISelFunction::new("gh_nested".into(), sig);
        for b in 0..7u32 {
            f.ensure_block(Block(b));
        }
        f.next_vreg = 300;
        f.stack_slots = vec![GhSlot::new(4608, 8), GhSlot::new(4608, 8)];
        let vr = |id: u32| X86ISelOperand::VReg(VReg::new(id, RegClass::Gpr64));
        let cc = X86ISelOperand::CondCode(trust_cg_ir::X86CondCode::B);
        let blk = |b: u32| X86ISelOperand::Block(Block(b));
        let push = |f: &mut X86ISelFunction, b: u32, op: X86Opcode, ops: Vec<X86ISelOperand>| {
            f.push_inst(Block(b), X86ISelInst::new(op, ops));
        };
        let mem = |base: u32, disp: i32| X86ISelOperand::MemAddr {
            base: Box::new(X86ISelOperand::VReg(VReg::new(base, RegClass::Gpr64))),
            disp,
        };
        let slot = |s: u32, disp: i32| X86ISelOperand::MemAddr {
            base: Box::new(X86ISelOperand::StackSlot(s)),
            disp,
        };

        // B0 outer-preheader: r(v10)=0 ; jmp B1
        push(&mut f, 0, X86Opcode::MovRI, vec![vr(10), imm(0)]);
        push(&mut f, 0, X86Opcode::Jmp, vec![blk(1)]);
        f.blocks.get_mut(&Block(0)).unwrap().successors = vec![Block(1)];

        // B1 outer-header: cmp r,24 ; jcc B2 ; jmp B6
        push(&mut f, 1, X86Opcode::CmpRI, vec![vr(10), imm(24)]);
        push(&mut f, 1, X86Opcode::Jcc, vec![cc.clone(), blk(2)]);
        push(&mut f, 1, X86Opcode::Jmp, vec![blk(6)]);
        f.blocks.get_mut(&Block(1)).unwrap().successors = vec![Block(2), Block(6)];

        // B2 inner-preheader (outer body): [r-copy?] ; guard(r|rc <24) ; col(v11)=0 ; jmp B3
        let rguard = if r_copy {
            push(&mut f, 2, X86Opcode::MovRR, vec![vr(20), vr(10)]);
            20
        } else {
            10
        };
        push(
            &mut f,
            2,
            X86Opcode::TrapBoundsCheckExact,
            vec![vr(90), vr(rguard), imm(24)],
        );
        push(&mut f, 2, X86Opcode::MovRI, vec![vr(11), imm(0)]);
        push(&mut f, 2, X86Opcode::Jmp, vec![blk(3)]);
        f.blocks.get_mut(&Block(2)).unwrap().successors = vec![Block(3)];

        // B3 inner-header: cmp col,24 ; jcc B4 ; jmp B5
        push(&mut f, 3, X86Opcode::CmpRI, vec![vr(11), imm(24)]);
        push(&mut f, 3, X86Opcode::Jcc, vec![cc.clone(), blk(4)]);
        push(&mut f, 3, X86Opcode::Jmp, vec![blk(5)]);
        f.blocks.get_mut(&Block(3)).unwrap().successors = vec![Block(4), Block(5)];

        // B4 inner-body/latch:
        //   col-guard(col<24)
        //   store c[r][col]: lea v30=[slot1] ; v31=r*192 ; v32=v30+v31 ; v33=col*8 ; v34=v32+v33 ; [v34]=v40
        //   load  a[r][k0]:  lea v50=[slot0] ; v51=r*192 ; v52=v50+v51 ; v53=[v52]
        //   s+=a: v41=v41+v53 ; col++ ; jmp B3
        push(
            &mut f,
            4,
            X86Opcode::TrapBoundsCheckExact,
            vec![vr(91), vr(11), imm(24)],
        );
        push(&mut f, 4, X86Opcode::Lea, vec![vr(30), slot(1, 0)]);
        push(
            &mut f,
            4,
            X86Opcode::ImulRRI,
            vec![vr(31), vr(10), imm(192)],
        );
        push(&mut f, 4, X86Opcode::AddRR, vec![vr(32), vr(30), vr(31)]);
        push(&mut f, 4, X86Opcode::ImulRRI, vec![vr(33), vr(11), imm(8)]);
        push(&mut f, 4, X86Opcode::AddRR, vec![vr(34), vr(32), vr(33)]);
        push(&mut f, 4, X86Opcode::MovMR, vec![mem(34, 0), vr(40)]);
        push(&mut f, 4, X86Opcode::Lea, vec![vr(50), slot(0, 0)]);
        push(
            &mut f,
            4,
            X86Opcode::ImulRRI,
            vec![vr(51), vr(10), imm(192)],
        );
        push(&mut f, 4, X86Opcode::AddRR, vec![vr(52), vr(50), vr(51)]);
        push(&mut f, 4, X86Opcode::MovRM, vec![vr(53), mem(52, 0)]);
        push(&mut f, 4, X86Opcode::AddRR, vec![vr(41), vr(41), vr(53)]);
        push(&mut f, 4, X86Opcode::AddRI, vec![vr(11), vr(11), imm(1)]);
        push(&mut f, 4, X86Opcode::Jmp, vec![blk(3)]);
        f.blocks.get_mut(&Block(4)).unwrap().successors = vec![Block(3)];

        // B5 inner-exit / outer-latch: r++ ; jmp B1
        push(&mut f, 5, X86Opcode::AddRI, vec![vr(10), vr(10), imm(1)]);
        push(&mut f, 5, X86Opcode::Jmp, vec![blk(1)]);
        f.blocks.get_mut(&Block(5)).unwrap().successors = vec![Block(1)];

        // B6 outer-exit: ret
        push(&mut f, 6, X86Opcode::Ret, vec![]);
        f
    }

    fn inner_load_count(f: &X86ISelFunction) -> usize {
        block_insts(f, Block(4))
            .iter()
            .filter(|i| i.opcode == X86Opcode::MovRM)
            .count()
    }

    #[test]
    fn gh_nested_direct_names_hoists_inner_load() {
        let mut f = make_nested(false);
        let fired = gh_guarded_pass().run_on_function(&mut f);
        assert!(fired, "guarded hoist must fire on the nested b05 shape");
        assert_eq!(
            inner_load_count(&f),
            0,
            "the a[r][k0] load must leave the inner loop"
        );
        // The load's dst v53 is now a MovRR copy of a hoisted vreg.
        let copy = block_insts(&f, Block(4))
            .iter()
            .find(|i| i.opcode == X86Opcode::MovRR && i.operands.first() == Some(&vreg(53)));
        assert!(copy.is_some(), "in-loop load replaced by dst=MovRR H");
    }

    #[test]
    fn gh_nested_copy_captured_guard_hoists() {
        // The r-guard names a COPY of r captured across the inner header:
        // exercises the invariance-gated preheader-edge terminal matching.
        let mut f = make_nested(true);
        let fired = gh_guarded_pass().run_on_function(&mut f);
        assert!(fired, "must fire when the r-guard names a copy of r");
        assert_eq!(inner_load_count(&f), 0);
    }
}
