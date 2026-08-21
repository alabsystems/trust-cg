// trust-cg-opt - Loop-Invariant Code Motion
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Loop-Invariant Code Motion (LICM) for machine-level IR.
//!
//! Hoists loop-invariant instructions to the loop preheader, reducing
//! redundant computation inside loops.
//!
//! # Safety Requirements
//!
//! **Pure instructions and a restricted class of loads are hoisted.** The
//! memory-effects model classifies each opcode. `MemoryEffect::Pure`
//! instructions can always be safely moved out of loops. Stores and calls
//! are NEVER hoisted (their side effects must execute each iteration).
//!
//! Loads are hoisted only under the tiered rules in `load_is_admissible`,
//! which reconstruct the classic LICM safety argument at the machine level:
//! - **Address invariance.** Pre-regalloc loads are `LdrRI dst, base, #off`
//!   with no `MemOp`, so the base register and offset are ordinary operands
//!   the existing invariance engine already reasons about. Only a load whose
//!   address operands are all loop-invariant is a candidate.
//! - **Value stability (aliasing).** A hoisted load must read the same value
//!   on every iteration. Tier (a): a loop that neither writes memory nor
//!   calls/barriers cannot clobber the address, so any invariant load is
//!   value-stable. Tier (b): when the loop DOES write memory, the load is
//!   admitted only when a cheap static predicate proves it disjoint from
//!   every in-loop store (distinct globals, distinct stack slots, or
//!   stack-vs-global — see `addr_bases_disjoint`); any store we cannot
//!   classify fails the loop closed.
//! - **Speculation (fault) safety.** Hoisting to the preheader must not
//!   introduce a fault on a zero-trip or early-exit path. The load is
//!   admitted only when it is GUARANTEED TO EXECUTE: its block dominates
//!   EVERY latch (back-edge source, not just the cached `lp.latch`) and every
//!   loop-exiting block, AND the preheader unconditionally
//!   enters the loop (so reaching the preheader implies the loop body runs at
//!   least once). See `load_guaranteed_to_execute`.
//! - **Excluded load forms.** Pre/post-index writeback loads (they redefine
//!   the base), load-pairs (two defs), register-offset and GOT/TLS/literal
//!   loads, and acquire/atomic loads (`Ldar*`) are never hoisted.
//!
//! **Only SSA-modeled virtual-register definitions are hoisted.** Physical
//! registers and special machine registers carry ABI state and fixed
//! instruction constraints that are not represented in LICM's virtual-register
//! def map. Moving call glue such as `x16 <- target` away from `blr x16`, or
//! moving `ret <- x0` away from a call, is unsound even if the opcode is
//! otherwise classified as pure.
//!
//! # Loop Invariance
//!
//! An instruction is loop-invariant if ALL its source operands are:
//! - Defined outside the loop, OR
//! - Themselves loop-invariant (transitive).
//!
//! # Algorithm
//!
//! 1. Compute dominator tree and loop analysis.
//! 2. For each loop (innermost first for best results), ensure a preheader,
//!    build the def-map, identify pure loop-invariant instructions, and hoist
//!    them to the preheader.
//! 3. Iterate until no more instructions can be hoisted.
//!
//! # Provenance
//!
//! LICM is provenance-neutral: hoisting removes an existing `InstId` from the
//! loop block's instruction list and inserts the same `InstId` into the
//! preheader. It does not mutate the `MachInst`, create/delete instructions, or
//! change source mappings, so provenance-aware hooks intentionally leave
//! `ProvenanceMap` unchanged.
//!
//! Reference: LLVM `LICM.cpp`

use std::collections::{HashMap, HashSet};

use trust_cg_ir::aarch64_regs::{X0, gpr32_to_gpr64, preg_class};
use trust_cg_ir::{
    AArch64Opcode, BlockId, InstId, MachFunction, MachInst, MachOperand, PReg, ProofAnnotation,
    ProvenanceMap, RegClass, StackSlotId, VReg,
};

use crate::dom::DomTree;
use crate::effects::{
    aarch64_for_each_use_position, for_each_inst_def, inst_defines_vreg, opcode_effect,
    produces_value, reads_flags, single_inst_def, writes_flags,
};
use crate::interfaces::OpInterfaces;
use crate::loops::{LoopAnalysis, NaturalLoop};
use crate::pass_manager::{AnalysisCache, MachinePass};

/// Loop-Invariant Code Motion pass.
pub struct LoopInvariantCodeMotion;

impl MachinePass for LoopInvariantCodeMotion {
    fn name(&self) -> &str {
        "licm"
    }

    fn run(&mut self, func: &mut MachFunction) -> bool {
        let dom = DomTree::compute(func);
        let loop_analysis = LoopAnalysis::compute(func, &dom);
        Self::run_with_loop_analysis(func, &loop_analysis)
    }

    fn run_with_analyses(&mut self, func: &mut MachFunction, analyses: &mut AnalysisCache) -> bool {
        let loop_analysis = analyses.loop_analysis(func).clone();
        Self::run_with_loop_analysis(func, &loop_analysis)
    }

    fn run_with_provenance(
        &mut self,
        func: &mut MachFunction,
        _provenance: &mut ProvenanceMap,
    ) -> bool {
        // Hoisting only changes where existing InstIds appear in block lists.
        // Provenance is keyed by InstId and encoding offsets are assigned after
        // optimization, so there is no source/provenance transform to record.
        self.run(func)
    }

    fn run_with_analyses_and_provenance(
        &mut self,
        func: &mut MachFunction,
        analyses: &mut AnalysisCache,
        _provenance: &mut ProvenanceMap,
    ) -> bool {
        // Same no-op provenance rationale as run_with_provenance, while still
        // using the cached loop analysis path.
        let loop_analysis = analyses.loop_analysis(func).clone();
        Self::run_with_loop_analysis(func, &loop_analysis)
    }
}

impl LoopInvariantCodeMotion {
    fn run_with_loop_analysis(func: &mut MachFunction, loop_analysis: &LoopAnalysis) -> bool {
        if loop_analysis.is_empty() {
            return false;
        }

        let mut changed = false;

        // Region-LICM (aarch64 port of the x86 S4 region-LICM v2 whole-loop
        // hoist, `x86_licm.rs::region_licm_hoist`): hoist a provably
        // outer-invariant inner LOOP out of its enclosing loop so it runs once
        // instead of every outer iteration. OPT-IN and DEFAULT-OFF behind
        // `TCG_A64_REGION_LICM`: when the variable is unset this is a single
        // env probe and the pass below is byte-identical to before. Each
        // successful hoist rewires the CFG, so the stage recomputes its own
        // dominators/loops per round, and the instruction tiers below run on a
        // freshly recomputed loop analysis.
        let recomputed_after_region;
        let loop_analysis = if region_licm_enabled() && region_licm_run(func) {
            changed = true;
            let dom = DomTree::compute(func);
            recomputed_after_region = LoopAnalysis::compute(func, &dom);
            &recomputed_after_region
        } else {
            loop_analysis
        };

        // The dominator tree is needed by the load speculation guard. The
        // instruction tiers below only ever MOVE existing instructions between
        // existing blocks (they refuse synthetic preheaders), so they never
        // mutate the CFG: one dominator tree computed here — after any region
        // surgery above — stays valid across every hoist in this function.
        let dom = DomTree::compute(func);

        // Process loops innermost-first (higher depth first).
        let mut loops: Vec<_> = loop_analysis.all_loops().cloned().collect();
        loops.sort_by_key(|lp| std::cmp::Reverse(lp.depth));

        // Whole-function VReg maps, built ONCE for the whole scan rather than
        // once per loop.
        //
        // `hoist_loop_invariants` used to rebuild both on every call, and it is
        // called once per natural loop, so a function with many loops paid
        // O(loops x function) — the dominant term in this pass on block-dense
        // code (many_fns: licm 38.6ms -> 150.5ms for a 2x block count, 3.90x).
        //
        // Reusing them across loops is sound because the scan only MOVES
        // instructions into preheaders: a move preserves both the number of
        // definitions of a vreg and the InstId that defines it, which is all
        // these two maps record (neither stores a block). The CFG surgery that
        // does create instructions, `region_licm_hoist`, has already run above,
        // and the one instruction it creates is a `B` branch with no modeled
        // definition positions, so it is absent from both maps.
        let def_counts = build_def_counts(func);
        let def_map = build_def_map(func);

        for lp in &loops {
            if std::env::var_os("TCG_DUMP_CHAINS").is_some() {
                let mut b: Vec<u32> = lp.body.iter().map(|x| x.0).collect();
                b.sort_unstable();
                eprintln!(
                    "TCG_CHAIN loop header={} latch={} preheader={:?} body={:?}",
                    lp.header.0,
                    lp.latch.0,
                    lp.preheader.map(|p| p.0),
                    b
                );
            }
            if hoist_loop_invariants(func, lp, &dom, &def_counts, &def_map) {
                changed = true;
            }
        }

        // Pure-call cluster hoist tier (aarch64 port of the x86
        // `x86_licm.rs::hoist_pure_call_clusters` ackermann-class invariant-call
        // lever). OPT-IN, DEFAULT-OFF behind `TCG_A64_PURE_CALL_HOIST`; when the
        // variable is unset this is a single env probe and the pass below is
        // byte-identical to before. Reuses the loops/dom computed above — the
        // cluster hoist only MOVES instructions between the loop body and its
        // preheader, never mutating the CFG or the whole-function single-def
        // counts (so the freshly recomputed `def_counts` stays valid).
        if pure_call_hoist_enabled() {
            let def_counts = build_def_counts(func);
            for lp in &loops {
                if hoist_pure_call_clusters(func, lp, &def_counts, &dom) {
                    changed = true;
                }
            }
        }

        changed
    }
}

/// Hoist loop-invariant instructions from a single loop to its preheader.
///
/// Returns true if any instructions were hoisted.
fn hoist_loop_invariants(
    func: &mut MachFunction,
    lp: &NaturalLoop,
    dom: &DomTree,
    def_counts: &HashMap<VReg, usize>,
    def_map: &HashMap<VReg, InstId>,
) -> bool {
    // LICM currently hoists by physically moving instructions into an existing
    // preheader block. Creating a synthetic preheader here is not sound yet:
    // `create_preheader()` rewires CFG edges but does not repair header Phi /
    // block-arg semantics. That is exactly the kind of loop shape the sparse
    // substitute reducer exercises, with join-heavy headers carrying values
    // from multiple predecessors. Be conservative and skip such loops until
    // preheader synthesis becomes SSA-aware.
    let preheader = match lp.preheader {
        Some(ph) => ph,
        None => return false,
    };

    // Defense in depth against malformed or stale loop-analysis metadata.  A
    // real preheader is outside the loop and dominates its header.  In
    // particular, a header self-edge plus another latch used to leave the
    // second latch cached as a preheader after the loop bodies were merged;
    // moving a header definition there could place it after an existing use.
    if lp.body.contains(&preheader) || !dom.dominates(preheader, lp.header) {
        return false;
    }

    // Build def maps before classifying invariants. Trust Codegen machine IR is not
    // guaranteed to be strict SSA after lowering: block-argument copies and
    // materialization chains can reuse VRegs along different paths. LICM's
    // invariant set is keyed by full VReg identity, so hoisting a multi-def
    // VReg is unsound unless the pass models those path-sensitive definitions.
    // `def_counts` and `def_map` are supplied by the caller and built ONCE per
    // pass run — see `run_with_loop_analysis`.

    // Build a map: VReg -> (inst_id, block_id) for definitions inside the loop.
    let loop_defs = build_loop_defs(func, &lp.body);

    // Per-loop memory-write facts drive load admission: whether the loop writes
    // memory at all (tier a vs b), whether any writer is opaque (fails tier b
    // closed), and the classified base of every simple in-loop store.
    let mem_facts = compute_loop_memory_facts(func, lp, &def_map, &def_counts);

    // A hoisted load lands in the preheader, which executes unconditionally.
    // That is fault-safe against a zero-trip loop ONLY if reaching the preheader
    // already implies the loop body runs at least once, i.e. the preheader's
    // sole successor is the header. A rotated-loop guard block (which doubles as
    // the natural preheader and branches header/exit) fails this, keeping loads
    // out of loops whose trip count may be zero.
    let preheader_enters_loop = {
        let succs = &func.block(preheader).succs;
        succs.len() == 1 && succs[0] == lp.header
    };

    // Set of VRegs known to be loop-invariant.
    let mut invariant_vregs: HashSet<VReg> = HashSet::new();

    // Instructions to hoist: (inst_id, source_block).
    let mut to_hoist: Vec<(InstId, BlockId)> = Vec::new();

    // Multi-def constant chains sit outside the ordinary single-def X5 net.
    // Retain their exact carrier/InstId sequence so a dedicated per-instance
    // check can validate tied-def-use order after the splice.
    let mut constant_chains: Vec<(VReg, Vec<InstId>)> = Vec::new();

    // Constant-chain tier: hoist immediate materialization chains
    // (`MOVZ/MOVN/MOVI` head + `MOVK` patches) as a unit. Each such chain
    // defines a single GPR carrier that is (a) multiply-defined and (b) built
    // from a tied-def-use `MOVK`, so the per-instruction SSA/`is_pure` model
    // above never admits it — yet the carrier holds one compile-time constant
    // and is loop-invariant. Seeding the carrier into `invariant_vregs` and
    // pre-queuing its chain lets the whole chain move to the preheader AND
    // lets a consuming `FMOV Dn, Xcarrier` (non-encodable f64 literal) hoist
    // by the normal transitive path below, matching how encodable
    // `FmovImm` constants already lift out. Without this, fade/lerp-style f64
    // literals are re-materialized every iteration in perlin-class FP kernels,
    // and srem-by-constant magic reciprocals (the `MOVN/MOVK` of
    // 0x…80808081 in ReedSolomon's `% 255` loops) are re-materialized every
    // iteration in integer kernels.
    //
    // GATED on `lp.depth >= 2` (loop is itself nested): the tier only relocates
    // a chain to a strictly-less-frequent region that is STILL inside a loop —
    // it never performs the final "pull out of the OUTERMOST loop" step. That
    // last move shrinks a single hot loop's body and, on the measured target,
    // regresses tight FP kernels (flops-1/flops-7) for no critical-path benefit.
    // (This comment used to attribute that to "fetch alignment"; see the R3
    // control below — the regression is alignment-independent.) Deeply-nested kernels
    // (perlin's fade/lerp coefficients, live in the depth-3/4 inner loops) still
    // lift across every inner level and out of the hottest loops — only the
    // outermost-loop hoist they never needed is skipped. `depth` is 1-based
    // (outermost == 1), so a non-nested loop (`depth == 1`) is left untouched.
    // Depth-1 (non-nested) loops are admitted ONLY for MULTI-instruction constant
    // chains, gated behind `TCG_LICM_DEPTH1_MULTI`.
    //
    // The blanket depth-1 hoist was tried and reverted (475d949b): it regressed
    // flops-1 by 8% and flops-7 by 2.3%. That revert note attributed the loss to
    // "fetch-alignment effects when a single hot loop's body shrinks", and this
    // comment used to claim that requiring `chain.len() >= 2` "keeps the reverted
    // single-instruction case excluded while admitting the shape where the win is
    // large."
    //
    // ★ BOTH HALVES OF THAT CLAIM ARE FALSE — measured 2026-08-15, whole corpus,
    // tcg-vs-tcg (same .ll, same driver object, interleaved, min of 13, with a
    // byte-identical null arm on every row):
    //
    //   * The guard does NOT exclude the reverted regressions. flops-1 still loses
    //     8.15% and flops-7 1.73% WITH `chain.len() >= 2` in force — flops-1
    //     reproducing the cited 8% almost exactly. The chain it hoists there is a
    //     2-instruction `mov`+`movk` of the loop bound 0x12a05f20, admitted by
    //     precisely this guard.
    //   * It is NOT a fetch-alignment effect. Re-run under
    //     TCG_NO_LOOP_HEAD_ALIGN=1 the numbers are unchanged (flops-1 1.0815 vs
    //     1.0810, flops-3 0.7969 vs 0.7987, misr 1.0187 vs 1.0188), so R3 clears
    //     alignment as the cause. (Independently: 32-byte head alignment was
    //     priced at ZERO benefit on this target — see loop_align.rs.)
    //
    // What the arm actually does is PERTURB DOWNSTREAM PASSES. On flops-3 the
    // hoist suppresses a 4x unroll (`add x1,#4` -> `add x0,#1`), and the
    // un-unrolled form is 20% FASTER (0.7980/0.7997). Both flops programs run a
    // fixed 312.5M iterations (this llvm-test-suite copy is truncated to Module 1
    // with its outputs stabilized to `0 * 1e-30`, so `loops` never recalibrates),
    // giving exact per-iteration deltas: flops-1 -2 insts/iter for +8% cycles,
    // flops-3 +4 insts/iter for -20% cycles. Instruction count does not predict
    // the sign, let alone the size.
    //
    // ⇒ The tier is a SHAPE LOTTERY at depth 1, not a cost/benefit the guard can
    // be tuned to capture. Corpus verdict over the 40 programs it changes:
    // geomean 1.0014 min / 1.0022 tmed against a null arm of 1.0002 / 1.0017 —
    // inside the instrument's own envelope, i.e. nothing. It is kept OPT-IN
    // (`TCG_LICM_DEPTH1_MULTI`) for that reason, NOT because the guard is safe.
    // The p4_matmul motivation below is real but was never worth the variance.
    //
    // A movz+movk... chain is a different trade: 2-4 instructions per iteration,
    // and on p4_matmul's initialization loop a 4-instruction 64-bit magic
    // constant is rebuilt every iteration inside a ~10-instruction body
    // (measured: 12 movz/movk in `main` against LLVM's 6, LLVM hoisting the same
    // constant). Real wins do exist in the set — almabench 0.9945/0.9964 in both
    // alignment regimes — but they are outnumbered by same-size losses.
    let depth1_multi = lp.depth == 1 && crate::env_lock::var_os("TCG_LICM_DEPTH1_MULTI").is_some();
    if const_chain_hoist_enabled() && (lp.depth >= 2 || depth1_multi) {
        for (carrier, chain) in find_hoistable_constant_chains(func, &lp.body, &def_counts) {
            // At depth 1 admit only multi-instruction chains (see above).
            if depth1_multi && chain.len() < 2 {
                continue;
            }
            invariant_vregs.insert(carrier);
            constant_chains.push((carrier, chain.iter().map(|(id, _)| *id).collect()));
            for site in chain {
                to_hoist.push(site);
            }
        }
    }

    // Iteratively find loop-invariant instructions.
    // Keep iterating until no new invariants are found (transitive closure).
    let mut found_new = true;
    while found_new {
        found_new = false;

        for &block_id in &func.block_order {
            if !lp.body.contains(&block_id) {
                continue;
            }

            let block = func.block(block_id);
            for &inst_id in &block.insts {
                // Skip instructions already marked for hoisting.
                if to_hoist.iter().any(|(id, _)| *id == inst_id) {
                    continue;
                }

                let inst = func.inst(inst_id);

                // Two admission classes:
                //  * `is_pure` instructions satisfy the stronger machine
                //    movement contract (rejects tied def-use MOVK/BFM, flag
                //    readers/writers, trapping div/sqrt, control-flow/trap
                //    pseudos) and hoist as before.
                //  * plain, analyzable loads (`is_plain_hoistable_load`) are
                //    admitted by the tiered load-motion rules in
                //    `load_is_admissible` below. `is_pure` rejects every load
                //    (loads are `MemoryEffect::Load`), so this is the only path
                //    that moves a load, and it is gated far more tightly.
                let is_hoistable_load = is_plain_hoistable_load(inst.opcode);
                if !inst.opcode.is_pure() && !is_hoistable_load {
                    continue;
                }
                let Some(def) = single_inst_def(inst) else {
                    continue;
                };

                // Relocation-bearing address materialization (Adrp / Adr /
                // AddPCRel) IS loop-invariant and safe to hoist. The prior
                // exclusion demanded "a proof that moving relocation pseudos
                // preserves encoding"; here it is:
                //
                //  * `Adrp` computes `page(sym)` PC-relatively, but the PAGE21
                //    relocation attached to the instruction is re-resolved by
                //    the linker for whatever PC the instruction finally lands
                //    at, so the RESULT (the symbol's page address) is
                //    INDEPENDENT of the instruction's own address. Moving the
                //    `Adrp` is therefore encoding-safe. `AddPCRel` adds the
                //    `:lo12:` PAGEOFF12 of the same symbol; likewise a link-time
                //    constant, independent of position.
                //  * `Adrp`/`AddPCRel` adjacency on Mach-O only enables the
                //    OPTIONAL ld64 linker relaxation (folding into a single
                //    `ADR` when in range); it is never required for
                //    correctness, so separating them across the preheader
                //    boundary changes nothing.
                //  * All three are pure and non-trapping, so speculating them
                //    into the preheader (which executes even when the loop body
                //    runs zero times) is safe.
                //
                // The surrounding guards still bound this: the single-def check
                // below is the multi-def protection, `inst_touches_fixed_register`
                // keeps fixed-register call-glue materialization in place, and
                // `is_operand_loop_invariant` keeps a jump-table `Adr` (whose
                // operand is a non-invariant `JumpTableIndex`) and any base
                // defined inside the loop from hoisting.

                // LICM only models virtual-register definitions. Fixed
                // physical registers are ABI/call-lowering state, not SSA
                // values: hoisting `x16 <- target` can separate it from a
                // later `blr x16`, and hoisting `dst <- x0` can read a stale
                // return value.
                if def_counts.get(&def).copied().unwrap_or(0) != 1 {
                    continue;
                }
                if inst_touches_fixed_register(inst) {
                    continue;
                }

                // Don't hoist branches, terminators, or phis.
                if inst.is_branch() || inst.is_terminator() || inst.opcode.is_phi() {
                    continue;
                }

                // Check if all source operands are loop-invariant.
                let mut all_invariant = true;
                aarch64_for_each_use_position(inst.opcode, inst.operands.len(), |pos| {
                    if !inst.operands.get(pos).is_some_and(|op| {
                        is_operand_loop_invariant(op, &loop_defs, &invariant_vregs, &def_counts)
                    }) {
                        all_invariant = false;
                    }
                });

                if !all_invariant {
                    continue;
                }

                // A load with an invariant address still faces the value-
                // stability (aliasing) and speculation (fault) gates before it
                // may leave the loop. Pure instructions skip this entirely.
                if is_hoistable_load
                    && !load_is_admissible(
                        func,
                        dom,
                        lp,
                        block_id,
                        inst,
                        preheader_enters_loop,
                        &mem_facts,
                        &def_map,
                        &def_counts,
                    )
                {
                    continue;
                }

                // Mark this instruction's def as invariant.
                invariant_vregs.insert(def);
                to_hoist.push((inst_id, block_id));
                found_new = true;
            }
        }
    }

    if to_hoist.is_empty() {
        return false;
    }

    // Hoist instructions to the preheader.
    // Insert before the preheader's ENTIRE branch tail — not merely before its
    // last instruction. A rotated loop's preheader is the guard block, whose
    // tail is `CmpRR; BCond(cc, header); B exit`: inserting at `len - 1` places
    // the hoisted instruction BETWEEN the BCond and the B, where it executes
    // only on the fall-through (loop-skipped) path — the loop body then reads
    // an undefined register, a MISCOMPILE (found by revmapfuzz: `x ^ x` in the
    // body rewritten to `MovI 0`, hoisted as invariant, sunk below the guard's
    // BCond). The correct position is before the FIRST branch/terminator:
    // every path out of the preheader (including into the loop) executes it,
    // and every vreg the hoisted instruction reads is still defined earlier
    // (preheader vreg defs precede the tail — branches and bare compares
    // define none; loop-external defs dominate the preheader; earlier-hoisted
    // invariants were inserted at this same position before it). Defensively
    // also step back over a preceding NON-value-producing flag-setter (the
    // `CmpRR/CmpRI` feeding the BCond) so hoisted code never sits between a
    // compare and its conditional branch — hoisted instructions are flag-free
    // today (`is_pure` rejects NZCV writers), but placement before the compare
    // keeps this correct even if that ever changed. Value-producing
    // flag-setters (`AddsRR`) are NOT stepped over: a hoisted instruction
    // could legitimately read their result.
    for (inst_id, source_block) in &to_hoist {
        // Remove from source block.
        let block = func.block_mut(*source_block);
        block.insts.retain(|id| id != inst_id);

        // Recompute per insertion (immutable borrows) so successive hoists
        // land in discovery order: each before the tail, after its deps.
        let ph_insts = &func.block(preheader).insts;
        let first_term = ph_insts
            .iter()
            .position(|&id| {
                let inst = func.inst(id);
                inst.is_branch() || inst.is_terminator()
            })
            .unwrap_or(ph_insts.len());
        let insert_pos = if first_term > 0 {
            let prev = func.inst(ph_insts[first_term - 1]);
            if prev.has_side_effects() && !produces_value(prev.opcode) {
                first_term - 1
            } else {
                first_term
            }
        } else {
            0
        };
        func.block_mut(preheader).insts.insert(insert_pos, *inst_id);
    }

    // X5 value-level nets: ordinary moved values use the single-def check;
    // MOVZ/MOVK materialization carriers are intentionally multi-def and use a
    // separate tied-chain order/consumer check.
    verify_preheader_defs_precede_uses(func, preheader, &def_counts);
    verify_preheader_constant_chains(func, preheader, &constant_chains);

    true
}

// ===========================================================================
// Pure-call cluster hoist tier (aarch64 port of x86
// `x86_licm.rs::hoist_pure_call_clusters` — the ackermann-class invariant-call
// lever). Hoists a loop-invariant call to a proven-pure callee (its
// `IS_CALL_ARG_SETUP` register moves + the `Bl` + the result copy) out of a
// loop into the preheader, but ONLY when the loop is proven to run at least
// once.
//
// A pure callee may still DIVERGE or trap, so executing it once in the preheader
// of a loop that would otherwise run zero times introduces non-termination /
// traps the source never had — the >=1-trip proof is a hard soundness
// precondition, not a heuristic. It reuses `region_loop_runs_at_least_once`, the
// aarch64 port of the x86 `loop_runs_at_least_once` the region tier already
// relies on (concrete guard interpretation; a false negative merely skips the
// hoist, a false positive would be a miscompile, so it fails safe).
//
// aarch64 vs x86 IR: x86 recognizes the cluster structurally against the
// `Call.call_arg_regs` field. aarch64 exposes a CLEANER signal on the
// `MachInst` itself — a direct `Bl` carries `proof == Some(ProofAnnotation::
// Pure)` (stamped in `isel.rs::select_call` from the SAME `pure_callees`
// module-purity fixpoint — `collect_pure_func_ids` /
// `compute_structural_pure_func_ids` — that feeds x86's `PURE_CALL_HOISTABLE`),
// and every ABI argument-setup move carries `InstFlags::IS_CALL_ARG_SETUP`
// (x86's ISel stream never sets that bit). The call's argument registers are its
// `implicit_uses`; its caller-saved clobbers are its `implicit_defs`, and both
// travel with the instruction when the cluster is moved.
//
// The tier fails safe: any deviation from the exact recognized shape declines.
// OPT-IN, DEFAULT-OFF behind `TCG_A64_PURE_CALL_HOIST`.
// ===========================================================================

/// Opt-in gate for the aarch64 pure-call cluster-hoist tier. DEFAULT-OFF: the
/// tier runs only when `TCG_A64_PURE_CALL_HOIST` is set, so the shipping aarch64
/// pipeline is byte-identical until a differential corpus certifies a default-ON
/// flip (mirroring the region-LICM rollout, which shipped behind
/// `TCG_A64_REGION_LICM` first). Unlike the x86 tier — which shipped default-ON
/// after a 354-program-pair differential campaign — the aarch64 port has no
/// per-pass translation-validation net yet, so it stays opt-in.
fn pure_call_hoist_enabled() -> bool {
    crate::env_lock::var_os("TCG_A64_PURE_CALL_HOIST").is_some()
}

/// Canonicalize a GPR `PReg` to its 64-bit form (`W0` -> `X0`); non-GPRs (FPRs,
/// `SP`) are returned unchanged. Lets the argument-register accounting compare
/// the W-form an arg-setup move may write (the 64<-32 `Uxtw`/W-alias path) with
/// the X-form the `Bl` records in `implicit_uses`.
fn canon_gpr(p: PReg) -> PReg {
    gpr32_to_gpr64(p).unwrap_or(p)
}

/// True iff `p` (canonicalized) is one of the AAPCS64 integer argument registers
/// `X0..=X7`. Rejects `X8` (the sret indirect-result register), `SP`/`LR`, and
/// every FPR — restricting the tier to simple integer-argument pure calls whose
/// entire ABI setup is register moves.
fn is_int_arg_reg(p: PReg) -> bool {
    let c = canon_gpr(p);
    preg_class(c) == RegClass::Gpr64 && c.encoding() <= 7
}

/// Recognize the pure-call cluster whose `Bl` sits at `block.insts[call_idx]`.
/// Returns the ordered `InstId`s `[arg-setup moves.., Bl, result copy]` when the
/// call is a hoistable loop-invariant pure-call cluster, else `None` (fail-safe
/// decline). Direct port of x86 `recognize_pure_call_cluster` onto the arena IR.
fn recognize_pure_call_cluster(
    func: &MachFunction,
    block_id: BlockId,
    call_idx: usize,
    loop_defs: &HashMap<VReg, (InstId, BlockId)>,
    invariant_vregs: &HashSet<VReg>,
    def_counts: &HashMap<VReg, usize>,
) -> Option<Vec<InstId>> {
    let insts = &func.block(block_id).insts;
    let call_id = insts[call_idx];
    let call = func.inst(call_id);

    // (1) Direct pure call only: a `Bl` carrying `ProofAnnotation::Pure`. `Blr`
    //     (indirect) is never stamped pure, so it can never reach here; the
    //     explicit opcode gate keeps that guarantee local and future-proof.
    if call.opcode != AArch64Opcode::Bl || call.proof != Some(ProofAnnotation::Pure) {
        return None;
    }

    // (2) Argument registers = the call's implicit uses. Require every one to be
    //     a simple integer argument register `X0..=X7` (rejects sret `X8`, FP
    //     args, indirect-aggregate register pairs, and variadic setups).
    let arg_regs: Vec<PReg> = call.implicit_uses.to_vec();
    if arg_regs.iter().any(|p| !is_int_arg_reg(*p)) {
        return None;
    }
    let n = arg_regs.len();
    let mut needed: HashSet<PReg> = arg_regs.iter().map(|p| canon_gpr(*p)).collect();
    if needed.len() != n {
        return None; // duplicate argument registers desync the accounting
    }

    // (3) Result copy: the instruction immediately after the `Bl` must be a plain
    //     register copy `Copy/MovR [VReg(dst), PReg(X0)]` capturing the single
    //     scalar-GPR return into a genuine single-def SSA value (its in-loop uses
    //     are what the hoisted value feeds). Void / multi-result / FP (`V0`) /
    //     i128 `GprPair` returns are all declined.
    let result_idx = call_idx.checked_add(1)?;
    let result_id = *insts.get(result_idx)?;
    let res = func.inst(result_id);
    if !matches!(res.opcode, AArch64Opcode::Copy | AArch64Opcode::MovR) {
        return None;
    }
    let [MachOperand::VReg(dst), MachOperand::PReg(src)] = res.operands.as_slice() else {
        return None;
    };
    if canon_gpr(*src) != X0 || def_counts.get(dst).copied().unwrap_or(0) != 1 {
        return None;
    }
    if !res.implicit_defs.is_empty() || !res.implicit_uses.is_empty() {
        return None; // no secondary fixed-register coupling on the result copy
    }

    // (4) Arg-setup moves: the `n` instructions immediately before the `Bl` must
    //     each be an `IS_CALL_ARG_SETUP` register move into exactly one of the
    //     call's argument registers, from a loop-invariant source. This window
    //     check ALSO rejects stack arguments: stack-argument stores are emitted
    //     AFTER the register moves (later positional args), so they land inside
    //     this window and are not `IS_CALL_ARG_SETUP` register moves -> decline.
    let start = call_idx.checked_sub(n)?;
    let mut cluster: Vec<InstId> = Vec::with_capacity(n + 2);
    for &mid in &insts[start..call_idx] {
        let m = func.inst(mid);
        if !m.flags.is_call_arg_setup() {
            return None;
        }
        // Pure register mover only (`Copy` pseudo, `MovR`, or the zero-extending
        // `Uxtw` the 64<-32 argument path emits); no memory / flags / control
        // flow. Every one of these is memory-`Pure` and non-trapping.
        if !matches!(
            m.opcode,
            AArch64Opcode::Copy | AArch64Opcode::MovR | AArch64Opcode::Uxtw
        ) {
            return None;
        }
        let [MachOperand::PReg(dest), source] = m.operands.as_slice() else {
            return None;
        };
        if !needed.remove(&canon_gpr(*dest)) {
            return None; // dest is not one of this call's arg regs (or a dup)
        }
        if !is_operand_loop_invariant(source, loop_defs, invariant_vregs, def_counts) {
            return None;
        }
        if !m.implicit_defs.is_empty() || !m.implicit_uses.is_empty() {
            return None; // no secondary fixed-register coupling on an arg move
        }
        cluster.push(mid);
    }
    if !needed.is_empty() {
        return None; // some argument register was not populated by these moves
    }

    // (5) Zero-register-argument corner: a pure call with NO register args. Guard
    //     against a stack-only-argument call (whose stores are not
    //     `IS_CALL_ARG_SETUP` and would be left behind in the loop) by requiring
    //     the instruction immediately before the `Bl` not to write memory.
    if n == 0 && start > 0 {
        let prev = func.inst(insts[start - 1]);
        if opcode_effect(prev.opcode).writes_memory() {
            return None;
        }
    }

    cluster.push(call_id);
    cluster.push(result_id);
    Some(cluster)
}

/// Hoist every loop-invariant pure-call cluster out of `lp` into its preheader,
/// when the loop is proven to run at least once. Returns whether anything moved.
/// Direct port of x86 `hoist_pure_call_clusters`.
fn hoist_pure_call_clusters(
    func: &mut MachFunction,
    lp: &NaturalLoop,
    def_counts: &HashMap<VReg, usize>,
    dom: &DomTree,
) -> bool {
    // Only hoist when a natural preheader exists (we never synthesize one — the
    // same conservatism as the value-producer and load tiers above).
    let Some(preheader) = lp.preheader else {
        return false;
    };
    // Soundness precondition: a pure call may diverge/trap, so it may only be
    // relocated ahead of a loop guaranteed to have executed it at least once.
    if !region_loop_runs_at_least_once(func, lp, preheader, dom) {
        return false;
    }

    // Fail-closed: the preheader must UNCONDITIONALLY enter the header. Unlike the
    // value-producer / load tiers (which move non-flag-clobbering, non-trapping
    // instructions), the cluster contains a `Bl` that clobbers NZCV + all
    // caller-saved registers, so a conditionally-branching preheader is doubly
    // unsound here. `find_preheader` returns the header's unique NON-LOOP
    // predecessor but does NOT require the header to be that block's only
    // successor — it may legally end in `CmpRI ..; BCond header; B other`. Two
    // ways that breaks a cluster hoist the existing tiers never expose:
    //   (a) FLAG CLOBBER: `has_side_effects()` is an unset stamp on a compare, so
    //       the `insert_pos` guard would place the `Bl` BETWEEN that compare and
    //       its `BCond`, corrupting the branch condition.
    //   (b) TRAP/DIVERGENCE: on the `B other` edge the loop runs zero times, yet
    //       the hoisted pure call would still execute — a trap/non-termination the
    //       source never had. `region_loop_runs_at_least_once` interprets only the
    //       HEADER guard, so it cannot see a preheader that conditionally skips.
    // Requiring a single-successor preheader that ends in an unconditional branch
    // to the header eliminates both: no compare/branch pair to split, and the
    // preheader provably falls straight into the >=1-trip loop.
    {
        let ph = func.block(preheader);
        if ph.succs.len() != 1 || ph.succs[0] != lp.header {
            return false;
        }
        let ends_unconditional = ph
            .insts
            .last()
            .map(|&id| func.inst(id).is_unconditional_branch())
            .unwrap_or(false);
        if !ends_unconditional {
            return false;
        }
    }

    let loop_defs = build_loop_defs(func, &lp.body);
    // v1 does not chain a hoisted cluster's result into a later cluster's
    // invariance, so the invariant seed stays empty: argument sources must be
    // defined OUTSIDE the loop.
    let invariant_vregs: HashSet<VReg> = HashSet::new();

    // Discover clusters in deterministic order (block_order, then ascending
    // in-block index). `claimed` guards against overlapping `InstId` ranges.
    let mut clusters: Vec<Vec<InstId>> = Vec::new();
    let mut claimed: HashSet<InstId> = HashSet::new();
    for &block_id in &func.block_order {
        if !lp.body.contains(&block_id) {
            continue;
        }
        let mut idx = 0;
        while idx < func.block(block_id).insts.len() {
            let iid = func.block(block_id).insts[idx];
            let is_pure_call = {
                let inst = func.inst(iid);
                inst.opcode == AArch64Opcode::Bl && inst.proof == Some(ProofAnnotation::Pure)
            };
            if is_pure_call
                && let Some(cluster) = recognize_pure_call_cluster(
                    func,
                    block_id,
                    idx,
                    &loop_defs,
                    &invariant_vregs,
                    def_counts,
                )
                && !cluster.iter().any(|id| claimed.contains(id))
            {
                for id in &cluster {
                    claimed.insert(*id);
                }
                clusters.push(cluster);
            }
            idx += 1;
        }
    }

    if clusters.is_empty() {
        return false;
    }

    // Materialize: remove every cluster `InstId` from its (body) source block,
    // then splice the clusters — each in captured order (arg moves.., `Bl`,
    // result copy) — into the preheader before its branch tail. Mirrors the
    // value-producer splice in `hoist_loop_invariants`, kept separate to move
    // contiguous multi-instruction clusters as units.
    let mut ordered: Vec<InstId> = Vec::new();
    for cluster in &clusters {
        ordered.extend_from_slice(cluster);
    }
    let to_remove: HashSet<InstId> = ordered.iter().copied().collect();
    let body_blocks: Vec<BlockId> = func
        .block_order
        .iter()
        .copied()
        .filter(|b| lp.body.contains(b))
        .collect();
    for block_id in body_blocks {
        func.block_mut(block_id)
            .insts
            .retain(|id| !to_remove.contains(id));
    }

    // Insert before the preheader's ENTIRE branch tail (same placement rule as
    // the value-producer splice at the top of this file): every path out of the
    // preheader — including into the loop — executes the cluster, and a flag-free
    // cluster never lands between a compare and its conditional branch. The
    // hoisted cluster's argument sources are loop-invariant (defined outside the
    // loop), so they dominate the preheader and are defined before this point.
    let ph_insts = &func.block(preheader).insts;
    let first_term = ph_insts
        .iter()
        .position(|&id| {
            let inst = func.inst(id);
            inst.is_branch() || inst.is_terminator()
        })
        .unwrap_or(ph_insts.len());
    let insert_pos = if first_term > 0 {
        let prev = func.inst(ph_insts[first_term - 1]);
        if prev.has_side_effects() && !produces_value(prev.opcode) {
            first_term - 1
        } else {
            first_term
        }
    } else {
        0
    };
    for (offset, iid) in ordered.into_iter().enumerate() {
        func.block_mut(preheader)
            .insts
            .insert(insert_pos + offset, iid);
    }

    // X5 value-level net: the cluster's argument sources are loop-invariant
    // (defined in dominating blocks) and the arg-move/Bl/result order is
    // preserved, so no use-before-def should exist — verify it fail-closed.
    verify_preheader_defs_precede_uses(func, preheader, def_counts);

    true
}

fn operand_touches_fixed_register(operand: &MachOperand) -> bool {
    matches!(
        operand,
        MachOperand::PReg(_) | MachOperand::MemOp { .. } | MachOperand::Special(_)
    )
}

fn inst_touches_fixed_register(inst: &MachInst) -> bool {
    !inst.implicit_defs.is_empty()
        || !inst.implicit_uses.is_empty()
        || inst.operands.iter().any(operand_touches_fixed_register)
}

fn build_def_counts(func: &MachFunction) -> HashMap<VReg, usize> {
    let mut counts: HashMap<VReg, usize> = HashMap::new();

    for &block_id in &func.block_order {
        let block = func.block(block_id);
        for &inst_id in &block.insts {
            let inst = func.inst(inst_id);
            for_each_inst_def(inst, |def| {
                *counts.entry(def).or_insert(0) += 1;
            });
        }
    }

    counts
}

/// Build a map from VReg to (InstId, BlockId) for all definitions
/// inside the loop body.
fn build_loop_defs(
    func: &MachFunction,
    body: &HashSet<BlockId>,
) -> HashMap<VReg, (InstId, BlockId)> {
    let mut defs: HashMap<VReg, (InstId, BlockId)> = HashMap::new();

    for &block_id in &func.block_order {
        if !body.contains(&block_id) {
            continue;
        }
        let block = func.block(block_id);
        for &inst_id in &block.insts {
            let inst = func.inst(inst_id);
            for_each_inst_def(inst, |def| {
                defs.insert(def, (inst_id, block_id));
            });
        }
    }

    defs
}

/// Check if an operand is loop-invariant.
///
/// An operand is loop-invariant if:
/// - It is an immediate or other non-vreg operand.
/// - It is a vreg defined outside the loop.
/// - It is a vreg defined inside the loop but already marked invariant.
fn is_operand_loop_invariant(
    operand: &MachOperand,
    loop_defs: &HashMap<VReg, (InstId, BlockId)>,
    invariant_vregs: &HashSet<VReg>,
    def_counts: &HashMap<VReg, usize>,
) -> bool {
    match operand {
        MachOperand::VReg(vreg) => {
            // A vreg LICM has already PROVEN invariant is invariant, full stop —
            // even if it is multiply-defined. The single-def gate below is a
            // conservative proxy for "provably one value"; it must not override
            // a positive proof already recorded in `invariant_vregs`. The
            // constant-chain tier (`find_hoistable_constant_chains`) seeds this
            // set with GPR carriers of `MOVZ/MOVK` immediate chains, which are
            // multiply-defined yet hold a single compile-time constant. Existing
            // single-def entries reach the same verdict either way, so this only
            // widens acceptance to the proven multi-def constant chains.
            if invariant_vregs.contains(vreg) {
                return true;
            }
            if def_counts.get(vreg).copied().unwrap_or(0) != 1 {
                return false;
            }
            // If this vreg is defined inside the loop...
            if loop_defs.contains_key(vreg) {
                // ...it's only invariant if we've already marked it so.
                invariant_vregs.contains(vreg)
            } else {
                // Defined outside the loop — invariant by definition.
                true
            }
        }
        // A relocation `Symbol` is a link-time constant: its resolved page
        // (Adrp) or page-offset (AddPCRel) does not vary across loop
        // iterations. Classifying it invariant is what lets an `Adrp @g` (whose
        // only source operand is the symbol) and an `AddPCRel base, @g` (symbol
        // plus an already-invariant base) hoist out of the loop. A jump-table
        // `Adr` carries a `JumpTableIndex`, not a `Symbol`, so it stays in the
        // `_ => false` arm and is never hoisted.
        MachOperand::Imm(_) | MachOperand::FImm(_) | MachOperand::Symbol(_) => true,
        _ => false,
    }
}

// ===========================================================================
// Constant-chain hoisting: lift `MOVZ/MOVK` immediate materialization chains
// ===========================================================================

/// Bisect kill switch for the constant-chain hoist tier. Set
/// `TCG_NO_LICM_CONST_CHAIN` to fall back to the single-instruction-only LICM
/// behaviour (encodable `FmovImm`/`Movz` constants still lift; multi-`MOVK`
/// chains and their consuming `FMOV Dn, Xv` stay in the loop).
fn const_chain_hoist_enabled() -> bool {
    std::env::var_os("TCG_NO_LICM_CONST_CHAIN").is_none()
}

/// Bisect kill switch for the INTEGER widening of the constant-chain tier.
/// Set `TCG_NO_LICM_INT_CONST_CHAIN` to restrict the tier to its original
/// FP-literal scope (chains consumed by an `FMOV Dn, Xv` only); multi-`MOVK`
/// integer constants — srem/sdiv magic reciprocals — then stay in the loop.
fn int_const_chain_hoist_enabled() -> bool {
    std::env::var_os("TCG_NO_LICM_INT_CONST_CHAIN").is_none()
}

/// Whether `opcode` heads an integer-constant materialization chain: a
/// stand-alone immediate move whose result is the constant so far.
fn is_const_chain_head(opcode: AArch64Opcode) -> bool {
    matches!(
        opcode,
        AArch64Opcode::Movz | AArch64Opcode::Movn | AArch64Opcode::MovI
    )
}

/// Whether every non-destination operand of `inst` is an integer immediate and
/// the instruction carries no fixed-register (implicit def/use, `PReg`,
/// `Special`, `MemOp`) state. Operand 0 is the tied destination register.
fn const_chain_operands_are_immediate(inst: &MachInst) -> bool {
    if !inst.implicit_defs.is_empty() || !inst.implicit_uses.is_empty() {
        return false;
    }
    !inst.operands.is_empty()
        && inst.operands[1..]
            .iter()
            .all(|op| matches!(op, MachOperand::Imm(_)))
}

/// Identify loop-invariant constant materialization chains and return,
/// for each, the GPR carrier it defines together with the ordered
/// `(InstId, BlockId)` of its defining instructions (all inside `body`).
///
/// A *constant chain* is a vreg `V` whose ENTIRE set of definitions is a
/// contiguous run in ONE block — a single `MOVZ`/`MOVN`/`MOVI` head followed by
/// zero or more `MOVK` patches — with immediate-only operands and no
/// fixed-register state. Such a `V` holds one compile-time constant and is
/// therefore loop-invariant, but the per-instruction LICM screen cannot admit
/// it: `MOVK` is a tied def-use (not `is_pure`, #366/#382/#408) and `V` is
/// multiply-defined (`def_counts != 1`). The downstream `FMOV Dn, Xv` that
/// turns the constant into an FP register (the lowering of a non-encodable f64
/// literal) is then pinned in the loop because its source "is not invariant".
///
/// SCOPE — two carrier classes are admitted:
///
/// * **FP-literal chains**: the carrier feeds an `FMOV Dn, Xv` (`FmovGprFpr`)
///   — the non-encodable f64-literal lowering (perlin fade/lerp coefficients)
///   the tier originally existed for. Admitted at any chain length.
/// * **Integer multi-`MOVK` chains** (>= 2 instructions, i.e. a head plus at
///   least one patch): wide integer constants such as the srem/sdiv magic
///   reciprocal `0x…80808081` that the `% 255` expansion re-materializes
///   every iteration in ReedSolomon's hot loops. Only the MULTI-def shape is
///   admitted here because it is the one the per-instruction screen can never
///   hoist (`MOVK` is tied def-use, the carrier is multiply-defined); a
///   single-def `MOVZ`/`MOVN` head with no patches already lifts on the
///   ordinary single-def path, so admitting it here would only reorder
///   existing hoists. Behind its own kill switch
///   (`TCG_NO_LICM_INT_CONST_CHAIN`) and the tier-wide `lp.depth >= 2` gate
///   at the call site, which keeps the documented "never pull out of the
///   OUTERMOST loop" fetch-alignment concern (flops-1/2/7) intact for
///   integer chains too.
///
/// # Soundness
/// * **`V` holds a single value.** Requiring the whole def set to be one head
///   plus `MOVK` patches, contiguous and in one block, means `V`'s bits are a
///   fixed function of immediates only — identical on every iteration and every
///   path. Two heads, a non-move def, an interleaved reader of the partial
///   value, or a def in another block all disqualify it (returned chain empty).
/// * **The preheader dominates every use of `V`.** `V` is defined ONLY by this
///   in-loop chain (no out-of-loop or out-of-block def survives the checks), so
///   every use of `V` is inside code the loop header dominates, which the
///   preheader dominates in turn. Moving the whole chain up keeps every use
///   dominated by its definition.
/// * **No partial-value hazard.** Contiguity guarantees no non-chain
///   instruction observes `V` between the head and the final `MOVK`, so lifting
///   the run cannot change any value an intermediate reader would have seen.
fn find_hoistable_constant_chains(
    func: &MachFunction,
    body: &HashSet<BlockId>,
    def_counts: &HashMap<VReg, usize>,
) -> Vec<(VReg, Vec<(InstId, BlockId)>)> {
    // Whole-function def sites of each vreg: (block, index-in-block, inst).
    // Function-wide (not body-restricted) so a def OUTSIDE the loop
    // disqualifies the carrier — we must account for every definition.
    // Simultaneously collect the set of GPRs consumed by an `FMOV Dn, Xv`;
    // such carriers are FP-literal chains, admitted at any length (the
    // integer class needs >= 2 defs — see the scope note above).
    let mut defs: HashMap<VReg, Vec<(BlockId, usize, InstId)>> = HashMap::new();
    let mut fmov_gpr_sources: HashSet<VReg> = HashSet::new();
    // Position of each block in the (deterministic) `block_order`, so the
    // returned chains can be sorted into a stable program order below — the
    // `defs` HashMap iteration order is nondeterministic and would otherwise
    // leak into which chain lands first in the preheader (a reproducibility
    // break for a verified compiler; cf. LoopAnalysis's BTreeMap rationale).
    let mut block_pos: HashMap<BlockId, usize> = HashMap::new();
    for (pos, &block_id) in func.block_order.iter().enumerate() {
        block_pos.insert(block_id, pos);
    }
    for &block_id in &func.block_order {
        let block = func.block(block_id);
        for (idx, &inst_id) in block.insts.iter().enumerate() {
            let inst = func.inst(inst_id);
            if inst.opcode == AArch64Opcode::FmovGprFpr {
                // Operand 0 is the FPR destination; the GPR source(s) follow.
                for op in inst.operands.iter().skip(1) {
                    if let MachOperand::VReg(src) = op {
                        fmov_gpr_sources.insert(*src);
                    }
                }
            }
            for_each_inst_def(inst, |def| {
                defs.entry(def).or_default().push((block_id, idx, inst_id));
            });
        }
    }

    type ConstantChain = ((usize, usize), VReg, Vec<(InstId, BlockId)>);

    let int_chains = int_const_chain_hoist_enabled();
    // DIAGNOSTIC (default off, TCG_DUMP_CHAINS=1): why each multi-def carrier
    // was declined. Only multi-def carriers are reported — single-def vregs are
    // the overwhelming majority and are not chain candidates.
    let dump = std::env::var_os("TCG_DUMP_CHAINS").is_some();
    let mut chains: Vec<ConstantChain> = Vec::new();
    for (&carrier, sites) in &defs {
        macro_rules! decline {
            ($why:expr) => {{
                if dump && sites.len() >= 2 {
                    eprintln!(
                        "TCG_CHAIN decline carrier=v{} sites={} why={}",
                        carrier.id,
                        sites.len(),
                        $why
                    );
                }
                continue;
            }};
        }
        // Carrier scope (see the SCOPE note above): FP-literal carriers (fed
        // to an `FMOV Dn, Xv`) at any length, integer carriers only as
        // multi-def chains (head + >=1 `MOVK`) — the shape the ordinary
        // single-def path can never hoist.
        if !(fmov_gpr_sources.contains(&carrier) || int_chains && sites.len() >= 2) {
            decline!("scope: not FP-literal and (int chains disabled or < 2 defs)");
        }
        // Sanity: our def collection must agree with the pass-wide count.
        if def_counts.get(&carrier).copied().unwrap_or(0) != sites.len() {
            decline!("def-count cross-check mismatch");
        }
        // All defs in one block, and that block is in the loop body.
        let block_id = sites[0].0;
        if sites.iter().any(|&(b, _, _)| b != block_id) {
            decline!("defs span multiple blocks");
        }
        if !body.contains(&block_id) {
            if std::env::var_os("TCG_DUMP_CHAINS").is_some() && sites.len() >= 2 {
                let mut body_sorted: Vec<u32> = body.iter().map(|b| b.0).collect();
                body_sorted.sort_unstable();
                let blk = func.block(block_id);
                eprintln!(
                    "TCG_CHAIN decline carrier=v{} sites={} why=block-membership chain_block={} preds={:?} succs={:?} loop_body={:?}",
                    carrier.id,
                    sites.len(),
                    block_id.0,
                    blk.preds.iter().map(|b| b.0).collect::<Vec<_>>(),
                    blk.succs.iter().map(|b| b.0).collect::<Vec<_>>(),
                    body_sorted
                );
            }
            continue;
        }
        // Order defs by their position in the block and require a contiguous run
        // (no non-chain instruction — hence no reader of a partial value — is
        // interleaved between the head and the last patch).
        let mut ordered = sites.clone();
        ordered.sort_by_key(|&(_, idx, _)| idx);
        let contiguous = ordered.windows(2).all(|w| w[1].1 == w[0].1 + 1);
        if !contiguous {
            decline!("defs not contiguous in block");
        }
        // Exactly one head (MOVZ/MOVN/MOVI) at the front; the rest are MOVK; all
        // operands immediates; operand 0 is the carrier; no fixed-register state.
        let mut ok = true;
        for (pos, &(_, _, inst_id)) in ordered.iter().enumerate() {
            let inst = func.inst(inst_id);
            let head = pos == 0;
            let opcode_ok = if head {
                is_const_chain_head(inst.opcode)
            } else {
                inst.opcode == AArch64Opcode::Movk
            };
            if !opcode_ok
                || inst.operands.first() != Some(&MachOperand::VReg(carrier))
                || !const_chain_operands_are_immediate(inst)
            {
                ok = false;
                break;
            }
        }
        if !ok {
            decline!("opcode/operand shape (head/MOVK/immediates)");
        }
        // Sort key = program position of the chain head (block order, then
        // in-block index) for deterministic preheader placement across runs.
        let head_key = (
            block_pos.get(&block_id).copied().unwrap_or(usize::MAX),
            ordered[0].1,
        );
        chains.push((
            head_key,
            carrier,
            ordered.into_iter().map(|(b, _, id)| (id, b)).collect(),
        ));
    }
    chains.sort_by_key(|(key, _, _)| *key);
    chains
        .into_iter()
        .map(|(_, carrier, sites)| (carrier, sites))
        .collect()
}

// ===========================================================================
// Load hoisting: opcode class, address classification, and admission gates
// ===========================================================================

/// Plain, analyzable loads eligible for the tiered load-motion rules.
///
/// These are the base+immediate scalar loads: a single value-producing def,
/// an ordinary base register operand at position 1, and a constant immediate
/// offset at position 2 — exactly the pre-regalloc `LdrRI dst, base, #off`
/// shape whose address the invariance engine already reasons about.
///
/// DELIBERATELY EXCLUDED (each unsound or unanalyzable to hoist here):
/// - `LdrPreIndex` / `LdrPostIndex`: writeback forms that also *define* the
///   base register (a second def LICM does not model).
/// - `LdpRI` / `LdpPostIndex` / NEON pair loads: define two registers.
/// - `LdrRO` / `LdrbRO` / …: register-offset addressing (a second, possibly
///   variant, index operand — not modeled here yet).
/// - `LdrLiteral`: PC-relative literal-pool load, no base register.
/// - `LdrGot` / `LdrTlvp` / `LdrGottprel`: GOT/TLS indirection.
/// - `Ldar*` / `Ldaxr`: acquire/atomic loads whose ordering must not move.
fn is_plain_hoistable_load(opcode: AArch64Opcode) -> bool {
    matches!(
        opcode,
        AArch64Opcode::LdrRI
            | AArch64Opcode::LdrbRI
            | AArch64Opcode::LdrhRI
            | AArch64Opcode::LdrsbRI
            | AArch64Opcode::LdrshRI
    )
}

/// The base-register operand of a *simple* base+immediate store, if this
/// instruction is one. Returns `None` for any other memory writer (store-pair,
/// writeback stores, atomics, `StackAlloc`, refcounting, calls, barriers),
/// which the caller treats as an opaque writer that fails tier (b) closed.
fn simple_store_base(inst: &MachInst) -> Option<&MachOperand> {
    match inst.opcode {
        // `StrRI value, base, #off` / `StrbRI` / `StrhRI`: operand 1 is the base.
        AArch64Opcode::StrRI | AArch64Opcode::StrbRI | AArch64Opcode::StrhRI => {
            inst.operands.get(1)
        }
        _ => None,
    }
}

/// Static classification of a memory address's provenance, used to prove two
/// accesses cannot alias.
#[derive(Debug, Clone, PartialEq, Eq)]
enum AddrBase {
    /// Derives directly from a named global symbol via `Adrp`/`AddPCRel`.
    /// Distinct symbols name distinct, non-overlapping link-time objects.
    Global(String),
    /// Derives directly from a specific stack slot via `AddPCRel base, ss#`.
    /// Distinct slots are distinct frame allocations that never overlap.
    Stack(StackSlotId),
    /// Anything we cannot prove — an arbitrary pointer. Fails disjointness.
    Unknown,
}

/// Classify the provenance of an address held in `base_op`.
///
/// Only a single-def base register whose defining instruction is *directly* an
/// `Adrp`/`AddPCRel` of a symbol, or an `AddPCRel` of a stack slot, is trusted.
/// Any runtime arithmetic on the address (an intervening `AddRR`/`AddRI`, a
/// value loaded from memory, a call result, …) yields `Unknown` — this is the
/// "direct symbol/slot + immediate form only" conservatism that keeps the
/// disjointness facts rock-solid.
fn classify_addr_base(
    func: &MachFunction,
    base_op: &MachOperand,
    def_map: &HashMap<VReg, InstId>,
    def_counts: &HashMap<VReg, usize>,
) -> AddrBase {
    let MachOperand::VReg(base) = base_op else {
        return AddrBase::Unknown;
    };
    if def_counts.get(base).copied().unwrap_or(0) != 1 {
        return AddrBase::Unknown;
    }
    let Some(&def_inst) = def_map.get(base) else {
        return AddrBase::Unknown;
    };
    let inst = func.inst(def_inst);
    match inst.opcode {
        // `AddPCRel dst, page, :lo12:sym`  -> global symbol address
        // `AddPCRel dst, SP,  ss#`         -> stack-slot address
        AArch64Opcode::AddPCRel => match inst.operands.get(2) {
            Some(MachOperand::Symbol(s)) => AddrBase::Global(s.clone()),
            Some(MachOperand::StackSlot(id)) => AddrBase::Stack(*id),
            _ => AddrBase::Unknown,
        },
        // `Adrp dst, sym` -> page address of a global symbol.
        AArch64Opcode::Adrp => match inst.operands.get(1) {
            Some(MachOperand::Symbol(s)) => AddrBase::Global(s.clone()),
            _ => AddrBase::Unknown,
        },
        _ => AddrBase::Unknown,
    }
}

/// Returns true when a load from `load` provably cannot alias a store to
/// `store`. Only rock-solid facts admit; anything `Unknown` refuses.
fn addr_bases_disjoint(load: &AddrBase, store: &AddrBase) -> bool {
    match (load, store) {
        (AddrBase::Unknown, _) | (_, AddrBase::Unknown) => false,
        // Distinct stack slots are distinct frame allocations.
        (AddrBase::Stack(a), AddrBase::Stack(b)) => a != b,
        // Distinct global symbols are distinct link-time objects.
        (AddrBase::Global(a), AddrBase::Global(b)) => a != b,
        // The stack and the data segment are disjoint address ranges.
        (AddrBase::Stack(_), AddrBase::Global(_)) | (AddrBase::Global(_), AddrBase::Stack(_)) => {
            true
        }
    }
}

/// Per-loop memory-write summary consumed by [`load_is_admissible`].
struct LoopMemFacts {
    /// Any body instruction writes memory / calls / is a barrier.
    writes_memory: bool,
    /// Some memory writer is not a simple, classifiable base+immediate store
    /// (a call, barrier, atomic, store-pair, writeback store, …). When set,
    /// tier (b) admits nothing: we cannot bound what the loop clobbers.
    opaque_writer: bool,
    /// Classified base of every simple in-loop store (only meaningful when
    /// `opaque_writer` is false).
    store_bases: Vec<AddrBase>,
}

/// Summarize the memory writes of a loop body in one pass.
fn compute_loop_memory_facts(
    func: &MachFunction,
    lp: &NaturalLoop,
    def_map: &HashMap<VReg, InstId>,
    def_counts: &HashMap<VReg, usize>,
) -> LoopMemFacts {
    let mut writes_memory = false;
    let mut opaque_writer = false;
    let mut store_bases: Vec<AddrBase> = Vec::new();

    for &block_id in &func.block_order {
        if !lp.body.contains(&block_id) {
            continue;
        }
        for &inst_id in &func.block(block_id).insts {
            let inst = func.inst(inst_id);
            let eff = opcode_effect(inst.opcode);
            // `writes_memory()` already covers stores, calls and barriers
            // (all `MemoryEffect::Call`); `is_barrier()` is included for
            // explicitness.
            if eff.writes_memory() || eff.is_barrier() {
                writes_memory = true;
                match simple_store_base(inst) {
                    Some(base) => {
                        store_bases.push(classify_addr_base(func, base, def_map, def_counts));
                    }
                    None => opaque_writer = true,
                }
            }
        }
    }

    LoopMemFacts {
        writes_memory,
        opaque_writer,
        store_bases,
    }
}

/// The classic LICM "guaranteed to execute" (a.k.a. must-execute) test for the
/// block containing a candidate load: the load runs on every path that enters
/// the loop, so hoisting it to the preheader introduces no fault that the
/// original program did not already have.
///
/// Two conditions:
/// - **Dominates EVERY latch** — i.e. every back-edge source, not merely the
///   one `lp.latch` happens to cache. The load then runs on every complete
///   iteration (which is also what rules out a load buried in a conditional
///   inside an infinite loop with no exiting block, where the exit test below
///   is vacuous).
/// - **Dominates every loop-exiting block** — the load runs before control can
///   leave the loop, so it is not skipped on an early-exit path.
///
/// The caller separately requires the preheader to unconditionally enter the
/// loop, which together with this test guarantees the load ran at least once in
/// the original whenever the preheader executes.
fn load_guaranteed_to_execute(
    func: &MachFunction,
    dom: &DomTree,
    lp: &NaturalLoop,
    load_block: BlockId,
) -> bool {
    // Defense in depth: the cached representative latch must be dominated even
    // if `lp.body` were somehow stale and missed it in the sweep below.
    if !dom.dominates(load_block, lp.latch) {
        return false;
    }
    for &b in &lp.body {
        let succs = &func.block(b).succs;
        // A back-edge source (ANY latch of this loop), or a block from which
        // control can leave the loop.
        let is_latch = succs.contains(&lp.header);
        let exits_loop = succs.iter().any(|s| !lp.body.contains(s));
        if (is_latch || exits_loop) && !dom.dominates(load_block, b) {
            return false;
        }
    }
    true
}

/// Decide whether a loop-invariant plain load may be hoisted out of `lp`.
///
/// The address is already known invariant by the caller. This adds the two
/// remaining LICM safety obligations for loads:
///   1. Speculation/fault safety (the load must be guaranteed to execute).
///   2. Value stability / aliasing (tier a: no writers; tier b: proven
///      disjoint from every writer).
#[allow(clippy::too_many_arguments)]
fn load_is_admissible(
    func: &MachFunction,
    dom: &DomTree,
    lp: &NaturalLoop,
    load_block: BlockId,
    inst: &MachInst,
    preheader_enters_loop: bool,
    mem_facts: &LoopMemFacts,
    def_map: &HashMap<VReg, InstId>,
    def_counts: &HashMap<VReg, usize>,
) -> bool {
    // (1) Speculation guard — do not introduce a fault on a zero-trip or
    // early-exit path.
    if !preheader_enters_loop {
        return false;
    }
    if !load_guaranteed_to_execute(func, dom, lp, load_block) {
        return false;
    }

    // (2a) Tier (a): a loop that never writes memory (no stores, no calls, no
    // barriers) cannot clobber the invariant address, so the load is stable.
    if !mem_facts.writes_memory {
        return true;
    }

    // (2b) Tier (b): the loop writes memory. Admit only if every writer is a
    // simple store we could classify AND each is provably disjoint from the
    // load's own (classifiable) address.
    if mem_facts.opaque_writer {
        return false;
    }
    let Some(base) = inst.operands.get(1) else {
        return false;
    };
    let load_base = classify_addr_base(func, base, def_map, def_counts);
    if matches!(load_base, AddrBase::Unknown) {
        return false;
    }
    mem_facts
        .store_bases
        .iter()
        .all(|store_base| addr_bases_disjoint(&load_base, store_base))
}

/// Build a whole-function map from each value-producing VReg to its defining
/// [`InstId`]. Only meaningful for single-def VRegs (the caller pairs this with
/// `def_counts` to reject multi-def carriers).
fn build_def_map(func: &MachFunction) -> HashMap<VReg, InstId> {
    crate::effects::build_reaching_def_map_by_vreg(func)
}

// ===========================================================================
// Region-LICM: hoist an outer-invariant inner LOOP out of its enclosing loop
// (aarch64 port of the x86 S4 region-LICM v2, `x86_licm.rs::region_licm_hoist`;
// design docs/region-licm-design-2026-07-16.md §8 v2)
// ===========================================================================

/// Opt-in gate for the aarch64 region-LICM stage. DEFAULT-OFF: the stage runs
/// only when `TCG_A64_REGION_LICM` is set, so the shipping aarch64 pipeline is
/// byte-identical until a differential corpus certifies a default-ON flip
/// (mirroring the x86 rollout, which shipped behind `TCG_REGION_LICM` first).
fn region_licm_enabled() -> bool {
    crate::env_lock::var_os("TCG_A64_REGION_LICM").is_some()
}

/// Driver: repeatedly attempt one region hoist, recomputing dominators and
/// loops after each CFG surgery (bounded — one hoist per invocation, at most
/// 64 rounds). Returns whether anything was hoisted.
fn region_licm_run(func: &mut MachFunction) -> bool {
    let mut changed = false;
    let mut guard = 0;
    loop {
        let dom = DomTree::compute(func);
        let analysis = LoopAnalysis::compute(func, &dom);
        if analysis.is_empty() {
            break;
        }
        let loops: Vec<NaturalLoop> = analysis.all_loops().cloned().collect();
        if !region_licm_hoist(func, &loops, &dom) {
            break;
        }
        changed = true;
        guard += 1;
        if guard >= 64 {
            break;
        }
    }
    changed
}

/// The single VReg an instruction defines, if it is a value-producer whose
/// first operand is a plain VReg (the local convention used by the region
/// scan; mirrors x86 `region_def_of`).
fn region_def_of(inst: &MachInst) -> Option<VReg> {
    single_inst_def(inst)
}

/// Retarget every CFG edge `from -> old_to` to `from -> new_to`: the branch
/// instructions' `Block` operands, the `succs` list, AND both targets' `preds`
/// lists (unlike the x86 ISel IR, the aarch64 `MachBlock` carries a
/// materialized `preds` list that `DomTree`/`LoopAnalysis` read directly, so
/// it must be kept in sync). The caller guarantees `from` has exactly ONE edge
/// to `old_to` (the `retain` below removes every occurrence).
fn region_retarget_edge(func: &mut MachFunction, from: BlockId, old_to: BlockId, new_to: BlockId) {
    let inst_ids: Vec<InstId> = func.block(from).insts.clone();
    for iid in inst_ids {
        for op in &mut func.inst_mut(iid).operands {
            if let MachOperand::Block(t) = op
                && *t == old_to
            {
                *t = new_to;
            }
        }
    }
    for s in &mut func.block_mut(from).succs {
        if *s == old_to {
            *s = new_to;
        }
    }
    func.block_mut(old_to).preds.retain(|p| *p != from);
    func.block_mut(new_to).preds.push(from);
}

/// True when `block` can observe NZCV state from its predecessors: some
/// instruction reads the flags before any instruction writes them. The region
/// surgery changes which block precedes `outer.header` / `inner.header` /
/// `exit_blk` at runtime, so each must be flag-dead at entry. At LICM time the
/// materialized-boolean lowering keeps every compare adjacent to its consumer
/// in one block (cmp-branch fusion runs later), so this normally holds; the
/// check makes the port fail closed on any exception. `BCond`/`Bcc` read NZCV
/// but are not in `effects::reads_flags` (that set serves CSE/scheduling), so
/// they are added explicitly here.
fn region_nzcv_live_into_block(func: &MachFunction, block: BlockId) -> bool {
    for &iid in &func.block(block).insts {
        let op = func.inst(iid).opcode;
        if reads_flags(op) || matches!(op, AArch64Opcode::BCond | AArch64Opcode::Bcc) {
            return true;
        }
        if writes_flags(op) {
            return false;
        }
    }
    false
}

/// Evaluate an AArch64 condition-code immediate (the `convert_isel_operand_to_ir`
/// encoding: 0=EQ 1=NE 2=HS 3=LO 8=HI 9=LS 10=GE 11=LT 12=GT 13=LE) on the
/// operands `(a, b)` of the flag-setting `CMP a, b`. Restricted to operands in
/// `[0, i32::MAX]` so signed and unsigned comparisons coincide and the compare
/// width (Wn vs Xn) cannot change the result; `None` (unknown — fail safe)
/// outside that range or for flag codes (MI/PL/VS/VC) this cannot model.
fn region_eval_cc(cc: i64, a: i64, b: i64) -> Option<bool> {
    const MAXV: i64 = i32::MAX as i64;
    if !(0..=MAXV).contains(&a) || !(0..=MAXV).contains(&b) {
        return None;
    }
    match cc {
        0 => Some(a == b),      // EQ
        1 => Some(a != b),      // NE
        2 | 10 => Some(a >= b), // HS / GE
        3 | 11 => Some(a < b),  // LO / LT
        8 | 12 => Some(a > b),  // HI / GT
        9 | 13 => Some(a <= b), // LS / LE
        _ => None,
    }
}

/// Forward constant propagation over one block into `vals`: `MovI` immediates
/// (range-restricted to `[0, i32::MAX]`) and `MovR` copies of known values.
/// Every other value producer makes its def unknown. Reads consult
/// `untrusted` (see [`region_loop_runs_at_least_once`]): a vreg with a def
/// outside the trusted region never contributes a value, so a stale
/// chain-seeded constant cannot flow through a copy.
fn region_interp_const_defs(
    func: &MachFunction,
    block: BlockId,
    vals: &mut HashMap<VReg, i64>,
    untrusted: &HashSet<VReg>,
) {
    const MAXV: i64 = i32::MAX as i64;
    for &iid in &func.block(block).insts {
        let inst = func.inst(iid);
        match (inst.opcode, inst.operands.as_slice()) {
            // MovI and Movz are the SAME operation (aliased in the encoder):
            // a single-16-bit-immediate constant load. isel emits Movz; the
            // guard must treat both identically or it never sees the loop's
            // entry constants and fails to prove >=1-trip.
            (
                AArch64Opcode::MovI | AArch64Opcode::Movz,
                [MachOperand::VReg(d), MachOperand::Imm(c)],
            ) => {
                if (0..=MAXV).contains(c) {
                    vals.insert(*d, *c);
                } else {
                    vals.remove(d);
                }
            }
            (AArch64Opcode::MovR, [MachOperand::VReg(d), MachOperand::VReg(s)]) => {
                match vals.get(s).copied().filter(|_| !untrusted.contains(s)) {
                    Some(v) => {
                        vals.insert(*d, v);
                    }
                    None => {
                        vals.remove(d);
                    }
                }
            }
            _ => {
                for_each_inst_def(inst, |d| {
                    vals.remove(&d);
                });
            }
        }
    }
}

/// Prove the loop executes at least once by CONCRETELY evaluating its entry
/// guard on the loop-entry constant state (the aarch64 port of the x86
/// `loop_runs_at_least_once`, which the pure-call and region tiers there share).
/// Returns `false` (not proven) whenever any needed value is unknown — a false
/// negative merely skips the hoist; a false positive would be a miscompile, so
/// the guard is evaluated by faithful interpretation and the branch DIRECTION
/// is decided by loop-body membership of the concretely-taken successor.
///
/// At LICM time the frontend's `while`-guard shape is materialized-boolean
/// (`select_cmp` + `select_brif`; cmp-branch fusion runs later):
/// `CmpRR/CmpRI; CSet b, cc; ...; CmpRI b, #0; BCond NE, then; B else`.
/// Constants are seeded from the entry path (the idom chain up to the
/// preheader — in-loop blocks are never on this chain, pinning a loop-carried
/// counter to its first-header-visit INIT value), then the header is walked
/// tracking the last compare's operands as the flag state.
///
/// STRICTER THAN THE X86 ORIGINAL: a consulted vreg is trusted only when
/// EVERY one of its defining blocks lies on the idom chain or inside `lp.body`
/// (`untrusted` below). A def in any other block (e.g. the body of a
/// grand-outer loop re-entering this preheader with a different value, or an
/// off-chain diamond arm) would make the chain-seeded constant wrong on later
/// entries; such vregs are treated as unknown and the proof fails safe.
fn region_loop_runs_at_least_once(
    func: &MachFunction,
    lp: &NaturalLoop,
    preheader: BlockId,
    dom: &DomTree,
) -> bool {
    if !dom.dominates(preheader, lp.header) {
        return false;
    }

    // The idom chain from the preheader up to the entry, entry-first.
    let mut chain: Vec<BlockId> = Vec::new();
    let mut b = preheader;
    loop {
        chain.push(b);
        match dom.idom(b) {
            Some(up) if up != b => b = up,
            _ => break,
        }
    }
    chain.reverse();
    let chain_set: HashSet<BlockId> = chain.iter().copied().collect();

    // Vregs with a def in a block that is neither on the chain nor in the loop
    // body: their value at the preheader is not a pure function of the chain,
    // so they are never consulted (see the doc comment).
    let mut untrusted: HashSet<VReg> = HashSet::new();
    for &block_id in &func.block_order {
        if chain_set.contains(&block_id) || lp.body.contains(&block_id) {
            continue;
        }
        for &iid in &func.block(block_id).insts {
            for_each_inst_def(func.inst(iid), |d| {
                untrusted.insert(d);
            });
        }
    }

    let mut vals: HashMap<VReg, i64> = HashMap::new();
    for &blk in &chain {
        region_interp_const_defs(func, blk, &mut vals, &untrusted);
    }
    let known = |vals: &HashMap<VReg, i64>, v: &VReg| -> Option<i64> {
        vals.get(v).copied().filter(|_| !untrusted.contains(v))
    };

    // Walk the header, extending `vals` and tracking the last compare's
    // operands as `flags`, until a branch resolves concretely.
    const MAXV: i64 = i32::MAX as i64;
    let mut flags: Option<(i64, i64)> = None;
    for &iid in &func.block(lp.header).insts {
        let inst = func.inst(iid);
        let ops = inst.operands.as_slice();
        match inst.opcode {
            AArch64Opcode::CmpRR => match ops {
                [MachOperand::VReg(a), MachOperand::VReg(c)] => {
                    match (known(&vals, a), known(&vals, c)) {
                        (Some(x), Some(y)) => flags = Some((x, y)),
                        _ => return false,
                    }
                }
                _ => return false,
            },
            AArch64Opcode::CmpRI => match ops {
                [MachOperand::VReg(a), MachOperand::Imm(c)] => match known(&vals, a) {
                    Some(x) if (0..=MAXV).contains(c) => flags = Some((x, *c)),
                    _ => return false,
                },
                _ => return false,
            },
            AArch64Opcode::CSet => match ops {
                [MachOperand::VReg(d), MachOperand::Imm(cc)] => {
                    let Some((x, y)) = flags else { return false };
                    match region_eval_cc(*cc, x, y) {
                        Some(t) => {
                            vals.insert(*d, i64::from(t));
                        }
                        None => return false,
                    }
                }
                _ => return false,
            },
            AArch64Opcode::BCond => match ops {
                [MachOperand::Imm(cc), MachOperand::Block(t)] => {
                    let Some((x, y)) = flags else { return false };
                    match region_eval_cc(*cc, x, y) {
                        // Taken: the guard resolves here.
                        Some(true) => return lp.body.contains(t),
                        // Not taken: fall through to the next instruction
                        // (the explicit `B else` this lowering always emits).
                        Some(false) => {}
                        None => return false,
                    }
                }
                _ => return false,
            },
            AArch64Opcode::Cbz | AArch64Opcode::Cbnz => match ops {
                [MachOperand::VReg(v), MachOperand::Block(t)] => {
                    let Some(x) = known(&vals, v) else {
                        return false;
                    };
                    let taken = (inst.opcode == AArch64Opcode::Cbz) == (x == 0);
                    if taken {
                        return lp.body.contains(t);
                    }
                }
                _ => return false,
            },
            AArch64Opcode::B => match ops {
                [MachOperand::Block(t)] => return lp.body.contains(t),
                _ => return false,
            },
            AArch64Opcode::MovI | AArch64Opcode::Movz => {
                if let [MachOperand::VReg(d), MachOperand::Imm(c)] = ops {
                    if (0..=MAXV).contains(c) {
                        vals.insert(*d, *c);
                    } else {
                        vals.remove(d);
                    }
                } else {
                    for_each_inst_def(inst, |d| {
                        vals.remove(&d);
                    });
                }
            }
            AArch64Opcode::MovR => {
                if let [MachOperand::VReg(d), MachOperand::VReg(s)] = ops {
                    match known(&vals, s) {
                        Some(v) => {
                            vals.insert(*d, v);
                        }
                        None => {
                            vals.remove(d);
                        }
                    }
                } else {
                    for_each_inst_def(inst, |d| {
                        vals.remove(&d);
                    });
                }
            }
            op => {
                // Any unmodeled flag writer or barrier invalidates the tracked
                // compare state; any unmodeled control transfer fails safe;
                // any other value producer loses its def.
                if writes_flags(op) || opcode_effect(op).is_barrier() {
                    flags = None;
                }
                if inst.is_branch() || inst.is_terminator() {
                    return false;
                }
                for_each_inst_def(inst, |d| {
                    vals.remove(&d);
                });
            }
        }
    }
    false
}

/// Attempt ONE whole-inner-loop hoist: move a provably outer-invariant inner
/// loop (plus the INIT prefix of its preheader) out of its enclosing outer
/// loop so it runs once instead of every outer iteration. Direct port of the
/// x86 `region_licm_hoist` (design §8 v2) onto the `MachFunction` arena IR,
/// with the aarch64-specific additions called out inline. Every legality miss
/// DECLINES to the unchanged original — the transform is fail-safe by
/// construction.
///
/// SOUNDNESS (all must hold; see the x86 original for the full argument):
///   L1  inner nested in outer; `ip = inner.preheader` inside `outer.body`.
///   L2  every inner-loop instruction is memory-Pure (no load/store/call),
///       carries no implicit/fixed-register state, and is not a Phi.
///   L4  the inner loop has exactly ONE exit block, inside `outer.body`, and
///       (stricter than x86) the single exit EDGE leaves from `inner.header` —
///       the edge surgery below rewires exactly that edge.
///   L5  `inner.header` dominates every outer latch.
///   L6  the outer loop provably runs >= 1 time
///       ([`region_loop_runs_at_least_once`]).
///   P   `outer.preheader` (`op_pre`) and `ip` are single-successor blocks
///       ending in an explicit `B` to their header (layout-order independence
///       for the moved blocks; the seam retargets rewrite exactly one edge).
///   INIT every inner live-in is EITHER defined in `ip` by a relocatable
///       `MovI`/`MovR` whose sources chain within `ip` or are outer-invariant
///       (the INIT cluster), OR is itself outer-invariant.
///   SEP no non-INIT instruction in `ip` reads an INIT def.
///   INV no register defined in the REGION (INIT defs ∪ inner defs) is
///       redefined elsewhere in `outer.body`.
///   NZCV (aarch64-specific) the blocks whose runtime predecessor changes
///       (`outer.header`, `inner.header`, `exit_blk`) are flag-dead at entry.
///   PHI  (aarch64-specific) those same blocks contain no Phi — their preds
///       lists change, and Phi operands are keyed to predecessors.
/// Fail-closed structural check of the region-LICM CFG surgery. Verifies the
/// invariants a correct edge-retarget must preserve; a violation is a TRANSFORM
/// BUG and panics (the compile fails closed — never ships a miscompiled object).
///
/// Checks, all O(blocks + edges):
///  1. succ/pred bidirectional consistency: every `a -> b` in `a.succs` has a
///     matching `b <- a` in `b.preds`, and vice versa. A dropped or mis-directed
///     retarget desyncs these — the exact CFG-surgery failure class.
///  2. Every block is reachable from entry (no block orphaned by the surgery).
///  3. The synthesized run-once preheader `sp` has exactly one successor, the
///     inner header, and the retargeted `exit` is reachable (the inner loop's
///     result still flows out).
fn region_verify_cfg_after_surgery(
    func: &MachFunction,
    sp: BlockId,
    inner_header: BlockId,
    exit: BlockId,
) {
    // (1) succ/pred bidirectional consistency.
    for &a in &func.block_order {
        for &b in &func.block(a).succs {
            assert!(
                func.block(b).preds.contains(&a),
                "region-LICM CFG surgery bug in fn `{}`: edge {a:?} -> {b:?} in succs                  but {a:?} absent from {b:?}.preds (fail-closed)",
                func.name
            );
        }
        for &p in &func.block(a).preds {
            assert!(
                func.block(p).succs.contains(&a),
                "region-LICM CFG surgery bug in fn `{}`: edge {p:?} -> {a:?} in preds                  but {a:?} absent from {p:?}.succs (fail-closed)",
                func.name
            );
        }
    }

    // (2) reachability from entry (no orphaned block).
    let mut seen: HashSet<BlockId> = HashSet::new();
    let mut stack = vec![func.entry];
    while let Some(b) = stack.pop() {
        if seen.insert(b) {
            for &s in &func.block(b).succs {
                stack.push(s);
            }
        }
    }
    for &b in &func.block_order {
        assert!(
            seen.contains(&b),
            "region-LICM CFG surgery bug in fn `{}`: block {b:?} unreachable from entry              after the hoist (fail-closed)",
            func.name
        );
    }

    // (3) the run-once preheader feeds exactly the inner header; exit reachable.
    assert_eq!(
        func.block(sp).succs.as_slice(),
        &[inner_header],
        "region-LICM CFG surgery bug in fn `{}`: run-once preheader {sp:?} must have the          inner header {inner_header:?} as its sole successor (fail-closed)",
        func.name
    );
    assert!(
        seen.contains(&exit),
        "region-LICM CFG surgery bug in fn `{}`: retargeted exit {exit:?} unreachable          from entry (inner-loop result does not flow out) (fail-closed)",
        func.name
    );
}

/// Fail-closed VALUE-LEVEL LICM net (X5): after any hoist into `preheader`,
/// verify no instruction READS a VReg that is DEFINED LATER in that same block —
/// a use-before-def the motion would have introduced. This complements the
/// CFG-structural [`region_verify_cfg_after_surgery`] with the operand-value
/// property and covers BOTH the value-producer tier ([`hoist_loop_invariants`])
/// and the pure-call cluster tier ([`hoist_pure_call_clusters`]).
///
/// SOUND, and false-positive-free, by restricting to SINGLE-DEF VRegs. The
/// machine IR is NOT strict SSA at LICM time (block-argument copies can reuse a
/// VReg along different paths — see [`hoist_loop_invariants`]), so a VReg defined
/// BOTH in a dominating block AND in the preheader could read its dominating def
/// legitimately before a preheader redef. We therefore consider only VRegs with
/// `def_counts == 1`: their single def is their ONLY def, so any occurrence
/// strictly before that def-site is an unambiguous use-before-def. This is
/// the ordinary value-producer and pure-call-result class LICM hoists (their
/// invariance gates require `def_counts == 1`). Path-reused multi-def VRegs are
/// conservatively skipped (never falsely flagged). The one admitted multi-def
/// class — immediate-only MOVZ/MOVK constant chains — is checked separately by
/// [`verify_preheader_constant_chains`]. Panics on violation — a transform bug
/// must fail closed, never ship a miscompiled hoist.
fn verify_preheader_defs_precede_uses(
    func: &MachFunction,
    preheader: BlockId,
    def_counts: &HashMap<VReg, usize>,
) {
    let insts = &func.block(preheader).insts;
    let mut def_pos: HashMap<VReg, usize> = HashMap::new();
    for (i, &iid) in insts.iter().enumerate() {
        for_each_inst_def(func.inst(iid), |d| {
            if def_counts.get(&d).copied().unwrap_or(0) == 1 {
                def_pos.entry(d).or_insert(i);
            }
        });
    }
    for (i, &iid) in insts.iter().enumerate() {
        let inst = func.inst(iid);
        aarch64_for_each_use_position(inst.opcode, inst.operands.len(), |pos| {
            if let Some(MachOperand::VReg(v)) = inst.operands.get(pos)
                && let Some(&dp) = def_pos.get(v)
            {
                assert!(
                    i >= dp,
                    "LICM preheader use-before-def in fn `{}`: single-def vreg {v:?} used at \
                     index {i} but defined at index {dp} in preheader {preheader:?} — a hoist \
                     reordered a def below its use (fail-closed)",
                    func.name
                );
            }
        });
    }
}

/// Fail-closed X5 companion for the one deliberately multi-definition LICM
/// class: an immediate-only MOVZ/MOVN/MOVI + MOVK constant-materialization
/// chain.  The ordinary verifier cannot treat the carrier's first definition as
/// its final value, because each MOVK both reads and partially redefines it.
///
/// Admission already proves the chain shape and that these are every definition
/// of `carrier`.  After motion, validate the remaining value-order obligations:
/// every chain instruction is present contiguously in its recorded order, and
/// every non-chain use of the carrier occurs only after the final patch.  A
/// splice/reordering bug therefore stops compilation instead of exposing a
/// partial literal to the consuming FMOV.
fn verify_preheader_constant_chains(
    func: &MachFunction,
    preheader: BlockId,
    chains: &[(VReg, Vec<InstId>)],
) {
    let insts = &func.block(preheader).insts;
    let positions: HashMap<InstId, usize> = insts
        .iter()
        .copied()
        .enumerate()
        .map(|(position, id)| (id, position))
        .collect();

    for (carrier, chain) in chains {
        assert!(
            !chain.is_empty(),
            "LICM constant-chain validation bug in fn `{}`: empty chain for {carrier:?} \
             (fail-closed)",
            func.name
        );
        let first = *positions.get(&chain[0]).unwrap_or_else(|| {
            panic!(
                "LICM constant-chain splice bug in fn `{}`: chain head {:?} for {carrier:?} \
                 missing from preheader {preheader:?} (fail-closed)",
                func.name, chain[0]
            )
        });
        for (offset, id) in chain.iter().enumerate() {
            let position = positions.get(id).copied().unwrap_or_else(|| {
                panic!(
                    "LICM constant-chain splice bug in fn `{}`: chain instruction {id:?} for \
                     {carrier:?} missing from preheader {preheader:?} (fail-closed)",
                    func.name
                )
            });
            assert_eq!(
                position,
                first + offset,
                "LICM constant-chain order bug in fn `{}`: instruction {id:?} for {carrier:?} \
                 is at index {position}, expected {} in preheader {preheader:?} (fail-closed)",
                func.name,
                first + offset
            );
        }

        let last = first + chain.len() - 1;
        let chain_ids: HashSet<InstId> = chain.iter().copied().collect();
        for (position, &id) in insts.iter().enumerate() {
            if chain_ids.contains(&id) {
                continue;
            }
            let inst = func.inst(id);
            aarch64_for_each_use_position(inst.opcode, inst.operands.len(), |pos| {
                if inst.operands.get(pos) == Some(&MachOperand::VReg(*carrier)) {
                    assert!(
                        position > last,
                        "LICM constant-chain use-before-complete in fn `{}`: carrier {carrier:?} \
                         used at index {position} but its final patch is at index {last} in \
                         preheader {preheader:?} (fail-closed)",
                        func.name
                    );
                }
            });
        }
    }
}

fn region_licm_hoist(func: &mut MachFunction, loops: &[NaturalLoop], dom: &DomTree) -> bool {
    let dbg = std::env::var_os("TCG_A64_REGION_LICM_DEBUG").is_some();

    for inner in loops {
        // The smallest strictly-enclosing outer loop, from the loop forest.
        let Some(outer) = inner
            .parent
            .and_then(|h| loops.iter().find(|o| o.header == h))
        else {
            continue; // top-level loop — nothing to hoist out of.
        };
        let note = |msg: &str| {
            if dbg {
                eprintln!(
                    "[a64-region-licm] fn={} inner={:?} outer={:?} decline: {}",
                    func.name, inner.header, outer.header, msg
                );
            }
        };

        // L1: inner preheader present, inside the outer body.
        let Some(ip) = inner.preheader.filter(|p| outer.body.contains(p)) else {
            continue;
        };
        // P: outer preheader present.
        let Some(op_pre) = outer.preheader else {
            continue;
        };

        // L2 + operand hygiene over every inner-loop instruction: memory-Pure,
        // no Phi, no implicit defs/uses, no fixed-register / frame-lowering /
        // jump-table operands. (`Special` — SP/XZR/WZR reads — and `Symbol` /
        // `StackSlot` address material are allowed: they are constants or
        // function-lifetime-invariant, per the Adrp/AddPCRel hoist rationale
        // above.)
        let mut l2_ok = true;
        'l2: for &b in &inner.body {
            for &iid in &func.block(b).insts {
                let inst = func.inst(iid);
                if !opcode_effect(inst.opcode).is_pure()
                    || inst.opcode.is_phi()
                    || !inst.implicit_defs.is_empty()
                    || !inst.implicit_uses.is_empty()
                    || inst.operands.iter().any(|op| {
                        matches!(
                            op,
                            MachOperand::PReg(_)
                                | MachOperand::MemOp { .. }
                                | MachOperand::JumpTableIndex(_)
                                | MachOperand::IncomingArg(_)
                        )
                    })
                {
                    l2_ok = false;
                    break 'l2;
                }
            }
        }
        if !l2_ok {
            note("inner loop not pure/self-contained");
            continue;
        }

        // L4: exactly one exit block, inside the outer body, and every exit
        // edge leaves from `inner.header` (stricter than the x86 original,
        // whose edge surgery silently assumed it).
        let mut exits: HashSet<BlockId> = HashSet::new();
        let mut exit_from_non_header = false;
        for &b in &inner.body {
            for &s in &func.block(b).succs {
                if !inner.body.contains(&s) {
                    exits.insert(s);
                    if b != inner.header {
                        exit_from_non_header = true;
                    }
                }
            }
        }
        if exits.len() != 1 || exit_from_non_header {
            note("inner loop does not have a single header-exit");
            continue;
        }
        let exit_blk = *exits.iter().next().unwrap();
        if !outer.body.contains(&exit_blk) || exit_blk == outer.header || exit_blk == ip {
            continue;
        }
        if func
            .block(inner.header)
            .succs
            .iter()
            .filter(|s| **s == exit_blk)
            .count()
            != 1
        {
            continue; // duplicate exit edges desync the retarget accounting
        }

        // L5: inner.header dominates every outer latch.
        let latches: Vec<BlockId> = func
            .block(outer.header)
            .preds
            .iter()
            .copied()
            .filter(|p| outer.body.contains(p))
            .collect();
        if latches.is_empty() || !latches.iter().all(|l| dom.dominates(inner.header, *l)) {
            continue;
        }

        // L6: the outer loop provably runs at least once.
        if !region_loop_runs_at_least_once(func, outer, op_pre, dom) {
            note("outer loop not proven >=1-trip");
            continue;
        }

        // P: `op_pre` and `ip` are single-successor blocks ending in an
        // explicit `B` to their loop header.
        let ends_with_b_to = |f: &MachFunction, blk: BlockId, target: BlockId| -> bool {
            f.block(blk).insts.last().is_some_and(|&iid| {
                let t = f.inst(iid);
                t.opcode == AArch64Opcode::B
                    && matches!(t.operands.first(), Some(MachOperand::Block(b)) if *b == target)
            })
        };
        let single_succ = |f: &MachFunction, blk: BlockId, s: BlockId| {
            let succs = &f.block(blk).succs;
            succs.len() == 1 && succs[0] == s
        };
        if !single_succ(func, op_pre, outer.header) || !ends_with_b_to(func, op_pre, outer.header) {
            note("outer preheader lacks a sole explicit B to the outer header");
            continue;
        }
        if !single_succ(func, ip, inner.header) || !ends_with_b_to(func, ip, inner.header) {
            note("inner preheader lacks a sole explicit B to the inner header");
            continue;
        }

        // Seam pred-multiplicity: the retarget `retain` removes every
        // occurrence, so each rewired edge must be unique in the preds list.
        let pred_count = |f: &MachFunction, blk: BlockId, p: BlockId| {
            f.block(blk).preds.iter().filter(|q| **q == p).count()
        };
        if pred_count(func, outer.header, op_pre) != 1
            || pred_count(func, inner.header, ip) != 1
            || pred_count(func, exit_blk, inner.header) != 1
        {
            continue;
        }

        // PHI seam guard: the preds of these three blocks change.
        let has_phi = |f: &MachFunction, blk: BlockId| {
            f.block(blk)
                .insts
                .iter()
                .any(|&iid| f.inst(iid).opcode.is_phi())
        };
        if has_phi(func, outer.header) || has_phi(func, inner.header) || has_phi(func, exit_blk) {
            note("phi at a retargeted seam block");
            continue;
        }

        // NZCV seam guard: the runtime predecessor of these blocks changes, so
        // each must be provably flag-dead at entry.
        if region_nzcv_live_into_block(func, outer.header)
            || region_nzcv_live_into_block(func, inner.header)
            || region_nzcv_live_into_block(func, exit_blk)
        {
            note("NZCV live into a retargeted seam block");
            continue;
        }

        // Region defs / inner live-ins.
        let mut inner_defs: HashSet<VReg> = HashSet::new();
        for &b in &inner.body {
            for &iid in &func.block(b).insts {
                for_each_inst_def(func.inst(iid), |d| {
                    inner_defs.insert(d);
                });
            }
        }
        let mut inner_reads: HashSet<VReg> = HashSet::new();
        for &b in &inner.body {
            for &iid in &func.block(b).insts {
                let inst = func.inst(iid);
                aarch64_for_each_use_position(inst.opcode, inst.operands.len(), |pos| {
                    if let Some(MachOperand::VReg(v)) = inst.operands.get(pos)
                        && !inner_defs.contains(v)
                    {
                        inner_reads.insert(*v);
                    }
                });
            }
        }

        // A vreg is OUTER-INVARIANT iff it has no def anywhere in outer.body.
        let defined_in_outer = |f: &MachFunction, v: VReg| -> bool {
            outer.body.iter().any(|b| {
                f.block(*b)
                    .insts
                    .iter()
                    .any(|&iid| inst_defines_vreg(f.inst(iid), v))
            })
        };

        // The INIT cluster = the transitive backward closure, WITHIN `ip`, of
        // the inner loop's live-in / carried-register initializers. The
        // frontend lowers these as a copy chain (`carried = MovR const;
        // const = MovI imm`), so a relocatable INIT source may itself be
        // another INIT-cluster def in `ip`; only a source defined in the outer
        // body OUTSIDE `ip` (a real outer-varying value, e.g. a snapshot's
        // accumulator) makes an instruction non-invariant and declines.
        let ip_insts: Vec<InstId> = func.block(ip).insts.clone();
        let mut ip_def_idx: HashMap<VReg, usize> = HashMap::new();
        for (idx, &iid) in ip_insts.iter().enumerate() {
            for_each_inst_def(func.inst(iid), |d| {
                ip_def_idx.entry(d).or_insert(idx);
            });
        }
        // Seed: `ip` defs of a vreg the inner body reads or carries (redefines).
        let mut init_set: HashSet<usize> = HashSet::new();
        let mut init_defs: HashSet<VReg> = HashSet::new();
        let mut worklist: Vec<usize> = Vec::new();
        for (idx, &iid) in ip_insts.iter().enumerate() {
            let mut seeds = false;
            for_each_inst_def(func.inst(iid), |d| {
                if inner_reads.contains(&d) || inner_defs.contains(&d) {
                    seeds = true;
                }
            });
            if seeds {
                worklist.push(idx);
            }
        }
        let mut init_bad = false;
        while let Some(idx) = worklist.pop() {
            if !init_set.insert(idx) {
                continue;
            }
            let inst = func.inst(ip_insts[idx]);
            let self_def = region_def_of(inst);
            // Relocatable INIT forms on aarch64: full-register constant /
            // copy moves with no fixed-register, flag, or tied-def coupling.
            // (`Movz`/`Movk` chains are multi-def partial writes and are
            // deliberately NOT admitted in v1.)
            let relocatable = matches!(inst.opcode, AArch64Opcode::MovI | AArch64Opcode::MovR)
                && inst.implicit_defs.is_empty()
                && inst.implicit_uses.is_empty()
                && inst
                    .operands
                    .iter()
                    .all(|op| matches!(op, MachOperand::VReg(_) | MachOperand::Imm(_)));
            if !relocatable {
                init_bad = true;
                break;
            }
            let mut src_bad = false;
            for (oi, op) in inst.operands.iter().enumerate() {
                if oi == 0 {
                    continue; // destination
                }
                if let MachOperand::VReg(s) = op {
                    if Some(*s) == self_def {
                        continue; // self-reference
                    }
                    if let Some(&j) = ip_def_idx.get(s) {
                        worklist.push(j); // chained INIT def within ip
                    } else if defined_in_outer(func, *s) {
                        src_bad = true; // outer-varying source → not invariant
                    }
                }
            }
            if src_bad {
                init_bad = true;
                break;
            }
            if let Some(d) = self_def {
                init_defs.insert(d);
            }
        }
        if init_bad {
            note("ip has a non-relocatable or outer-varying inner-live-in def");
            continue;
        }

        // INIT completeness: every inner live-in is an INIT def or
        // outer-invariant.
        if inner_reads
            .iter()
            .any(|v| !init_defs.contains(v) && defined_in_outer(func, *v))
        {
            note("inner loop reads an outer-varying value not in the INIT cluster");
            continue;
        }

        // SEP: no non-INIT instruction in `ip` may read an INIT def.
        let mut sep_bad = false;
        for (idx, &iid) in ip_insts.iter().enumerate() {
            if init_set.contains(&idx) {
                continue;
            }
            let inst = func.inst(iid);
            aarch64_for_each_use_position(inst.opcode, inst.operands.len(), |pos| {
                if let Some(MachOperand::VReg(v)) = inst.operands.get(pos)
                    && init_defs.contains(v)
                {
                    sep_bad = true;
                }
            });
        }
        if sep_bad {
            note("ip split not clean (REST reads an INIT def)");
            continue;
        }

        // INV: no region def (INIT defs ∪ inner defs) is redefined elsewhere
        // in outer.body (outside the INIT cluster and inner.body).
        let region_defs: HashSet<VReg> = init_defs.union(&inner_defs).copied().collect();
        let mut inv_bad = false;
        for &b in &outer.body {
            if inner.body.contains(&b) {
                continue;
            }
            for (idx, &iid) in func.block(b).insts.iter().enumerate() {
                if b == ip && init_set.contains(&idx) {
                    continue; // the INIT defs themselves
                }
                for_each_inst_def(func.inst(iid), |d| {
                    if region_defs.contains(&d) {
                        inv_bad = true;
                    }
                });
            }
        }
        if inv_bad {
            note("a region def is redefined elsewhere in the outer loop");
            continue;
        }

        // ---- All legality holds — perform the surgery. -------------------
        // Extract the INIT InstIds out of `ip` (highest index first so the
        // remaining indices stay valid), preserving their original order.
        let mut init_idx: Vec<usize> = init_set.iter().copied().collect();
        init_idx.sort_unstable();
        let init_inst_ids: Vec<InstId> = init_idx.iter().map(|&i| ip_insts[i]).collect();
        {
            let ipb = func.block_mut(ip);
            for &i in init_idx.iter().rev() {
                ipb.insts.remove(i);
            }
        }

        // Synthesize the run-once preheader `sp` = INIT cluster + B inner.header.
        // The INIT InstIds are MOVED (not cloned), so provenance stays keyed to
        // the same arena entries; the new `B` is pass-created and reports
        // UNATTRIBUTED provenance, which is the safe default.
        let sp = func.create_block();
        for &iid in &init_inst_ids {
            func.append_inst(sp, iid);
        }
        let b_inner = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(inner.header)],
        ));
        func.append_inst(sp, b_inner);

        // Edge surgery (branch operands + succs + preds all maintained):
        //   op_pre -> outer.header      becomes  op_pre -> sp
        //   ip     -> inner.header      becomes  ip     -> exit_blk
        //   inner.header -> exit_blk    becomes  inner.header -> outer.header
        //   (new)  sp -> inner.header
        region_retarget_edge(func, op_pre, outer.header, sp);
        region_retarget_edge(func, ip, inner.header, exit_blk);
        region_retarget_edge(func, inner.header, exit_blk, outer.header);
        func.add_edge(sp, inner.header);

        // Layout: pull the inner-loop blocks out and place [sp, <inner blocks
        // in their prior relative order>] immediately after `op_pre`. All the
        // moved blocks end in explicit terminators (P), so layout order only
        // affects fall-through elision, not semantics.
        let inner_seq: Vec<BlockId> = func
            .block_order
            .iter()
            .copied()
            .filter(|b| inner.body.contains(b))
            .collect();
        func.block_order
            .retain(|b| !inner.body.contains(b) && *b != sp);
        let at = func
            .block_order
            .iter()
            .position(|b| *b == op_pre)
            .map(|p| p + 1)
            .unwrap_or(func.block_order.len());
        let mut seq = vec![sp];
        seq.extend(inner_seq);
        for (off, b) in seq.into_iter().enumerate() {
            func.block_order.insert(at + off, b);
        }

        // X5-net: fail-closed structural verification of the CFG surgery. This
        // catches a BUG IN THE TRANSFORM (a mis-retargeted or dropped edge)
        // rather than trusting the surgery blindly — the property that lets
        // this default-OFF pass eventually flip on. A violation panics: the
        // compile fails closed (a backend bug surfaces loudly) instead of
        // emitting a miscompiled object. Cheap: O(blocks + edges).
        region_verify_cfg_after_surgery(func, sp, inner.header, exit_blk);

        // X5 value-level net (third a64 hoist tier): the surgery relocates the
        // inner loop's INIT cluster into the synthesized preheader `sp`. Verify
        // no relocated instruction reads a single-def VReg defined later in `sp`
        // — a reorder bug the CFG-structural check above cannot see. Fresh
        // def_counts on the post-surgery function; fail-closed.
        let region_def_counts = build_def_counts(func);
        verify_preheader_defs_precede_uses(func, sp, &region_def_counts);

        if dbg {
            eprintln!(
                "[a64-region-licm] HOISTED inner {:?} out of outer {:?} (fn={}, sp={:?}, {} INIT insts, exit={:?})",
                inner.header,
                outer.header,
                func.name,
                sp,
                init_defs.len(),
                exit_blk
            );
        }
        return true; // one hoist per invocation; the driver re-analyzes.
    }
    false
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pass_manager::{AnalysisCache, MachinePass};
    use trust_cg_ir::{
        AArch64Opcode, MachFunction, MachInst, MachOperand, PassId, ProvenanceMap, RegClass,
        Signature, SpecialReg, StackSlotId, TransformKind, TrustIrInstId, VReg,
        regs::{X0, X16},
    };

    fn vreg(id: u32) -> MachOperand {
        MachOperand::VReg(VReg::new(id, RegClass::Gpr64))
    }

    fn vreg_class(id: u32, class: RegClass) -> MachOperand {
        MachOperand::VReg(VReg::new(id, class))
    }

    fn imm(val: i64) -> MachOperand {
        MachOperand::Imm(val)
    }

    fn record_identity_provenance(
        func: &MachFunction,
        first_trust_ir: u32,
    ) -> (ProvenanceMap, Vec<(TrustIrInstId, InstId)>) {
        let mut provenance = ProvenanceMap::new();
        let mut mappings = Vec::new();

        for &block_id in &func.block_order {
            for &inst_id in &func.block(block_id).insts {
                let trust_ir = TrustIrInstId(first_trust_ir + mappings.len() as u32);
                provenance.record_lowering(trust_ir, &[inst_id], PassId::new("isel"));
                mappings.push((trust_ir, inst_id));
            }
        }

        (provenance, mappings)
    }

    fn assert_identity_provenance_survived(
        provenance: &ProvenanceMap,
        mappings: &[(TrustIrInstId, InstId)],
    ) {
        for &(trust_ir, inst_id) in mappings {
            assert_eq!(
                provenance
                    .get_mach_insts(trust_ir)
                    .expect("source mapping should remain present"),
                std::slice::from_ref(&inst_id)
            );

            let entry = provenance
                .get_entry(inst_id)
                .expect("instruction should keep provenance entry");
            assert!(entry.is_active());
            assert_eq!(entry.trust_ir_origins, vec![trust_ir]);
            assert_eq!(entry.transforms.len(), 1);
            assert_eq!(&entry.transforms[0].pass, &PassId::new("isel"));
            assert_eq!(&entry.transforms[0].kind, &TransformKind::Lowered);
        }
    }

    /// Build a loop with a loop-invariant instruction:
    ///
    /// ```text
    ///   bb0 (entry):
    ///     v0 = movi #10
    ///     v1 = movi #20
    ///     b bb1
    ///
    ///   bb1 (header) <---+
    ///     v2 = add v0, v1      ← loop-invariant (v0, v1 defined outside)
    ///     v3 = add v2, v4      ← NOT invariant (v4 is defined in loop)
    ///     v4 = sub v3, #1
    ///     b.cond bb2, bb1
    ///                    |
    ///   bb2 (exit):      +
    ///     ret
    /// ```
    fn make_loop_with_invariant() -> MachFunction {
        let mut func = MachFunction::new("licm_test".to_string(), Signature::new(vec![], vec![]));
        let bb0 = func.entry;
        let bb1 = func.create_block();
        let bb2 = func.create_block();

        // bb0: define loop-invariant inputs
        let m0 = func.push_inst(MachInst::new(AArch64Opcode::MovI, vec![vreg(0), imm(10)]));
        func.append_inst(bb0, m0);
        let m1 = func.push_inst(MachInst::new(AArch64Opcode::MovI, vec![vreg(1), imm(20)]));
        func.append_inst(bb0, m1);
        let br0 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb1)],
        ));
        func.append_inst(bb0, br0);

        // bb1 (loop header):
        let add_inv = func.push_inst(MachInst::new(
            AArch64Opcode::AddRR,
            vec![vreg(2), vreg(0), vreg(1)],
        ));
        func.append_inst(bb1, add_inv);
        let add_var = func.push_inst(MachInst::new(
            AArch64Opcode::AddRR,
            vec![vreg(3), vreg(2), vreg(4)],
        ));
        func.append_inst(bb1, add_var);
        let sub = func.push_inst(MachInst::new(
            AArch64Opcode::SubRI,
            vec![vreg(4), vreg(3), imm(1)],
        ));
        func.append_inst(bb1, sub);
        let br1 = func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![MachOperand::Block(bb2), MachOperand::Block(bb1)],
        ));
        func.append_inst(bb1, br1);

        // bb2 (exit):
        let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb2, ret);

        func.add_edge(bb0, bb1);
        func.add_edge(bb1, bb2);
        func.add_edge(bb1, bb1); // back-edge

        func
    }

    #[test]
    fn test_licm_hoists_invariant() {
        let mut func = make_loop_with_invariant();

        let mut licm = LoopInvariantCodeMotion;
        assert!(licm.run(&mut func));

        // The loop-invariant `add v0, v1` should be hoisted to bb0 (preheader).
        // bb1 should now have: add_var, sub, bcond (3 instructions instead of 4)
        let bb1 = func.block(BlockId(1));
        assert_eq!(bb1.insts.len(), 3);

        // bb0 (preheader) should now have: movi, movi, add, b (4 instructions)
        let bb0 = func.block(BlockId(0));
        assert_eq!(bb0.insts.len(), 4);

        // Verify the hoisted instruction is the add
        let hoisted = func.inst(bb0.insts[2]);
        assert_eq!(hoisted.opcode, AArch64Opcode::AddRR);
        assert_eq!(hoisted.operands[1], vreg(0));
        assert_eq!(hoisted.operands[2], vreg(1));
    }

    /// REGRESSION (found by revmapfuzz): when the preheader is a ROTATED-LOOP
    /// GUARD block ending `CmpRR; BCond(cc, header); B exit`, the hoisted
    /// instruction must land BEFORE that whole branch tail. The old `len - 1`
    /// insertion put it between the BCond and the B — executed only on the
    /// loop-SKIPPED path, so the loop body read an undefined register (the
    /// `a[i] = a[i]^a[i]` kernel: the body's `MovI 0` was hoisted below the
    /// guard branch and `str` stored garbage).
    #[test]
    fn test_licm_hoist_into_guard_preheader_lands_before_branch_tail() {
        let mut func =
            MachFunction::new("licm_guard_ph".to_string(), Signature::new(vec![], vec![]));
        let guard = func.entry; // rotated-loop guard doubles as the preheader
        let header = func.create_block();
        let latch = func.create_block();
        let exit = func.create_block();

        // guard: inputs; CmpRR(v0, v1); BCond -> header; B -> exit.
        let m0 = func.push_inst(MachInst::new(AArch64Opcode::MovI, vec![vreg(0), imm(10)]));
        func.append_inst(guard, m0);
        let m1 = func.push_inst(MachInst::new(AArch64Opcode::MovI, vec![vreg(1), imm(20)]));
        func.append_inst(guard, m1);
        let cmp = func.push_inst(MachInst::new(AArch64Opcode::CmpRR, vec![vreg(0), vreg(1)]));
        func.append_inst(guard, cmp);
        let bcond = func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![imm(11), MachOperand::Block(header)],
        ));
        func.append_inst(guard, bcond);
        let bexit = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(exit)],
        ));
        func.append_inst(guard, bexit);

        // header: v2 = v0 + v1 (loop-invariant), v3 = v3 - 1 (variant); b latch.
        let inv = func.push_inst(MachInst::new(
            AArch64Opcode::AddRR,
            vec![vreg(2), vreg(0), vreg(1)],
        ));
        func.append_inst(header, inv);
        let var = func.push_inst(MachInst::new(
            AArch64Opcode::SubRI,
            vec![vreg(3), vreg(3), imm(1)],
        ));
        func.append_inst(header, var);
        let bh = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(latch)],
        ));
        func.append_inst(header, bh);

        // latch: CmpRR; BCond -> header; B -> exit.
        let lcmp = func.push_inst(MachInst::new(AArch64Opcode::CmpRR, vec![vreg(3), vreg(1)]));
        func.append_inst(latch, lcmp);
        let lb = func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![imm(11), MachOperand::Block(header)],
        ));
        func.append_inst(latch, lb);
        let lbe = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(exit)],
        ));
        func.append_inst(latch, lbe);

        let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(exit, ret);

        func.add_edge(guard, header);
        func.add_edge(guard, exit);
        func.add_edge(header, latch);
        func.add_edge(latch, header);
        func.add_edge(latch, exit);

        let mut licm = LoopInvariantCodeMotion;
        assert!(licm.run(&mut func), "invariant add should hoist");

        // The invariant must now be in the guard block...
        let ginsts = &func.block(guard).insts;
        let inv_pos = ginsts
            .iter()
            .position(|&id| id == inv)
            .expect("hoisted into the guard preheader");
        // ...and STRICTLY BEFORE the compare/branch tail (CmpRR, BCond, B) so it
        // executes on the loop-entry path too.
        let cmp_pos = ginsts.iter().position(|&id| id == cmp).unwrap();
        let bcond_pos = ginsts.iter().position(|&id| id == bcond).unwrap();
        assert!(
            inv_pos < cmp_pos && inv_pos < bcond_pos,
            "hoisted instruction must precede the guard's compare+branch tail \
             (was inserted at {inv_pos}, cmp at {cmp_pos}, bcond at {bcond_pos})"
        );
    }

    #[test]
    fn test_licm_same_numeric_id_different_class_loop_def_does_not_block_hoist() {
        let mut func = MachFunction::new(
            "licm_class_exact_vreg".to_string(),
            Signature::new(vec![], vec![]),
        );
        let bb0 = func.entry;
        let bb1 = func.create_block();
        let bb2 = func.create_block();

        let gpr64_input = func.push_inst(MachInst::new(AArch64Opcode::MovI, vec![vreg(0), imm(7)]));
        func.append_inst(bb0, gpr64_input);
        let other_input = func.push_inst(MachInst::new(AArch64Opcode::MovI, vec![vreg(1), imm(9)]));
        func.append_inst(bb0, other_input);
        let br0 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb1)],
        ));
        func.append_inst(bb0, br0);

        let loop_gpr32 = func.push_inst(MachInst::new(
            AArch64Opcode::SubRI,
            vec![
                vreg_class(0, RegClass::Gpr32),
                vreg_class(0, RegClass::Gpr32),
                imm(1),
            ],
        ));
        func.append_inst(bb1, loop_gpr32);
        let invariant_add = func.push_inst(MachInst::new(
            AArch64Opcode::AddRR,
            vec![vreg(2), vreg(0), vreg(1)],
        ));
        func.append_inst(bb1, invariant_add);
        let br1 = func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![MachOperand::Block(bb2), MachOperand::Block(bb1)],
        ));
        func.append_inst(bb1, br1);

        let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb2, ret);

        func.add_edge(bb0, bb1);
        func.add_edge(bb1, bb2);
        func.add_edge(bb1, bb1);

        let mut licm = LoopInvariantCodeMotion;
        assert!(licm.run(&mut func));

        assert!(func.block(bb0).insts.contains(&invariant_add));
        assert!(func.block(bb1).insts.contains(&loop_gpr32));
        assert!(!func.block(bb1).insts.contains(&invariant_add));
    }

    #[test]
    fn test_licm_provenance_survives_hoist() {
        let mut func = make_loop_with_invariant();
        let hoisted_inst = func.block(BlockId(1)).insts[0];
        let (mut provenance, mappings) = record_identity_provenance(&func, 100);

        let mut licm = LoopInvariantCodeMotion;
        let mut analyses = AnalysisCache::new();
        let changed =
            licm.run_with_analyses_and_provenance(&mut func, &mut analyses, &mut provenance);
        assert!(changed);

        assert!(func.block(BlockId(0)).insts.contains(&hoisted_inst));
        assert!(!func.block(BlockId(1)).insts.contains(&hoisted_inst));
        assert_identity_provenance_survived(&provenance, &mappings);
    }

    #[test]
    fn test_licm_no_hoist_store() {
        // Loop with a store — should NOT be hoisted.
        let mut func = MachFunction::new("licm_store".to_string(), Signature::new(vec![], vec![]));
        let bb0 = func.entry;
        let bb1 = func.create_block();
        let bb2 = func.create_block();

        let br0 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb1)],
        ));
        func.append_inst(bb0, br0);

        let store = func.push_inst(MachInst::new(AArch64Opcode::StrRI, vec![vreg(0), imm(8)]));
        func.append_inst(bb1, store);
        let br1 = func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![MachOperand::Block(bb2), MachOperand::Block(bb1)],
        ));
        func.append_inst(bb1, br1);

        let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb2, ret);

        func.add_edge(bb0, bb1);
        func.add_edge(bb1, bb2);
        func.add_edge(bb1, bb1);

        let mut licm = LoopInvariantCodeMotion;
        assert!(!licm.run(&mut func));
    }

    #[test]
    fn test_licm_no_hoist_flag_reader() {
        // CSET reads NZCV implicitly; even with invariant explicit operands,
        // moving it out of the loop would read flags from the wrong dynamic
        // point.
        let mut func = MachFunction::new(
            "licm_flag_reader".to_string(),
            Signature::new(vec![], vec![]),
        );
        let bb0 = func.entry;
        let bb1 = func.create_block();
        let bb2 = func.create_block();

        let br0 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb1)],
        ));
        func.append_inst(bb0, br0);

        let cset = func.push_inst(MachInst::new(AArch64Opcode::CSet, vec![vreg(0), imm(0)]));
        func.append_inst(bb1, cset);
        let br1 = func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![MachOperand::Block(bb2), MachOperand::Block(bb1)],
        ));
        func.append_inst(bb1, br1);

        let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb2, ret);

        func.add_edge(bb0, bb1);
        func.add_edge(bb1, bb2);
        func.add_edge(bb1, bb1);

        let mut licm = LoopInvariantCodeMotion;
        assert!(!licm.run(&mut func));
        assert_eq!(func.block(bb1).insts[0], cset);
    }

    #[test]
    fn test_licm_no_hoist_flag_writer() {
        // ADDS writes NZCV implicitly. Hoisting it can clobber the flags used
        // by a later CSET/CSEL/branch inside the loop.
        let mut func = MachFunction::new(
            "licm_flag_writer".to_string(),
            Signature::new(vec![], vec![]),
        );
        let bb0 = func.entry;
        let bb1 = func.create_block();
        let bb2 = func.create_block();

        let m0 = func.push_inst(MachInst::new(AArch64Opcode::MovI, vec![vreg(0), imm(10)]));
        func.append_inst(bb0, m0);
        let m1 = func.push_inst(MachInst::new(AArch64Opcode::MovI, vec![vreg(1), imm(20)]));
        func.append_inst(bb0, m1);
        let br0 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb1)],
        ));
        func.append_inst(bb0, br0);

        let adds = func.push_inst(MachInst::new(
            AArch64Opcode::AddsRR,
            vec![vreg(2), vreg(0), vreg(1)],
        ));
        func.append_inst(bb1, adds);
        let br1 = func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![MachOperand::Block(bb2), MachOperand::Block(bb1)],
        ));
        func.append_inst(bb1, br1);

        let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb2, ret);

        func.add_edge(bb0, bb1);
        func.add_edge(bb1, bb2);
        func.add_edge(bb1, bb1);

        let mut licm = LoopInvariantCodeMotion;
        assert!(!licm.run(&mut func));
        assert_eq!(func.block(bb1).insts[0], adds);
    }

    #[test]
    fn test_licm_no_hoist_variant() {
        // Loop with instruction whose operand is defined in the loop.
        let mut func =
            MachFunction::new("licm_variant".to_string(), Signature::new(vec![], vec![]));
        let bb0 = func.entry;
        let bb1 = func.create_block();
        let bb2 = func.create_block();

        let br0 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb1)],
        ));
        func.append_inst(bb0, br0);

        // v1 defined in loop, v0 = add v1, #5 depends on v1
        let sub = func.push_inst(MachInst::new(
            AArch64Opcode::SubRI,
            vec![vreg(1), vreg(1), imm(1)],
        ));
        func.append_inst(bb1, sub);
        let add = func.push_inst(MachInst::new(
            AArch64Opcode::AddRI,
            vec![vreg(0), vreg(1), imm(5)],
        ));
        func.append_inst(bb1, add);
        let br1 = func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![MachOperand::Block(bb2), MachOperand::Block(bb1)],
        ));
        func.append_inst(bb1, br1);

        let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb2, ret);

        func.add_edge(bb0, bb1);
        func.add_edge(bb1, bb2);
        func.add_edge(bb1, bb1);

        let mut licm = LoopInvariantCodeMotion;
        assert!(!licm.run(&mut func));
    }

    #[test]
    fn test_licm_no_loops() {
        // No loops → LICM should be a no-op.
        let mut func = MachFunction::new("no_loops".to_string(), Signature::new(vec![], vec![]));
        let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(func.entry, ret);

        let mut licm = LoopInvariantCodeMotion;
        assert!(!licm.run(&mut func));
    }

    #[test]
    fn test_licm_transitive_invariance() {
        // v0, v1 defined outside loop.
        // v2 = add v0, v1  ← invariant
        // v3 = mul v2, v0  ← also invariant (v2 and v0 are both invariant)
        // Both should be hoisted.
        let mut func = MachFunction::new(
            "licm_transitive".to_string(),
            Signature::new(vec![], vec![]),
        );
        let bb0 = func.entry;
        let bb1 = func.create_block();
        let bb2 = func.create_block();

        let m0 = func.push_inst(MachInst::new(AArch64Opcode::MovI, vec![vreg(0), imm(10)]));
        func.append_inst(bb0, m0);
        let m1 = func.push_inst(MachInst::new(AArch64Opcode::MovI, vec![vreg(1), imm(20)]));
        func.append_inst(bb0, m1);
        let br0 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb1)],
        ));
        func.append_inst(bb0, br0);

        let add = func.push_inst(MachInst::new(
            AArch64Opcode::AddRR,
            vec![vreg(2), vreg(0), vreg(1)],
        ));
        func.append_inst(bb1, add);
        let mul = func.push_inst(MachInst::new(
            AArch64Opcode::MulRR,
            vec![vreg(3), vreg(2), vreg(0)],
        ));
        func.append_inst(bb1, mul);
        let br1 = func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![MachOperand::Block(bb2), MachOperand::Block(bb1)],
        ));
        func.append_inst(bb1, br1);

        let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb2, ret);

        func.add_edge(bb0, bb1);
        func.add_edge(bb1, bb2);
        func.add_edge(bb1, bb1);

        let mut licm = LoopInvariantCodeMotion;
        assert!(licm.run(&mut func));

        // Both add and mul should be hoisted.
        let bb1_block = func.block(BlockId(1));
        assert_eq!(bb1_block.insts.len(), 1); // just bcond

        // Preheader (bb0) should have: movi, movi, add, mul, b
        let bb0_block = func.block(BlockId(0));
        assert_eq!(bb0_block.insts.len(), 5);
    }

    #[test]
    fn test_licm_no_hoist_call() {
        // A BL (call) instruction should not be hoisted even if operands are invariant.
        let mut func = MachFunction::new("licm_call".to_string(), Signature::new(vec![], vec![]));
        let bb0 = func.entry;
        let bb1 = func.create_block();
        let bb2 = func.create_block();

        let br0 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb1)],
        ));
        func.append_inst(bb0, br0);

        let call = func.push_inst(MachInst::new(AArch64Opcode::Bl, vec![imm(0x1000)]));
        func.append_inst(bb1, call);
        let br1 = func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![MachOperand::Block(bb2), MachOperand::Block(bb1)],
        ));
        func.append_inst(bb1, br1);

        let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb2, ret);

        func.add_edge(bb0, bb1);
        func.add_edge(bb1, bb2);
        func.add_edge(bb1, bb1);

        let mut licm = LoopInvariantCodeMotion;
        assert!(!licm.run(&mut func));
    }

    #[test]
    fn test_licm_no_hoist_physical_register_call_glue() {
        // Indirect-call lowering uses fixed ABI registers:
        //
        //   x16 <- target
        //   blr x16
        //   ret <- x0
        //
        // `MovR` and `Copy` are otherwise pure, but moving either across the
        // call breaks the fixed-register dataflow that LICM does not model.
        let mut func = MachFunction::new(
            "licm_preg_call_glue".to_string(),
            Signature::new(vec![], vec![]),
        );
        let bb0 = func.entry;
        let bb1 = func.create_block();
        let bb2 = func.create_block();

        let target = func.push_inst(MachInst::new(AArch64Opcode::MovI, vec![vreg(0), imm(42)]));
        func.append_inst(bb0, target);
        let br0 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb1)],
        ));
        func.append_inst(bb0, br0);

        let target_copy = func.push_inst(MachInst::new(
            AArch64Opcode::MovR,
            vec![MachOperand::PReg(X16), vreg(0)],
        ));
        func.append_inst(bb1, target_copy);
        let call = func.push_inst(MachInst::new(
            AArch64Opcode::Blr,
            vec![MachOperand::PReg(X16)],
        ));
        func.append_inst(bb1, call);
        let ret_copy = func.push_inst(MachInst::new(
            AArch64Opcode::Copy,
            vec![vreg(1), MachOperand::PReg(X0)],
        ));
        func.append_inst(bb1, ret_copy);
        let br1 = func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![MachOperand::Block(bb2), MachOperand::Block(bb1)],
        ));
        func.append_inst(bb1, br1);

        let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb2, ret);

        func.add_edge(bb0, bb1);
        func.add_edge(bb1, bb2);
        func.add_edge(bb1, bb1);

        let original_loop_insts = func.block(bb1).insts.clone();

        let mut licm = LoopInvariantCodeMotion;
        assert!(
            !licm.run(&mut func),
            "LICM must not move fixed-register call glue"
        );
        assert_eq!(func.block(bb1).insts, original_loop_insts);
    }

    #[test]
    fn test_licm_no_hoist_implicit_physical_register_dependency() {
        // Some pseudos model fixed-register dependencies through implicit
        // uses/defs rather than explicit operands. LICM must still treat them
        // as ordered machine state, not loop-invariant SSA values.
        static IMPLICIT_USES: &[trust_cg_ir::PReg] = &[X0];

        let mut func = MachFunction::new(
            "licm_implicit_preg".to_string(),
            Signature::new(vec![], vec![]),
        );
        let bb0 = func.entry;
        let bb1 = func.create_block();
        let bb2 = func.create_block();

        let m0 = func.push_inst(MachInst::new(AArch64Opcode::MovI, vec![vreg(0), imm(10)]));
        func.append_inst(bb0, m0);
        let m1 = func.push_inst(MachInst::new(AArch64Opcode::MovI, vec![vreg(1), imm(20)]));
        func.append_inst(bb0, m1);
        let br0 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb1)],
        ));
        func.append_inst(bb0, br0);

        let add = func.push_inst(
            MachInst::new(AArch64Opcode::AddRR, vec![vreg(2), vreg(0), vreg(1)])
                .with_implicit_uses(IMPLICIT_USES),
        );
        func.append_inst(bb1, add);
        let br1 = func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![MachOperand::Block(bb2), MachOperand::Block(bb1)],
        ));
        func.append_inst(bb1, br1);

        let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb2, ret);

        func.add_edge(bb0, bb1);
        func.add_edge(bb1, bb2);
        func.add_edge(bb1, bb1);

        let mut licm = LoopInvariantCodeMotion;
        assert!(
            !licm.run(&mut func),
            "LICM must not hoist implicit fixed-register dependencies"
        );
        assert_eq!(func.block(bb1).insts[0], add);
    }

    #[test]
    fn test_licm_no_hoist_movk_tied_def_use() {
        // MOVK preserves parts of its destination register. Operand 0 is both
        // a def and an implicit use, so treating the immediate operands as
        // loop-invariant and hoisting the instruction corrupts materialized
        // constants used by later call glue.
        let mut func = MachFunction::new(
            "licm_movk_tied_def_use".to_string(),
            Signature::new(vec![], vec![]),
        );
        let bb0 = func.entry;
        let bb1 = func.create_block();
        let bb2 = func.create_block();

        let br0 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb1)],
        ));
        func.append_inst(bb0, br0);

        let movk = func.push_inst(MachInst::new(
            AArch64Opcode::Movk,
            vec![vreg(1), imm(0x1234), imm(16)],
        ));
        func.append_inst(bb1, movk);
        let br1 = func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![MachOperand::Block(bb2), MachOperand::Block(bb1)],
        ));
        func.append_inst(bb1, br1);

        let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb2, ret);

        func.add_edge(bb0, bb1);
        func.add_edge(bb1, bb2);
        func.add_edge(bb1, bb1);

        let original_loop_insts = func.block(bb1).insts.clone();

        let mut licm = LoopInvariantCodeMotion;
        assert!(
            !licm.run(&mut func),
            "LICM must not hoist tied-def-use MOVK"
        );
        assert_eq!(func.block(bb1).insts, original_loop_insts);
    }

    /// Build a two-deep loop nest and populate the INNER loop body (bb3, depth
    /// 2, preheader bb2) via `fill_inner`. Shape:
    ///   bb0 -> bb1(outer hdr) -> bb2(inner ph) -> bb3(inner hdr/latch)
    ///   bb3 -{exit}-> bb4(outer latch) -> bb1 (back) | bb5(exit)
    /// Returns `(func, inner_preheader=bb2, inner_body=bb3)`.
    fn make_nested_loop(
        fill_inner: impl FnOnce(&mut MachFunction, BlockId),
    ) -> (MachFunction, BlockId, BlockId) {
        let mut func = MachFunction::new("licm_nested".to_string(), Signature::new(vec![], vec![]));
        let bb0 = func.entry;
        let bb1 = func.create_block();
        let bb2 = func.create_block();
        let bb3 = func.create_block();
        let bb4 = func.create_block();
        let bb5 = func.create_block();

        let b01 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb1)],
        ));
        func.append_inst(bb0, b01);
        let b12 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb2)],
        ));
        func.append_inst(bb1, b12);
        let b23 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb3)],
        ));
        func.append_inst(bb2, b23);

        // Inner loop body (caller-provided), then the inner back-edge branch.
        fill_inner(&mut func, bb3);
        let br_inner = func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![MachOperand::Block(bb4), MachOperand::Block(bb3)],
        ));
        func.append_inst(bb3, br_inner);

        // Outer latch: variant counter + back-edge branch.
        let osub = func.push_inst(MachInst::new(
            AArch64Opcode::SubRI,
            vec![vreg(6), vreg(6), imm(1)],
        ));
        func.append_inst(bb4, osub);
        let br_outer = func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![MachOperand::Block(bb5), MachOperand::Block(bb1)],
        ));
        func.append_inst(bb4, br_outer);

        let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb5, ret);

        func.add_edge(bb0, bb1);
        func.add_edge(bb1, bb2);
        func.add_edge(bb2, bb3);
        func.add_edge(bb3, bb4);
        func.add_edge(bb3, bb3);
        func.add_edge(bb4, bb1);
        func.add_edge(bb4, bb5);
        (func, bb2, bb3)
    }

    #[test]
    fn test_licm_hoists_constant_chain_and_consuming_fmov() {
        // The constant-chain tier: `MOVZ v1,#lo; MOVK v1,#hi,16; FMOV d(v2),x(v1)`
        // is the lowering of a non-encodable f64 literal. The MOVK is a tied
        // def-use and v1 is multiply-defined, so the per-instruction screen
        // rejects the chain — yet v1 holds one compile-time constant. In a nested
        // loop (the tier only fires for depth >= 2) the whole chain AND the
        // consuming FMOV must move to the inner preheader.
        let (mut func, inner_ph, inner_body) = make_nested_loop(|func, bb| {
            let movz = func.push_inst(MachInst::new(
                AArch64Opcode::Movz,
                vec![vreg(1), imm(0x1400)],
            ));
            func.append_inst(bb, movz);
            let movk = func.push_inst(MachInst::new(
                AArch64Opcode::Movk,
                vec![vreg(1), imm(0x3fe8), imm(16)],
            ));
            func.append_inst(bb, movk);
            let fmov = func.push_inst(MachInst::new(
                AArch64Opcode::FmovGprFpr,
                vec![vreg_class(2, RegClass::Fpr64), vreg(1)],
            ));
            func.append_inst(bb, fmov);
            // Loop-variant accumulate consuming the constant (keeps v2 live).
            let acc = func.push_inst(MachInst::new(
                AArch64Opcode::FaddRR,
                vec![
                    vreg_class(3, RegClass::Fpr64),
                    vreg_class(3, RegClass::Fpr64),
                    vreg_class(2, RegClass::Fpr64),
                ],
            ));
            func.append_inst(bb, acc);
            let sub = func.push_inst(MachInst::new(
                AArch64Opcode::SubRI,
                vec![vreg(5), vreg(5), imm(1)],
            ));
            func.append_inst(bb, sub);
        });

        let mut licm = LoopInvariantCodeMotion;
        assert!(licm.run(&mut func), "constant chain + FMOV must hoist");

        // Inner body keeps only the variant accumulate, counter, and branch.
        let body_ops: Vec<_> = func
            .block(inner_body)
            .insts
            .iter()
            .map(|&id| func.inst(id).opcode)
            .collect();
        assert_eq!(
            body_ops,
            vec![
                AArch64Opcode::FaddRR,
                AArch64Opcode::SubRI,
                AArch64Opcode::BCond
            ],
            "MOVZ/MOVK/FMOV must all leave the inner loop body"
        );

        // Inner preheader holds the chain in order (MOVZ, MOVK, FMOV) before its B.
        let ph_ops: Vec<_> = func
            .block(inner_ph)
            .insts
            .iter()
            .map(|&id| func.inst(id).opcode)
            .collect();
        assert_eq!(
            ph_ops,
            vec![
                AArch64Opcode::Movz,
                AArch64Opcode::Movk,
                AArch64Opcode::FmovGprFpr,
                AArch64Opcode::B
            ],
            "chain must land in the inner preheader in materialization order, before the branch"
        );
    }

    #[test]
    fn test_licm_no_hoist_two_head_constant_chain() {
        // Two MOVZ heads targeting the same vreg means the value is NOT a single
        // compile-time constant (it depends on which def is live), so the
        // constant-chain tier must refuse it even in a nested loop. The consuming
        // FMOV therefore also stays in the loop (its source is not invariant).
        let (mut func, _inner_ph, inner_body) = make_nested_loop(|func, bb| {
            let movz_a = func.push_inst(MachInst::new(
                AArch64Opcode::Movz,
                vec![vreg(1), imm(0x1000)],
            ));
            func.append_inst(bb, movz_a);
            let movz_b = func.push_inst(MachInst::new(
                AArch64Opcode::Movz,
                vec![vreg(1), imm(0x2000)],
            ));
            func.append_inst(bb, movz_b);
            let fmov = func.push_inst(MachInst::new(
                AArch64Opcode::FmovGprFpr,
                vec![vreg_class(2, RegClass::Fpr64), vreg(1)],
            ));
            func.append_inst(bb, fmov);
            let sub = func.push_inst(MachInst::new(
                AArch64Opcode::SubRI,
                vec![vreg(5), vreg(5), imm(1)],
            ));
            func.append_inst(bb, sub);
        });

        let original = func.block(inner_body).insts.clone();
        let mut licm = LoopInvariantCodeMotion;
        licm.run(&mut func);
        assert_eq!(
            func.block(inner_body).insts,
            original,
            "two-head (ambiguous) constant must not hoist"
        );
    }

    #[test]
    fn test_licm_no_hoist_constant_chain_in_single_loop() {
        // Depth gate: a constant chain in a NON-nested (depth-1) loop is left in
        // place. The tier only relocates chains out of nested loops, where the
        // recompute savings dominate; the depth-1→0 pull-out shrinks a single hot
        // loop's body and can retune its fetch alignment for no benefit.
        let mut func = MachFunction::new(
            "licm_single_loop_chain".to_string(),
            Signature::new(vec![], vec![]),
        );
        let bb0 = func.entry;
        let bb1 = func.create_block();
        let bb2 = func.create_block();

        let br0 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb1)],
        ));
        func.append_inst(bb0, br0);

        let movz = func.push_inst(MachInst::new(
            AArch64Opcode::Movz,
            vec![vreg(1), imm(0x1400)],
        ));
        func.append_inst(bb1, movz);
        let movk = func.push_inst(MachInst::new(
            AArch64Opcode::Movk,
            vec![vreg(1), imm(0x3fe8), imm(16)],
        ));
        func.append_inst(bb1, movk);
        let fmov = func.push_inst(MachInst::new(
            AArch64Opcode::FmovGprFpr,
            vec![vreg_class(2, RegClass::Fpr64), vreg(1)],
        ));
        func.append_inst(bb1, fmov);
        let sub = func.push_inst(MachInst::new(
            AArch64Opcode::SubRI,
            vec![vreg(4), vreg(4), imm(1)],
        ));
        func.append_inst(bb1, sub);
        let br1 = func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![MachOperand::Block(bb2), MachOperand::Block(bb1)],
        ));
        func.append_inst(bb1, br1);

        let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb2, ret);

        func.add_edge(bb0, bb1);
        func.add_edge(bb1, bb2);
        func.add_edge(bb1, bb1);

        let original = func.block(bb1).insts.clone();
        let mut licm = LoopInvariantCodeMotion;
        licm.run(&mut func);
        assert_eq!(
            func.block(bb1).insts,
            original,
            "depth-1 loop constant chain must stay in place (depth gate)"
        );
    }

    #[test]
    fn test_licm_hoists_int_constant_chain_multi_def() {
        // The integer widening of the constant-chain tier: `MOVN v1,#lo;
        // MOVK v1,#hi,16` is the srem/sdiv magic-reciprocal materialization
        // (ReedSolomon's `% 255` -> 0x…80808081). No FMOV consumes the
        // carrier — the consumer is an ordinary MUL — but the multi-def chain
        // is still one compile-time constant, so in a nested loop it must move
        // to the inner preheader as a unit. The MUL reads the loop counter, so
        // it must STAY in the body.
        let (mut func, inner_ph, inner_body) = make_nested_loop(|func, bb| {
            let movn = func.push_inst(MachInst::new(
                AArch64Opcode::Movn,
                vec![vreg(1), imm(0x7f7e)],
            ));
            func.append_inst(bb, movn);
            let movk = func.push_inst(MachInst::new(
                AArch64Opcode::Movk,
                vec![vreg(1), imm(0x8080), imm(16)],
            ));
            func.append_inst(bb, movk);
            // Loop-variant multiply consuming the constant (v5 is the inner
            // counter, redefined below — not invariant).
            let mul = func.push_inst(MachInst::new(
                AArch64Opcode::MulRR,
                vec![vreg(2), vreg(5), vreg(1)],
            ));
            func.append_inst(bb, mul);
            let sub = func.push_inst(MachInst::new(
                AArch64Opcode::SubRI,
                vec![vreg(5), vreg(5), imm(1)],
            ));
            func.append_inst(bb, sub);
        });

        let mut licm = LoopInvariantCodeMotion;
        assert!(licm.run(&mut func), "integer constant chain must hoist");

        let body_ops: Vec<_> = func
            .block(inner_body)
            .insts
            .iter()
            .map(|&id| func.inst(id).opcode)
            .collect();
        assert_eq!(
            body_ops,
            vec![
                AArch64Opcode::MulRR,
                AArch64Opcode::SubRI,
                AArch64Opcode::BCond
            ],
            "MOVN/MOVK must leave the inner loop body; the variant MUL must stay"
        );

        let ph_ops: Vec<_> = func
            .block(inner_ph)
            .insts
            .iter()
            .map(|&id| func.inst(id).opcode)
            .collect();
        assert_eq!(
            ph_ops,
            vec![AArch64Opcode::Movn, AArch64Opcode::Movk, AArch64Opcode::B],
            "chain must land in the inner preheader in materialization order"
        );
    }

    #[test]
    fn test_licm_no_hoist_two_head_int_constant_chain() {
        // Two MOVZ heads on the same carrier with no FMOV consumer: the
        // integer class passes the >=2-defs length gate, but the shape check
        // (exactly one head, the rest MOVK) must still refuse it — the value
        // depends on which def is live, not a single compile-time constant.
        let (mut func, _inner_ph, inner_body) = make_nested_loop(|func, bb| {
            let movz_a = func.push_inst(MachInst::new(
                AArch64Opcode::Movz,
                vec![vreg(1), imm(0x1000)],
            ));
            func.append_inst(bb, movz_a);
            let movz_b = func.push_inst(MachInst::new(
                AArch64Opcode::Movz,
                vec![vreg(1), imm(0x2000)],
            ));
            func.append_inst(bb, movz_b);
            let mul = func.push_inst(MachInst::new(
                AArch64Opcode::MulRR,
                vec![vreg(2), vreg(5), vreg(1)],
            ));
            func.append_inst(bb, mul);
            let sub = func.push_inst(MachInst::new(
                AArch64Opcode::SubRI,
                vec![vreg(5), vreg(5), imm(1)],
            ));
            func.append_inst(bb, sub);
        });

        let original = func.block(inner_body).insts.clone();
        let mut licm = LoopInvariantCodeMotion;
        licm.run(&mut func);
        assert_eq!(
            func.block(inner_body).insts,
            original,
            "two-head (ambiguous) integer constant must not hoist"
        );
    }

    #[test]
    fn test_licm_no_hoist_bfm_tied_def_use() {
        // BFM also reads its destination register as an implicit source.
        let mut func = MachFunction::new(
            "licm_bfm_tied_def_use".to_string(),
            Signature::new(vec![], vec![]),
        );
        let bb0 = func.entry;
        let bb1 = func.create_block();
        let bb2 = func.create_block();

        let src = func.push_inst(MachInst::new(AArch64Opcode::MovI, vec![vreg(0), imm(42)]));
        func.append_inst(bb0, src);
        let br0 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb1)],
        ));
        func.append_inst(bb0, br0);

        let bfm = func.push_inst(MachInst::new(
            AArch64Opcode::Bfm,
            vec![vreg(1), vreg(0), imm(0), imm(15)],
        ));
        func.append_inst(bb1, bfm);
        let br1 = func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![MachOperand::Block(bb2), MachOperand::Block(bb1)],
        ));
        func.append_inst(bb1, br1);

        let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb2, ret);

        func.add_edge(bb0, bb1);
        func.add_edge(bb1, bb2);
        func.add_edge(bb1, bb1);

        let original_loop_insts = func.block(bb1).insts.clone();

        let mut licm = LoopInvariantCodeMotion;
        assert!(!licm.run(&mut func), "LICM must not hoist tied-def-use BFM");
        assert_eq!(func.block(bb1).insts, original_loop_insts);
    }

    #[test]
    fn test_licm_hoists_symbol_address_materialization() {
        // Relocation-bearing address materialization (Adrp + AddPCRel) IS a
        // loop-invariant, pure, non-trapping link-time constant, so LICM now
        // hoists it to the preheader.
        //
        // Soundness (the proof the old exclusion asked for): the PAGE21 and
        // PAGEOFF12 relocations are re-resolved by the linker for the
        // instruction's FINAL PC, so the computed address is independent of
        // where the instruction lands; moving it is encoding-safe. Adrp /
        // AddPCRel adjacency on Mach-O only enables OPTIONAL ld64 relaxation
        // (fold to a single ADR when in range), never correctness, so
        // separating them across the preheader boundary is fine. Both are pure
        // and non-trapping, so preheader speculation is safe.
        //
        // This is the Bubblesort inner-loop win: two loop-invariant adrp+add
        // pairs computing a global's address now leave the 12.5M-iteration
        // inner loop entirely.
        let mut func = MachFunction::new(
            "licm_symbol_address".to_string(),
            Signature::new(vec![], vec![]),
        );
        let bb0 = func.entry;
        let bb1 = func.create_block();
        let bb2 = func.create_block();

        let br0 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb1)],
        ));
        func.append_inst(bb0, br0);

        let adrp = func.push_inst(MachInst::new(
            AArch64Opcode::Adrp,
            vec![vreg(1), MachOperand::Symbol("g".to_string())],
        ));
        func.append_inst(bb1, adrp);
        let add = func.push_inst(MachInst::new(
            AArch64Opcode::AddPCRel,
            vec![vreg(2), vreg(1), MachOperand::Symbol("g".to_string())],
        ));
        func.append_inst(bb1, add);
        let br1 = func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![MachOperand::Block(bb2), MachOperand::Block(bb1)],
        ));
        func.append_inst(bb1, br1);

        let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb2, ret);

        func.add_edge(bb0, bb1);
        func.add_edge(bb1, bb2);
        func.add_edge(bb1, bb1);

        let mut licm = LoopInvariantCodeMotion;
        assert!(
            licm.run(&mut func),
            "LICM must hoist loop-invariant relocation address materialization"
        );

        // Both the Adrp and the AddPCRel left the loop body...
        assert!(!func.block(bb1).insts.contains(&adrp));
        assert!(!func.block(bb1).insts.contains(&add));
        // ...and now live in the preheader.
        assert!(func.block(bb0).insts.contains(&adrp));
        assert!(func.block(bb0).insts.contains(&add));
        // bb1 retains only its conditional branch.
        assert_eq!(func.block(bb1).insts.len(), 1);
        // Dependency order preserved: Adrp precedes the AddPCRel that reads it.
        let ph = &func.block(bb0).insts;
        let adrp_pos = ph.iter().position(|&id| id == adrp).unwrap();
        let add_pos = ph.iter().position(|&id| id == add).unwrap();
        assert!(
            adrp_pos < add_pos,
            "hoisted Adrp must precede its dependent AddPCRel"
        );
    }

    #[test]
    fn test_licm_no_hoist_multi_def_symbol_address() {
        // The single-def guard is the multi-def protection that survives the
        // Adrp/AddPCRel hoist enablement. A call target (or global) whose
        // address vreg is materialized on two paths reuses the same VReg id in
        // non-SSA machine IR; LICM tracks invariance by VReg id, so a multi-def
        // address vreg must NOT hoist even though the opcode is now eligible.
        let mut func = MachFunction::new(
            "licm_multi_def_symbol_address".to_string(),
            Signature::new(vec![], vec![]),
        );
        let bb0 = func.entry;
        let bb1 = func.create_block();
        let bb2 = func.create_block();

        let br0 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb1)],
        ));
        func.append_inst(bb0, br0);

        // v1 defined twice inside the loop (multi-def) -> not SSA, not hoistable.
        let adrp_a = func.push_inst(MachInst::new(
            AArch64Opcode::Adrp,
            vec![vreg(1), MachOperand::Symbol("callee".to_string())],
        ));
        func.append_inst(bb1, adrp_a);
        let adrp_b = func.push_inst(MachInst::new(
            AArch64Opcode::Adrp,
            vec![vreg(1), MachOperand::Symbol("callee".to_string())],
        ));
        func.append_inst(bb1, adrp_b);
        let br1 = func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![MachOperand::Block(bb2), MachOperand::Block(bb1)],
        ));
        func.append_inst(bb1, br1);

        let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb2, ret);

        func.add_edge(bb0, bb1);
        func.add_edge(bb1, bb2);
        func.add_edge(bb1, bb1);

        let original_loop_insts = func.block(bb1).insts.clone();

        let mut licm = LoopInvariantCodeMotion;
        assert!(
            !licm.run(&mut func),
            "LICM must not hoist a multi-def address vreg"
        );
        assert_eq!(func.block(bb1).insts, original_loop_insts);
    }

    #[test]
    fn test_licm_no_hoist_trapping_division() {
        // SDiv/UDiv are memory-pure but can trap. Hoisting them before loop
        // guards can make a conditional trap unconditional.
        let mut func = MachFunction::new(
            "licm_trapping_division".to_string(),
            Signature::new(vec![], vec![]),
        );
        let bb0 = func.entry;
        let bb1 = func.create_block();
        let bb2 = func.create_block();

        let numerator = func.push_inst(MachInst::new(AArch64Opcode::MovI, vec![vreg(0), imm(100)]));
        func.append_inst(bb0, numerator);
        let denominator = func.push_inst(MachInst::new(AArch64Opcode::MovI, vec![vreg(1), imm(5)]));
        func.append_inst(bb0, denominator);
        let br0 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb1)],
        ));
        func.append_inst(bb0, br0);

        let div = func.push_inst(MachInst::new(
            AArch64Opcode::SDiv,
            vec![vreg(2), vreg(0), vreg(1)],
        ));
        func.append_inst(bb1, div);
        let br1 = func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![MachOperand::Block(bb2), MachOperand::Block(bb1)],
        ));
        func.append_inst(bb1, br1);

        let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb2, ret);

        func.add_edge(bb0, bb1);
        func.add_edge(bb1, bb2);
        func.add_edge(bb1, bb1);

        let original_loop_insts = func.block(bb1).insts.clone();

        let mut licm = LoopInvariantCodeMotion;
        assert!(
            !licm.run(&mut func),
            "LICM must not hoist trapping integer division"
        );
        assert_eq!(func.block(bb1).insts, original_loop_insts);
    }

    #[test]
    fn test_licm_no_hoist_multi_def_vreg() {
        // Machine IR can reuse the same VReg id for path/block-argument
        // carrier values. LICM tracks invariance by VReg id, so it must not
        // move instructions defining a non-SSA VReg.
        let mut func = MachFunction::new(
            "licm_multi_def_vreg".to_string(),
            Signature::new(vec![], vec![]),
        );
        let bb0 = func.entry;
        let bb1 = func.create_block();
        let bb2 = func.create_block();

        let left = func.push_inst(MachInst::new(AArch64Opcode::MovI, vec![vreg(0), imm(10)]));
        func.append_inst(bb0, left);
        let right = func.push_inst(MachInst::new(AArch64Opcode::MovI, vec![vreg(2), imm(20)]));
        func.append_inst(bb0, right);
        let br0 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb1)],
        ));
        func.append_inst(bb0, br0);

        let first_def = func.push_inst(MachInst::new(AArch64Opcode::MovR, vec![vreg(1), vreg(0)]));
        func.append_inst(bb1, first_def);
        let second_def = func.push_inst(MachInst::new(AArch64Opcode::MovR, vec![vreg(1), vreg(2)]));
        func.append_inst(bb1, second_def);
        let br1 = func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![MachOperand::Block(bb2), MachOperand::Block(bb1)],
        ));
        func.append_inst(bb1, br1);

        let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb2, ret);

        func.add_edge(bb0, bb1);
        func.add_edge(bb1, bb2);
        func.add_edge(bb1, bb1);

        let original_loop_insts = func.block(bb1).insts.clone();

        let mut licm = LoopInvariantCodeMotion;
        assert!(
            !licm.run(&mut func),
            "LICM must not hoist non-SSA VReg definitions"
        );
        assert_eq!(func.block(bb1).insts, original_loop_insts);
    }

    #[test]
    fn test_licm_skips_loop_without_natural_preheader() {
        // Header bb2 has two non-loop predecessors (bb0, bb1) plus a latch (bb4),
        // so the loop has no natural preheader. LICM used to synthesize one
        // eagerly, which mutates CFG/Phi structure before proving any hoist is
        // legal. For sparse-substitute-style block-param loops, that is not safe.
        let mut func = MachFunction::new(
            "licm_no_natural_preheader".to_string(),
            Signature::new(vec![], vec![]),
        );
        let bb0 = func.entry;
        let bb1 = func.create_block();
        let bb2 = func.create_block(); // header
        let bb3 = func.create_block(); // exit
        let bb4 = func.create_block(); // latch

        let init0 = func.push_inst(MachInst::new(AArch64Opcode::MovI, vec![vreg(0), imm(0)]));
        func.append_inst(bb0, init0);
        let br0 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb2)],
        ));
        func.append_inst(bb0, br0);

        let init1 = func.push_inst(MachInst::new(AArch64Opcode::MovI, vec![vreg(1), imm(1)]));
        func.append_inst(bb1, init1);
        let br1 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb2)],
        ));
        func.append_inst(bb1, br1);

        let phi = func.push_inst(MachInst::new(
            AArch64Opcode::Phi,
            vec![
                vreg(2),
                vreg(0),
                MachOperand::Block(bb0),
                vreg(1),
                MachOperand::Block(bb1),
                vreg(4),
                MachOperand::Block(bb4),
            ],
        ));
        func.append_inst(bb2, phi);
        let inv = func.push_inst(MachInst::new(AArch64Opcode::MovI, vec![vreg(3), imm(42)]));
        func.append_inst(bb2, inv);
        let cmp = func.push_inst(MachInst::new(AArch64Opcode::CmpRI, vec![vreg(2), imm(10)]));
        func.append_inst(bb2, cmp);
        let br2 = func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![MachOperand::Block(bb3), MachOperand::Block(bb4)],
        ));
        func.append_inst(bb2, br2);

        let inc = func.push_inst(MachInst::new(
            AArch64Opcode::AddRI,
            vec![vreg(4), vreg(2), imm(1)],
        ));
        func.append_inst(bb4, inc);
        let br4 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb2)],
        ));
        func.append_inst(bb4, br4);

        let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb3, ret);

        func.add_edge(bb0, bb2);
        func.add_edge(bb1, bb2);
        func.add_edge(bb2, bb3);
        func.add_edge(bb2, bb4);
        func.add_edge(bb4, bb2);

        let orig_block_order = func.block_order.clone();
        let orig_header_preds = func.block(bb2).preds.clone();
        let orig_header_insts = func.block(bb2).insts.clone();

        let mut licm = LoopInvariantCodeMotion;
        assert!(
            !licm.run(&mut func),
            "LICM must skip loops without a natural preheader"
        );
        assert_eq!(
            func.block_order, orig_block_order,
            "LICM must not create a synthetic preheader here"
        );
        assert_eq!(
            func.block(bb2).preds,
            orig_header_preds,
            "LICM must not rewrite header predecessors"
        );
        assert_eq!(
            func.block(bb2).insts,
            orig_header_insts,
            "LICM must not hoist out of a loop without a natural preheader"
        );
    }

    #[test]
    fn test_licm_declines_stale_in_loop_preheader_metadata() {
        // Defense-in-depth tooth for the multi-latch analysis bug: bb0 has a
        // self-edge and bb1 is another latch.  A stale partial-body analysis
        // could label bb1 as bb0's preheader even though the final loop body is
        // {bb0, bb1}.  Hoisting `v0 = 0` into bb1 would put it after bb1's
        // existing `CmpRI v0`, which X5 correctly rejects.  Admission must
        // decline before mutating instead.
        let mut func = MachFunction::new(
            "licm_stale_in_loop_preheader".to_string(),
            Signature::new(vec![], vec![]),
        );
        let bb0 = func.entry;
        let bb1 = func.create_block();

        let invariant = func.push_inst(MachInst::new(AArch64Opcode::MovI, vec![vreg(0), imm(0)]));
        func.append_inst(bb0, invariant);
        let split = func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![MachOperand::Block(bb0), MachOperand::Block(bb1)],
        ));
        func.append_inst(bb0, split);

        let use_before_candidate =
            func.push_inst(MachInst::new(AArch64Opcode::CmpRI, vec![vreg(0), imm(0)]));
        func.append_inst(bb1, use_before_candidate);
        let latch = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb0)],
        ));
        func.append_inst(bb1, latch);

        func.add_edge(bb0, bb0);
        func.add_edge(bb0, bb1);
        func.add_edge(bb1, bb0);

        let stale = NaturalLoop {
            header: bb0,
            latch: bb1,
            body: HashSet::from([bb0, bb1]),
            preheader: Some(bb1),
            depth: 1,
            parent: None,
        };
        let dom = DomTree::compute(&func);
        // The whole-function maps are now built by the caller, once per scan.
        let def_counts = build_def_counts(&func);
        let def_map = build_def_map(&func);

        assert!(
            !hoist_loop_invariants(&mut func, &stale, &dom, &def_counts, &def_map),
            "an in-loop preheader candidate must fail closed before the splice"
        );
        assert!(func.block(bb0).insts.contains(&invariant));
        assert_eq!(
            func.block(bb1).insts,
            vec![use_before_candidate, latch],
            "declining must leave the candidate block byte-for-byte ordered"
        );
    }

    // =====================================================================
    // Load hoisting (LICM tiers a + b)
    // =====================================================================

    fn sym(name: &str) -> MachOperand {
        MachOperand::Symbol(name.to_string())
    }

    fn sp() -> MachOperand {
        MachOperand::Special(SpecialReg::SP)
    }

    /// Build the canonical single-block-loop skeleton used by the load tests:
    ///
    /// ```text
    ///   bb0 (preheader, succs = [bb1])
    ///     <setup...>
    ///     b bb1
    ///   bb1 (header == latch) <--+
    ///     <body...>              |
    ///     bcond bb2, bb1  -------+
    ///   bb2 (exit): ret
    /// ```
    ///
    /// The preheader unconditionally enters the loop and the single body block
    /// dominates both the latch and the (bb1) exiting block, so a store-free
    /// invariant load in bb1 satisfies the speculation guard.
    fn single_block_loop() -> (MachFunction, BlockId, BlockId, BlockId) {
        let mut func = MachFunction::new("licm_load".to_string(), Signature::new(vec![], vec![]));
        let bb0 = func.entry;
        let bb1 = func.create_block();
        let bb2 = func.create_block();
        func.add_edge(bb0, bb1);
        func.add_edge(bb1, bb2);
        func.add_edge(bb1, bb1);
        (func, bb0, bb1, bb2)
    }

    fn append(
        func: &mut MachFunction,
        block: BlockId,
        opcode: AArch64Opcode,
        ops: Vec<MachOperand>,
    ) -> InstId {
        let id = func.push_inst(MachInst::new(opcode, ops));
        func.append_inst(block, id);
        id
    }

    fn finish_preheader_branch(func: &mut MachFunction, bb0: BlockId, bb1: BlockId) {
        append(func, bb0, AArch64Opcode::B, vec![MachOperand::Block(bb1)]);
    }

    fn finish_loop_tail(func: &mut MachFunction, bb1: BlockId, bb2: BlockId) {
        // A variant carrier keeps the loop honest, then the conditional back-edge.
        append(
            func,
            bb1,
            AArch64Opcode::SubRI,
            vec![vreg(8), vreg(8), imm(1)],
        );
        append(
            func,
            bb1,
            AArch64Opcode::BCond,
            vec![MachOperand::Block(bb2), MachOperand::Block(bb1)],
        );
        append(func, bb2, AArch64Opcode::Ret, vec![]);
    }

    #[test]
    fn test_licm_hoists_invariant_load_store_free() {
        // Tier (a): a store-free / call-free loop cannot clobber an invariant
        // address, so a guaranteed-to-execute invariant load hoists.
        let (mut func, bb0, bb1, bb2) = single_block_loop();
        append(
            &mut func,
            bb0,
            AArch64Opcode::MovI,
            vec![vreg(0), imm(4096)],
        );
        finish_preheader_branch(&mut func, bb0, bb1);
        let load = append(
            &mut func,
            bb1,
            AArch64Opcode::LdrRI,
            vec![vreg(1), vreg(0), imm(0)],
        );
        finish_loop_tail(&mut func, bb1, bb2);

        let mut licm = LoopInvariantCodeMotion;
        assert!(licm.run(&mut func), "store-free invariant load must hoist");
        assert!(func.block(bb0).insts.contains(&load));
        assert!(!func.block(bb1).insts.contains(&load));
    }

    #[test]
    fn test_licm_no_hoist_load_in_store_loop_unprovable() {
        // Tier (a) boundary: the loop now contains a store. The load's base is
        // an unclassifiable pointer, so tier (b) cannot prove disjointness and
        // the load stays put.
        let (mut func, bb0, bb1, bb2) = single_block_loop();
        append(
            &mut func,
            bb0,
            AArch64Opcode::MovI,
            vec![vreg(0), imm(4096)],
        ); // load base
        append(
            &mut func,
            bb0,
            AArch64Opcode::MovI,
            vec![vreg(5), imm(8192)],
        ); // store base
        append(&mut func, bb0, AArch64Opcode::MovI, vec![vreg(6), imm(7)]); // store value
        finish_preheader_branch(&mut func, bb0, bb1);
        let load = append(
            &mut func,
            bb1,
            AArch64Opcode::LdrRI,
            vec![vreg(1), vreg(0), imm(0)],
        );
        append(
            &mut func,
            bb1,
            AArch64Opcode::StrRI,
            vec![vreg(6), vreg(5), imm(0)],
        );
        finish_loop_tail(&mut func, bb1, bb2);

        let mut licm = LoopInvariantCodeMotion;
        // Nothing hoistable (the load refuses, the sub is variant).
        assert!(!licm.run(&mut func));
        assert!(func.block(bb1).insts.contains(&load));
    }

    #[test]
    fn test_licm_no_hoist_writeback_load() {
        // LdrPostIndex redefines its base register (writeback) — never hoisted.
        let (mut func, bb0, bb1, bb2) = single_block_loop();
        append(
            &mut func,
            bb0,
            AArch64Opcode::MovI,
            vec![vreg(0), imm(4096)],
        );
        finish_preheader_branch(&mut func, bb0, bb1);
        let load = append(
            &mut func,
            bb1,
            AArch64Opcode::LdrPostIndex,
            vec![vreg(1), vreg(0), imm(8)],
        );
        finish_loop_tail(&mut func, bb1, bb2);

        let mut licm = LoopInvariantCodeMotion;
        assert!(!licm.run(&mut func));
        assert!(func.block(bb1).insts.contains(&load));
    }

    #[test]
    fn test_licm_no_hoist_acquire_load() {
        // Ldar (load-acquire) carries ordering semantics — never hoisted.
        let (mut func, bb0, bb1, bb2) = single_block_loop();
        append(
            &mut func,
            bb0,
            AArch64Opcode::MovI,
            vec![vreg(0), imm(4096)],
        );
        finish_preheader_branch(&mut func, bb0, bb1);
        let load = append(&mut func, bb1, AArch64Opcode::Ldar, vec![vreg(1), vreg(0)]);
        finish_loop_tail(&mut func, bb1, bb2);

        let mut licm = LoopInvariantCodeMotion;
        assert!(!licm.run(&mut func));
        assert!(func.block(bb1).insts.contains(&load));
    }

    #[test]
    fn test_licm_load_speculation_guard_conditional_block() {
        // Early-exit shape: the load sits in a body block that does NOT dominate
        // the (header) exiting block, so it is not guaranteed to execute and the
        // speculation guard refuses it even though the loop is store-free.
        //
        //   bb0 -> bb1 (header, exits to bb3) -> bb2 (body/latch) -> bb1
        let mut func =
            MachFunction::new("licm_spec_cond".to_string(), Signature::new(vec![], vec![]));
        let bb0 = func.entry;
        let bb1 = func.create_block();
        let bb2 = func.create_block();
        let bb3 = func.create_block();

        append(
            &mut func,
            bb0,
            AArch64Opcode::MovI,
            vec![vreg(0), imm(4096)],
        );
        append(
            &mut func,
            bb0,
            AArch64Opcode::B,
            vec![MachOperand::Block(bb1)],
        );
        append(
            &mut func,
            bb1,
            AArch64Opcode::BCond,
            vec![MachOperand::Block(bb3), MachOperand::Block(bb2)],
        );
        let load = append(
            &mut func,
            bb2,
            AArch64Opcode::LdrRI,
            vec![vreg(1), vreg(0), imm(0)],
        );
        append(
            &mut func,
            bb2,
            AArch64Opcode::B,
            vec![MachOperand::Block(bb1)],
        );
        append(&mut func, bb3, AArch64Opcode::Ret, vec![]);

        func.add_edge(bb0, bb1);
        func.add_edge(bb1, bb3);
        func.add_edge(bb1, bb2);
        func.add_edge(bb2, bb1);

        let mut licm = LoopInvariantCodeMotion;
        assert!(!licm.run(&mut func), "non-dominating load must not hoist");
        assert!(func.block(bb2).insts.contains(&load));
    }

    #[test]
    fn test_licm_load_speculation_guard_zero_trip_guard_preheader() {
        // Zero-trip shape: the natural preheader is a guard that branches
        // header/exit, so reaching it does NOT imply the loop runs. Hoisting the
        // load into it could fault on the loop-skipped path — refuse.
        //
        //   bb0 (guard/preheader: bcond exit, header) -> bb1 (header==latch)
        let mut func =
            MachFunction::new("licm_zero_trip".to_string(), Signature::new(vec![], vec![]));
        let bb0 = func.entry;
        let bb1 = func.create_block();
        let bb2 = func.create_block();

        append(
            &mut func,
            bb0,
            AArch64Opcode::MovI,
            vec![vreg(0), imm(4096)],
        );
        append(
            &mut func,
            bb0,
            AArch64Opcode::BCond,
            vec![MachOperand::Block(bb2), MachOperand::Block(bb1)],
        );
        let load = append(
            &mut func,
            bb1,
            AArch64Opcode::LdrRI,
            vec![vreg(1), vreg(0), imm(0)],
        );
        append(
            &mut func,
            bb1,
            AArch64Opcode::BCond,
            vec![MachOperand::Block(bb2), MachOperand::Block(bb1)],
        );
        append(&mut func, bb2, AArch64Opcode::Ret, vec![]);

        func.add_edge(bb0, bb1);
        func.add_edge(bb0, bb2);
        func.add_edge(bb1, bb1);
        func.add_edge(bb1, bb2);

        let mut licm = LoopInvariantCodeMotion;
        assert!(
            !licm.run(&mut func),
            "zero-trip guard preheader must block load"
        );
        assert!(func.block(bb1).insts.contains(&load));
    }

    /// Tier-(b) helper: single-block loop whose preheader materializes a global
    /// symbol address `&<name>` in `dst` (via Adrp + AddPCRel).
    fn materialize_global(func: &mut MachFunction, bb0: BlockId, page: u32, dst: u32, name: &str) {
        append(func, bb0, AArch64Opcode::Adrp, vec![vreg(page), sym(name)]);
        append(
            func,
            bb0,
            AArch64Opcode::AddPCRel,
            vec![vreg(dst), vreg(page), sym(name)],
        );
    }

    /// Tier-(b) helper: materialize a stack-slot address `&ss<slot>` in `dst`.
    fn materialize_slot(func: &mut MachFunction, bb0: BlockId, dst: u32, slot: u32) {
        append(
            func,
            bb0,
            AArch64Opcode::AddPCRel,
            vec![vreg(dst), sp(), MachOperand::StackSlot(StackSlotId(slot))],
        );
    }

    #[test]
    fn test_licm_tier_b_distinct_global_hoists() {
        // Load &gA, store &gB, gA != gB: distinct link-time objects, disjoint.
        let (mut func, bb0, bb1, bb2) = single_block_loop();
        materialize_global(&mut func, bb0, 0, 1, "gA"); // v1 = &gA
        materialize_global(&mut func, bb0, 2, 3, "gB"); // v3 = &gB
        append(&mut func, bb0, AArch64Opcode::MovI, vec![vreg(9), imm(7)]);
        finish_preheader_branch(&mut func, bb0, bb1);
        let load = append(
            &mut func,
            bb1,
            AArch64Opcode::LdrRI,
            vec![vreg(4), vreg(1), imm(0)],
        );
        append(
            &mut func,
            bb1,
            AArch64Opcode::StrRI,
            vec![vreg(9), vreg(3), imm(0)],
        );
        finish_loop_tail(&mut func, bb1, bb2);

        let mut licm = LoopInvariantCodeMotion;
        assert!(
            licm.run(&mut func),
            "load from a global disjoint from the store must hoist"
        );
        assert!(func.block(bb0).insts.contains(&load));
        assert!(!func.block(bb1).insts.contains(&load));
    }

    #[test]
    fn test_licm_tier_b_same_global_refuses() {
        // Load and store both target &gA: cannot prove disjoint — refuse.
        let (mut func, bb0, bb1, bb2) = single_block_loop();
        materialize_global(&mut func, bb0, 0, 1, "gA"); // v1 = &gA
        append(&mut func, bb0, AArch64Opcode::MovI, vec![vreg(9), imm(7)]);
        finish_preheader_branch(&mut func, bb0, bb1);
        let load = append(
            &mut func,
            bb1,
            AArch64Opcode::LdrRI,
            vec![vreg(4), vreg(1), imm(0)],
        );
        append(
            &mut func,
            bb1,
            AArch64Opcode::StrRI,
            vec![vreg(9), vreg(1), imm(0)],
        );
        finish_loop_tail(&mut func, bb1, bb2);

        let mut licm = LoopInvariantCodeMotion;
        assert!(
            !licm.run(&mut func),
            "same-symbol load/store must not hoist"
        );
        assert!(func.block(bb1).insts.contains(&load));
    }

    #[test]
    fn test_licm_tier_b_distinct_stack_slot_hoists() {
        // Load ss0, store ss1: distinct frame allocations, disjoint.
        let (mut func, bb0, bb1, bb2) = single_block_loop();
        materialize_slot(&mut func, bb0, 0, 0); // v0 = &ss0
        materialize_slot(&mut func, bb0, 1, 1); // v1 = &ss1
        append(&mut func, bb0, AArch64Opcode::MovI, vec![vreg(9), imm(7)]);
        finish_preheader_branch(&mut func, bb0, bb1);
        let load = append(
            &mut func,
            bb1,
            AArch64Opcode::LdrRI,
            vec![vreg(4), vreg(0), imm(0)],
        );
        append(
            &mut func,
            bb1,
            AArch64Opcode::StrRI,
            vec![vreg(9), vreg(1), imm(0)],
        );
        finish_loop_tail(&mut func, bb1, bb2);

        let mut licm = LoopInvariantCodeMotion;
        assert!(
            licm.run(&mut func),
            "load/store to distinct stack slots must hoist"
        );
        assert!(func.block(bb0).insts.contains(&load));
        assert!(!func.block(bb1).insts.contains(&load));
    }

    #[test]
    fn test_licm_tier_b_same_stack_slot_refuses() {
        // Load and store both target ss0: cannot prove disjoint — refuse.
        let (mut func, bb0, bb1, bb2) = single_block_loop();
        materialize_slot(&mut func, bb0, 0, 0); // v0 = &ss0
        append(&mut func, bb0, AArch64Opcode::MovI, vec![vreg(9), imm(7)]);
        finish_preheader_branch(&mut func, bb0, bb1);
        let load = append(
            &mut func,
            bb1,
            AArch64Opcode::LdrRI,
            vec![vreg(4), vreg(0), imm(0)],
        );
        append(
            &mut func,
            bb1,
            AArch64Opcode::StrRI,
            vec![vreg(9), vreg(0), imm(8)],
        );
        finish_loop_tail(&mut func, bb1, bb2);

        let mut licm = LoopInvariantCodeMotion;
        assert!(!licm.run(&mut func), "same-slot load/store must not hoist");
        assert!(func.block(bb1).insts.contains(&load));
    }

    #[test]
    fn test_licm_tier_b_stack_vs_global_hoists() {
        // Load a stack slot, store a global: the stack and data segment are
        // disjoint address ranges.
        let (mut func, bb0, bb1, bb2) = single_block_loop();
        materialize_slot(&mut func, bb0, 0, 0); // v0 = &ss0 (load base)
        materialize_global(&mut func, bb0, 2, 3, "gB"); // v3 = &gB (store base)
        append(&mut func, bb0, AArch64Opcode::MovI, vec![vreg(9), imm(7)]);
        finish_preheader_branch(&mut func, bb0, bb1);
        let load = append(
            &mut func,
            bb1,
            AArch64Opcode::LdrRI,
            vec![vreg(4), vreg(0), imm(0)],
        );
        append(
            &mut func,
            bb1,
            AArch64Opcode::StrRI,
            vec![vreg(9), vreg(3), imm(0)],
        );
        finish_loop_tail(&mut func, bb1, bb2);

        let mut licm = LoopInvariantCodeMotion;
        assert!(licm.run(&mut func), "stack-load vs global-store must hoist");
        assert!(func.block(bb0).insts.contains(&load));
        assert!(!func.block(bb1).insts.contains(&load));
    }

    #[test]
    fn test_licm_no_hoist_load_past_call() {
        // An opaque writer (a call clobbers all memory) fails tier (b) closed
        // even for an otherwise-classifiable global load.
        let (mut func, bb0, bb1, bb2) = single_block_loop();
        materialize_global(&mut func, bb0, 0, 1, "gA"); // v1 = &gA
        finish_preheader_branch(&mut func, bb0, bb1);
        let load = append(
            &mut func,
            bb1,
            AArch64Opcode::LdrRI,
            vec![vreg(4), vreg(1), imm(0)],
        );
        append(&mut func, bb1, AArch64Opcode::Bl, vec![imm(0x1000)]);
        finish_loop_tail(&mut func, bb1, bb2);

        let mut licm = LoopInvariantCodeMotion;
        assert!(
            !licm.run(&mut func),
            "load must not hoist past an opaque call"
        );
        assert!(func.block(bb1).insts.contains(&load));
    }

    // ---------------------------------------------------------------------
    // MULTI-LATCH must-execute (2026-08-18)
    // ---------------------------------------------------------------------

    /// A natural loop with TWO back-edges to the same header and NO exiting
    /// block: bb0 -> bb1; bb1 -> {bb2, bb3}; bb2 -> bb1; bb3 -> bb1.
    ///
    /// `LoopAnalysis` merges both back-edges into ONE `NaturalLoop` (bodies
    /// unioned) but caches a SINGLE representative `lp.latch`, so a gate that
    /// tests only that one is blind to the sibling latch.
    fn multi_latch_no_exit_loop() -> (MachFunction, BlockId, BlockId, BlockId, BlockId) {
        let mut func = MachFunction::new("licm_ml".to_string(), Signature::new(vec![], vec![]));
        let bb0 = func.entry;
        let bb1 = func.create_block();
        let bb2 = func.create_block();
        let bb3 = func.create_block();
        func.add_edge(bb0, bb1);
        func.add_edge(bb1, bb2);
        func.add_edge(bb1, bb3);
        func.add_edge(bb2, bb1);
        func.add_edge(bb3, bb1);
        (func, bb0, bb1, bb2, bb3)
    }

    /// WRONG-CODE REGRESSION: a load sitting in ONE latch of a multi-latch loop
    /// must not be speculated into the preheader.
    ///
    /// `load_guaranteed_to_execute` used to check `dominates(load, lp.latch)`
    /// for the single cached latch plus every EXITING block. Here bb2 is the
    /// cached latch (first back-edge source in block order) so that check
    /// passes, and the loop has no exiting block at all so the exit sweep is
    /// VACUOUS — yet an iteration can return to the header through bb3 without
    /// ever entering bb2. Hoisting then makes a program that merely spins
    /// forever instead FAULT on the very first entry.
    #[test]
    fn test_licm_no_hoist_load_in_undominated_second_latch() {
        let (mut func, bb0, bb1, bb2, bb3) = multi_latch_no_exit_loop();
        append(
            &mut func,
            bb0,
            AArch64Opcode::MovI,
            vec![vreg(0), imm(4096)],
        );
        finish_preheader_branch(&mut func, bb0, bb1);
        append(
            &mut func,
            bb1,
            AArch64Opcode::BCond,
            vec![MachOperand::Block(bb2), MachOperand::Block(bb3)],
        );
        // Latch A carries the invariant load ...
        let load = append(
            &mut func,
            bb2,
            AArch64Opcode::LdrRI,
            vec![vreg(1), vreg(0), imm(0)],
        );
        append(
            &mut func,
            bb2,
            AArch64Opcode::B,
            vec![MachOperand::Block(bb1)],
        );
        // ... latch B does not, and bb2 does not dominate it.
        append(
            &mut func,
            bb3,
            AArch64Opcode::AddRI,
            vec![vreg(8), vreg(8), imm(1)],
        );
        append(
            &mut func,
            bb3,
            AArch64Opcode::B,
            vec![MachOperand::Block(bb1)],
        );

        let mut licm = LoopInvariantCodeMotion;
        licm.run(&mut func);
        assert!(
            func.block(bb2).insts.contains(&load),
            "a load in a latch that a SIBLING latch bypasses must not be \
             speculated into the preheader (multi-latch must-execute)"
        );
        assert!(
            !func.block(bb0).insts.contains(&load),
            "the load must not appear in the preheader"
        );
    }

    /// POSITIVE CONTROL for the tightened gate — it must not over-gate.
    /// The header dominates every back-edge source, so a header load still
    /// hoists out of the same multi-latch loop.
    #[test]
    fn test_licm_hoists_load_from_header_of_multi_latch_loop() {
        let (mut func, bb0, bb1, bb2, bb3) = multi_latch_no_exit_loop();
        append(
            &mut func,
            bb0,
            AArch64Opcode::MovI,
            vec![vreg(0), imm(4096)],
        );
        finish_preheader_branch(&mut func, bb0, bb1);
        let load = append(
            &mut func,
            bb1,
            AArch64Opcode::LdrRI,
            vec![vreg(1), vreg(0), imm(0)],
        );
        append(
            &mut func,
            bb1,
            AArch64Opcode::BCond,
            vec![MachOperand::Block(bb2), MachOperand::Block(bb3)],
        );
        append(
            &mut func,
            bb2,
            AArch64Opcode::B,
            vec![MachOperand::Block(bb1)],
        );
        append(
            &mut func,
            bb3,
            AArch64Opcode::AddRI,
            vec![vreg(8), vreg(8), imm(1)],
        );
        append(
            &mut func,
            bb3,
            AArch64Opcode::B,
            vec![MachOperand::Block(bb1)],
        );

        let mut licm = LoopInvariantCodeMotion;
        assert!(licm.run(&mut func), "header load must still hoist");
        assert!(func.block(bb0).insts.contains(&load));
        assert!(!func.block(bb1).insts.contains(&load));
    }
}

#[cfg(test)]
mod region_tests {
    use super::*;
    use trust_cg_ir::{
        AArch64Opcode, InstId, MachFunction, MachInst, MachOperand, RegClass, Signature, VReg,
    };

    fn vreg(id: u32) -> MachOperand {
        MachOperand::VReg(VReg::new(id, RegClass::Gpr64))
    }

    fn vreg_class(id: u32, class: RegClass) -> MachOperand {
        MachOperand::VReg(VReg::new(id, class))
    }

    fn imm(val: i64) -> MachOperand {
        MachOperand::Imm(val)
    }

    fn append(
        func: &mut MachFunction,
        block: trust_cg_ir::BlockId,
        opcode: AArch64Opcode,
        operands: Vec<MachOperand>,
    ) -> InstId {
        let id = func.push_inst(MachInst::new(opcode, operands));
        func.append_inst(block, id);
        id
    }

    /// The rustc nested-counted-loop shape the region hoist targets, in the
    /// materialized-boolean guard form that exists at LICM time:
    ///
    /// ```text
    ///   bb0 (entry = outer preheader):  v0=0 (i)  v1=10 (n)  v10=0 (acc); B bb1
    ///   bb1 (outer header): CmpRR v0,v1; CSet v2,LT; CmpRI v2,#0;
    ///                       BCond NE bb2; B bb6
    ///   bb2 (inner preheader ip):  v3=0 (inner counter INIT);
    ///                              MovR v4,v0 (outer-varying SNAPSHOT); B bb3
    ///   bb3 (inner header): CmpRI v3,#100; CSet v5,LT; CmpRI v5,#0;
    ///                       BCond NE bb4; B bb5           (single header exit)
    ///   bb4 (inner latch):  v10=v10+1; v3=v3+1; B bb3
    ///   bb5 (outer latch = exit_blk): v6=v4+v10; v0=v0+1; B bb1
    ///   bb6: Ret
    /// ```
    ///
    /// The inner loop (bb3-bb4) is memory-pure and reads only its own INIT
    /// (`v3`) and carried defs; the snapshot `v4` stays behind in `ip`.
    fn make_region_shape() -> (MachFunction, [trust_cg_ir::BlockId; 7]) {
        let mut func =
            MachFunction::new("region_shape".to_string(), Signature::new(vec![], vec![]));
        let bb0 = func.entry;
        let bb1 = func.create_block();
        let bb2 = func.create_block();
        let bb3 = func.create_block();
        let bb4 = func.create_block();
        let bb5 = func.create_block();
        let bb6 = func.create_block();

        const LT: i64 = 11;
        const NE: i64 = 1;

        append(&mut func, bb0, AArch64Opcode::MovI, vec![vreg(0), imm(0)]);
        append(&mut func, bb0, AArch64Opcode::MovI, vec![vreg(1), imm(10)]);
        append(&mut func, bb0, AArch64Opcode::MovI, vec![vreg(10), imm(0)]);
        append(
            &mut func,
            bb0,
            AArch64Opcode::B,
            vec![MachOperand::Block(bb1)],
        );

        append(&mut func, bb1, AArch64Opcode::CmpRR, vec![vreg(0), vreg(1)]);
        append(&mut func, bb1, AArch64Opcode::CSet, vec![vreg(2), imm(LT)]);
        append(&mut func, bb1, AArch64Opcode::CmpRI, vec![vreg(2), imm(0)]);
        append(
            &mut func,
            bb1,
            AArch64Opcode::BCond,
            vec![imm(NE), MachOperand::Block(bb2)],
        );
        append(
            &mut func,
            bb1,
            AArch64Opcode::B,
            vec![MachOperand::Block(bb6)],
        );

        append(&mut func, bb2, AArch64Opcode::MovI, vec![vreg(3), imm(0)]);
        append(&mut func, bb2, AArch64Opcode::MovR, vec![vreg(4), vreg(0)]);
        append(
            &mut func,
            bb2,
            AArch64Opcode::B,
            vec![MachOperand::Block(bb3)],
        );

        append(
            &mut func,
            bb3,
            AArch64Opcode::CmpRI,
            vec![vreg(3), imm(100)],
        );
        append(&mut func, bb3, AArch64Opcode::CSet, vec![vreg(5), imm(LT)]);
        append(&mut func, bb3, AArch64Opcode::CmpRI, vec![vreg(5), imm(0)]);
        append(
            &mut func,
            bb3,
            AArch64Opcode::BCond,
            vec![imm(NE), MachOperand::Block(bb4)],
        );
        append(
            &mut func,
            bb3,
            AArch64Opcode::B,
            vec![MachOperand::Block(bb5)],
        );

        append(
            &mut func,
            bb4,
            AArch64Opcode::AddRI,
            vec![vreg(10), vreg(10), imm(1)],
        );
        append(
            &mut func,
            bb4,
            AArch64Opcode::AddRI,
            vec![vreg(3), vreg(3), imm(1)],
        );
        append(
            &mut func,
            bb4,
            AArch64Opcode::B,
            vec![MachOperand::Block(bb3)],
        );

        append(
            &mut func,
            bb5,
            AArch64Opcode::AddRR,
            vec![vreg(6), vreg(4), vreg(10)],
        );
        append(
            &mut func,
            bb5,
            AArch64Opcode::AddRI,
            vec![vreg(0), vreg(0), imm(1)],
        );
        append(
            &mut func,
            bb5,
            AArch64Opcode::B,
            vec![MachOperand::Block(bb1)],
        );

        append(&mut func, bb6, AArch64Opcode::Ret, vec![]);

        func.add_edge(bb0, bb1);
        func.add_edge(bb1, bb2);
        func.add_edge(bb1, bb6);
        func.add_edge(bb2, bb3);
        func.add_edge(bb3, bb4);
        func.add_edge(bb3, bb5);
        func.add_edge(bb4, bb3);
        func.add_edge(bb5, bb1);

        (func, [bb0, bb1, bb2, bb3, bb4, bb5, bb6])
    }

    #[test]
    fn test_region_hoists_outer_invariant_inner_loop() {
        let (mut func, [bb0, bb1, bb2, bb3, bb4, bb5, _bb6]) = make_region_shape();
        let ip_movi_v3 = func.block(bb2).insts[0];
        let ip_movr_v4 = func.block(bb2).insts[1];

        assert!(region_licm_run(&mut func), "the region hoist must fire");

        // The synthesized run-once preheader is the newest block.
        let sp = trust_cg_ir::BlockId((func.num_blocks() - 1) as u32);

        // sp = INIT cluster (the MovI v3 init, MOVED by InstId) + B bb3.
        let sp_insts = &func.block(sp).insts;
        assert_eq!(sp_insts.len(), 2);
        assert_eq!(sp_insts[0], ip_movi_v3);
        let sp_term = func.inst(sp_insts[1]);
        assert_eq!(sp_term.opcode, AArch64Opcode::B);
        assert_eq!(sp_term.operands[0], MachOperand::Block(bb3));

        // op_pre now enters sp; ip keeps the snapshot and jumps to exit_blk.
        assert_eq!(func.block(bb0).succs, vec![sp]);
        assert_eq!(func.block(bb2).insts.len(), 2, "ip = snapshot + terminator");
        assert_eq!(func.block(bb2).insts[0], ip_movr_v4);
        assert_eq!(func.block(bb2).succs, vec![bb5]);
        let ip_term = func.inst(*func.block(bb2).insts.last().unwrap());
        assert_eq!(ip_term.opcode, AArch64Opcode::B);
        assert_eq!(ip_term.operands[0], MachOperand::Block(bb5));

        // The inner header's exit edge now re-enters the outer loop.
        assert!(func.block(bb3).succs.contains(&bb1));
        assert!(!func.block(bb3).succs.contains(&bb5));

        // preds stayed consistent with succs at every seam.
        assert_eq!(func.block(sp).preds, vec![bb0]);
        assert!(func.block(bb3).preds.contains(&sp));
        assert!(!func.block(bb3).preds.contains(&bb2));
        assert_eq!(func.block(bb5).preds, vec![bb2]);
        assert!(func.block(bb1).preds.contains(&bb3));
        assert!(!func.block(bb1).preds.contains(&bb0));

        // Layout: [sp, inner blocks] immediately after op_pre.
        let order = &func.block_order;
        let p0 = order.iter().position(|&b| b == bb0).unwrap();
        assert_eq!(order[p0 + 1], sp);
        assert_eq!(order[p0 + 2], bb3);
        assert_eq!(order[p0 + 3], bb4);

        // One hoist only; the transformed function is a fixpoint.
        assert!(
            !region_licm_run(&mut func),
            "region hoist must be idempotent"
        );
    }

    #[test]
    fn test_region_declines_outer_varying_inner_read() {
        // Same shape, but the inner latch reads the per-outer-iteration
        // snapshot v4 (`v10 = v10 + v4`), making v4 an inner live-in whose ip
        // def (`MovR v4, v0`) has an outer-varying source — INIT declines.
        let (mut func, [bb0, _bb1, _bb2, _bb3, bb4, _bb5, _bb6]) = make_region_shape();
        let add_v10 = func.block(bb4).insts[0];
        func.inst_mut(add_v10).opcode = AArch64Opcode::AddRR;
        func.inst_mut(add_v10).operands = vec![vreg(10), vreg(10), vreg(4)];

        let n_blocks = func.num_blocks();
        assert!(
            !region_licm_run(&mut func),
            "an outer-varying inner live-in must decline the hoist"
        );
        assert_eq!(func.num_blocks(), n_blocks, "no block may be synthesized");
        assert_eq!(func.block(bb0).succs, vec![trust_cg_ir::BlockId(1)]);
    }

    #[test]
    fn test_region_declines_movz_movk_init_chain() {
        // Region-LICM v1 admits only full-register MovI/MovR INIT nodes.  A
        // MOVZ/MOVK literal carrier is multiply defined and tied-def-use, so
        // the ordinary single-def X5 net cannot validate it.  Keep the current
        // lane fail-closed until exact chain identities/order are threaded.
        let (mut func, [bb0, _bb1, bb2, _bb3, _bb4, _bb5, _bb6]) = make_region_shape();
        let movz = func.block(bb2).insts[0];
        func.inst_mut(movz).opcode = AArch64Opcode::Movz;
        func.inst_mut(movz).operands = vec![vreg(3), imm(0x1234)];
        let movk = func.push_inst(MachInst::new(
            AArch64Opcode::Movk,
            vec![vreg(3), imm(0x5678), imm(16)],
        ));
        func.block_mut(bb2).insts.insert(1, movk);

        let original_ip = func.block(bb2).insts.clone();
        let original_blocks = func.num_blocks();
        assert!(
            !region_licm_run(&mut func),
            "MOVZ/MOVK INIT chains must decline while region X5 is single-def only"
        );
        assert_eq!(
            func.num_blocks(),
            original_blocks,
            "no preheader synthesized"
        );
        assert_eq!(func.block(bb2).insts, original_ip, "INIT chain stays in ip");
        assert_eq!(func.block(bb0).succs, vec![trust_cg_ir::BlockId(1)]);
    }

    // ===================================================================
    // Pure-call cluster hoist tier (X3, aarch64 port of x86
    // `hoist_pure_call_clusters`). These drive `hoist_pure_call_clusters`
    // DIRECTLY — never through the env-gated `LoopInvariantCodeMotion::run`
    // — so they neither read nor write the process-global `TCG_A64_PURE_CALL_HOIST`
    // and cannot race the other tests in this binary.
    // ===================================================================

    const PC_ARG_REGS: &[PReg] = &[X0];

    /// Build a single counted loop whose body holds one pure-call cluster with a
    /// loop-invariant argument:
    ///
    /// ```text
    ///   bb0 (preheader):  v0 = movi #0 (iv init)   v7 = movi #7 (invariant arg)
    ///                     b bb1
    ///   bb1 (header):     cmpri v0, #10             b.lt bb2 ; b bb3
    ///   bb2 (body/latch): copy X0, v7  [ARG_SETUP] ← arg move (invariant source)
    ///                     bl @pure     [proof=Pure, uses=X0]
    ///                     copy v9, X0                ← result capture
    ///                     b bb1
    ///   bb3 (exit):       ret
    /// ```
    ///
    /// The header's `cmpri v0(=0), #10 ; b.lt bb2` discharges
    /// `region_loop_runs_at_least_once`, so the >=1-trip precondition holds and
    /// the (possibly divergent) pure call is legal to run once in the preheader.
    /// Returns `(func, [arg, call, result] InstIds, [bb0,bb1,bb2,bb3])`.
    fn make_pure_call_loop(
        pure: bool,
        invariant_arg: bool,
    ) -> (MachFunction, [InstId; 3], [BlockId; 4]) {
        let mut func = MachFunction::new("pc_hoist".to_string(), Signature::new(vec![], vec![]));
        let bb0 = func.entry;
        let bb1 = func.create_block();
        let bb2 = func.create_block();
        let bb3 = func.create_block();

        // bb0 preheader: iv init + invariant arg source; unconditional B header.
        append(&mut func, bb0, AArch64Opcode::MovI, vec![vreg(0), imm(0)]);
        append(&mut func, bb0, AArch64Opcode::MovI, vec![vreg(7), imm(7)]);
        append(
            &mut func,
            bb0,
            AArch64Opcode::B,
            vec![MachOperand::Block(bb1)],
        );

        // bb1 header: cmpri v0,#10 ; b.lt(11) bb2 ; b bb3 (>=1-trip provable).
        append(&mut func, bb1, AArch64Opcode::CmpRI, vec![vreg(0), imm(10)]);
        append(
            &mut func,
            bb1,
            AArch64Opcode::BCond,
            vec![imm(11), MachOperand::Block(bb2)],
        );
        append(
            &mut func,
            bb1,
            AArch64Opcode::B,
            vec![MachOperand::Block(bb3)],
        );

        // bb2 body: the cluster. Arg source is v7 (invariant, from bb0) unless
        // `invariant_arg` is false, in which case it is v0-in-loop... we instead
        // use a body-defined vreg to make the source loop-variant.
        if !invariant_arg {
            // A loop-defined source for the arg move (v20 defined here in body).
            append(&mut func, bb2, AArch64Opcode::MovI, vec![vreg(20), imm(3)]);
        }
        let arg_src = if invariant_arg { vreg(7) } else { vreg(20) };
        let mut arg = MachInst::new(AArch64Opcode::Copy, vec![MachOperand::PReg(X0), arg_src]);
        arg.flags = arg.flags.union(trust_cg_ir::InstFlags::IS_CALL_ARG_SETUP);
        let arg_id = func.push_inst(arg);
        func.append_inst(bb2, arg_id);

        let mut call = MachInst::new(AArch64Opcode::Bl, vec![]);
        if pure {
            call.proof = Some(ProofAnnotation::Pure);
        }
        call.implicit_uses = PC_ARG_REGS;
        let call_id = func.push_inst(call);
        func.append_inst(bb2, call_id);

        let res = MachInst::new(AArch64Opcode::Copy, vec![vreg(9), MachOperand::PReg(X0)]);
        let res_id = func.push_inst(res);
        func.append_inst(bb2, res_id);

        append(
            &mut func,
            bb2,
            AArch64Opcode::B,
            vec![MachOperand::Block(bb1)],
        );

        // bb3 exit.
        append(&mut func, bb3, AArch64Opcode::Ret, vec![]);

        func.add_edge(bb0, bb1);
        func.add_edge(bb1, bb2);
        func.add_edge(bb1, bb3);
        func.add_edge(bb2, bb1); // back-edge

        (func, [arg_id, call_id, res_id], [bb0, bb1, bb2, bb3])
    }

    fn pc_run(func: &mut MachFunction) -> bool {
        let dom = DomTree::compute(func);
        let analysis = LoopAnalysis::compute(func, &dom);
        let loops: Vec<NaturalLoop> = analysis.all_loops().cloned().collect();
        assert_eq!(loops.len(), 1, "expected exactly one natural loop");
        let def_counts = build_def_counts(func);
        hoist_pure_call_clusters(func, &loops[0], &def_counts, &dom)
    }

    #[test]
    fn pure_call_cluster_hoists_out_of_loop() {
        let (mut func, cluster, [bb0, _bb1, bb2, _bb3]) = make_pure_call_loop(true, true);
        assert!(
            pc_run(&mut func),
            "an invariant pure-call cluster must hoist"
        );
        // All three cluster instructions moved out of the body...
        for id in cluster {
            assert!(
                !func.block(bb2).insts.contains(&id),
                "cluster inst {id:?} must leave the loop body"
            );
            assert!(
                func.block(bb0).insts.contains(&id),
                "cluster inst {id:?} must land in the preheader"
            );
        }
        // ...in order, and strictly before the preheader's terminating branch.
        let ph = &func.block(bb0).insts;
        let pos = |id: InstId| ph.iter().position(|&x| x == id).unwrap();
        assert!(pos(cluster[0]) < pos(cluster[1]) && pos(cluster[1]) < pos(cluster[2]));
        let b_pos = ph
            .iter()
            .position(|&id| func.inst(id).opcode == AArch64Opcode::B)
            .unwrap();
        assert!(
            pos(cluster[2]) < b_pos,
            "cluster must precede the B to header"
        );
    }

    #[test]
    fn pure_call_cluster_declines_impure_call() {
        // Same shape but the `Bl` carries no `ProofAnnotation::Pure` — it may have
        // observable side effects, so hoisting is illegal.
        let (mut func, cluster, [_bb0, _bb1, bb2, _bb3]) = make_pure_call_loop(false, true);
        assert!(!pc_run(&mut func), "a non-pure call must never hoist");
        for id in cluster {
            assert!(
                func.block(bb2).insts.contains(&id),
                "cluster must stay in body"
            );
        }
    }

    #[test]
    fn pure_call_cluster_declines_loop_variant_arg() {
        // The argument source is defined inside the loop body, so the call is not
        // loop-invariant and must not hoist.
        let (mut func, cluster, [_bb0, _bb1, bb2, _bb3]) = make_pure_call_loop(true, false);
        assert!(
            !pc_run(&mut func),
            "a loop-variant argument must block the hoist"
        );
        for id in cluster {
            assert!(
                func.block(bb2).insts.contains(&id),
                "cluster must stay in body"
            );
        }
    }

    #[test]
    fn pure_call_cluster_declines_conditional_preheader() {
        // Fail-closed hardening: rewrite the preheader to end in a CONDITIONAL
        // branch `cmprr; b.cond header; b other`. `find_preheader` still returns
        // bb0 (the header's unique non-loop predecessor), but hoisting the
        // flag-clobbering / possibly-trapping call into it is unsound (flag split
        // + trap on the loop-skipping edge). The guard must decline.
        let (mut func, cluster, [bb0, bb1, bb2, bb3]) = make_pure_call_loop(true, true);
        // Replace bb0's terminating `B bb1` with `cmprr v0,v7; b.lt bb1; b bb3`.
        func.block_mut(bb0).insts.pop(); // drop the unconditional B
        let cmp = func.push_inst(MachInst::new(AArch64Opcode::CmpRR, vec![vreg(0), vreg(7)]));
        func.append_inst(bb0, cmp);
        let bc = func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![imm(11), MachOperand::Block(bb1)],
        ));
        func.append_inst(bb0, bc);
        let be = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb3)],
        ));
        func.append_inst(bb0, be);
        func.add_edge(bb0, bb3); // bb0 now also reaches bb3 (two successors)

        assert!(
            !pc_run(&mut func),
            "a conditionally-branching preheader must decline the pure-call hoist"
        );
        for id in cluster {
            assert!(
                func.block(bb2).insts.contains(&id),
                "cluster must stay in body"
            );
        }
    }

    // ---- X5 value-level net (verify_preheader_defs_precede_uses) -----------

    /// Build a single-block function whose block holds `insts` in order; return
    /// (func, block). Used to drive the preheader def-before-use verifier.
    fn single_block(insts: Vec<MachInst>) -> (MachFunction, BlockId) {
        let mut func = MachFunction::new("x5_net".to_string(), Signature::new(vec![], vec![]));
        let bb = func.entry;
        for mi in insts {
            let id = func.push_inst(mi);
            func.append_inst(bb, id);
        }
        (func, bb)
    }

    #[test]
    fn x5_net_accepts_def_before_use() {
        // movi v0,#5 ; add v2 <- v1, v0  — v0 defined (idx 0) BEFORE its use (idx 1).
        let (func, bb) = single_block(vec![
            MachInst::new(AArch64Opcode::MovI, vec![vreg(0), imm(5)]),
            MachInst::new(AArch64Opcode::AddRR, vec![vreg(2), vreg(1), vreg(0)]),
        ]);
        let dc = build_def_counts(&func);
        verify_preheader_defs_precede_uses(&func, bb, &dc); // must NOT panic
    }

    #[test]
    #[should_panic(expected = "use-before-def")]
    fn x5_net_fires_on_use_before_def() {
        // add v2 <- v1, v0 (uses v0 at idx 0) ; movi v0,#5 (its ONLY def at idx 1).
        // v0 is single-def, so the use at idx 0 < def at idx 1 is an unambiguous
        // use-before-def — the net must fail closed (panic).
        let (func, bb) = single_block(vec![
            MachInst::new(AArch64Opcode::AddRR, vec![vreg(2), vreg(1), vreg(0)]),
            MachInst::new(AArch64Opcode::MovI, vec![vreg(0), imm(5)]),
        ]);
        let dc = build_def_counts(&func);
        verify_preheader_defs_precede_uses(&func, bb, &dc);
    }

    #[test]
    fn x5_net_skips_multi_def_vreg() {
        // v0 defined TWICE (idx 1, idx 2) — multi-def, so a use at idx 0 is NOT
        // flagged (it may legitimately read a dominating-block def under the
        // non-SSA machine IR). Conservative: no panic.
        let (func, bb) = single_block(vec![
            MachInst::new(AArch64Opcode::AddRR, vec![vreg(2), vreg(1), vreg(0)]),
            MachInst::new(AArch64Opcode::MovI, vec![vreg(0), imm(5)]),
            MachInst::new(AArch64Opcode::MovI, vec![vreg(0), imm(6)]),
        ]);
        let dc = build_def_counts(&func);
        verify_preheader_defs_precede_uses(&func, bb, &dc); // must NOT panic (multi-def skipped)
    }

    #[test]
    #[should_panic(expected = "constant-chain use-before-complete")]
    fn x5_constant_chain_net_fires_when_consumer_precedes_final_patch() {
        // The ordinary single-def net intentionally skips v0.  The dedicated
        // chain net must still reject exposing its partial value to FMOV before
        // MOVZ/MOVK have completed the literal.
        let (func, bb) = single_block(vec![
            MachInst::new(
                AArch64Opcode::FmovGprFpr,
                vec![vreg_class(2, RegClass::Fpr64), vreg(0)],
            ),
            MachInst::new(AArch64Opcode::Movz, vec![vreg(0), imm(0x1400)]),
            MachInst::new(AArch64Opcode::Movk, vec![vreg(0), imm(0x3fe8), imm(16)]),
        ]);
        let ids = func.block(bb).insts.clone();
        verify_preheader_constant_chains(
            &func,
            bb,
            &[(VReg::new(0, RegClass::Gpr64), vec![ids[1], ids[2]])],
        );
    }

    #[test]
    #[should_panic(expected = "constant-chain order bug")]
    fn x5_constant_chain_net_fires_when_patches_are_reordered() {
        let (func, bb) = single_block(vec![
            MachInst::new(AArch64Opcode::Movk, vec![vreg(0), imm(0x3fe8), imm(16)]),
            MachInst::new(AArch64Opcode::Movz, vec![vreg(0), imm(0x1400)]),
            MachInst::new(
                AArch64Opcode::FmovGprFpr,
                vec![vreg_class(2, RegClass::Fpr64), vreg(0)],
            ),
        ]);
        let ids = func.block(bb).insts.clone();
        // Recorded semantic order is MOVZ then MOVK, but physical order is the
        // reverse.  This is exactly the splice error the runtime net guards.
        verify_preheader_constant_chains(
            &func,
            bb,
            &[(VReg::new(0, RegClass::Gpr64), vec![ids[1], ids[0]])],
        );
    }
}
