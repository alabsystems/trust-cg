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
//!   every in-loop store (bounded accesses in distinct fixed stack slots —
//!   see `addr_bases_disjoint`); symbol names and ADRP pages are not object
//!   authority, and any store we cannot
//!   classify fails the loop closed. Both tiers reason only about this
//!   thread's writes, so a loop containing a load-acquire (`Ldar*`/`Ldaxr`)
//!   counts as an opaque writer and admits no load: after the acquire the
//!   thread may observe what another thread published before the matching
//!   release, and a hoisted load would have read before it.
//! - **Speculation (fault) safety.** Hoisting to the preheader must not
//!   introduce a fault on a zero-trip, early-exit or non-terminating path. The
//!   load is admitted only when it is GUARANTEED TO EXECUTE: its block
//!   dominates EVERY latch (back-edge source, not just the cached `lp.latch`)
//!   and every loop-exiting block, nothing the first iteration runs before it
//!   can stop it (an earlier branch in its block, or an in-loop guard carrier,
//!   `BRK` or call on the way to it) or spin in an inner cycle before it (an
//!   inner loop, reducible or not, between the header and the load's block),
//!   AND the preheader unconditionally enters the loop (so reaching the
//!   preheader implies the first iteration reaches the load unless an earlier
//!   access of that iteration faults). See `load_guaranteed_to_execute`. A
//!   load that is NOT guaranteed to execute is still admitted when its
//!   address is a **dereferenceable frame access**: the base resolves, through
//!   copies and immediate offsets, to one fixed-size stack slot's address and
//!   the accessed bytes lie inside that slot (`frame_access_in_bounds`). The
//!   frame is mapped for the whole activation, so executing such a load early
//!   cannot fault. This is the AArch64 port of the x86 invariant-load tier's
//!   speculation argument (`x86_licm.rs`).
//! - **Placement.** The value-stability tiers examine in-loop writers only, so
//!   a hoisted load must read memory in the state the loop is entered with:
//!   it is inserted after every preheader store, call and mid-block trap guard,
//!   right before the preheader's branch tail (`preheader_insert_pos`). The
//!   loaded value then equals what the original load would read on every
//!   iteration, and it is used only where the original load ran. A preheader
//!   whose call an exception can leave through (an invoke block) is refused:
//!   code after that call does not run on the edge to the landing pad.
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

use crate::fast_hash::{FxHashMap as HashMap, FxHashSet as HashSet};

use trust_cg_ir::aarch64_regs::{X0, gpr32_to_gpr64, preg_class};
use trust_cg_ir::function::StackSlotAllocationKind;
use trust_cg_ir::{
    AArch64Opcode, BlockId, InstId, MachFunction, MachInst, MachOperand, PReg, ProofAnnotation,
    ProvenanceMap, RegClass, StackSlotId, VReg,
};

use crate::dom::DomTree;
use crate::effects::{
    aarch64_for_each_use_position, for_each_inst_def, inst_defines_vreg, is_load_acquire,
    opcode_effect, produces_value, reads_flags, single_inst_def, writes_flags,
};
use crate::interfaces::OpInterfaces;
use crate::loops::{LoopAnalysis, NaturalLoop, blocks_before_first_reaching};
use crate::pass_manager::{AnalysisCache, MachinePass};

/// Loop-Invariant Code Motion pass.
#[derive(Clone, Copy, Debug)]
pub struct LoopInvariantCodeMotion {
    /// Admit loop-invariant loads that are not guaranteed to execute when they
    /// read inside one fixed-size stack slot (see the module docs). The
    /// pipeline turns this off for the `licmframespec` disable-list key.
    frame_speculation: bool,
}

impl Default for LoopInvariantCodeMotion {
    fn default() -> Self {
        Self::new()
    }
}

impl LoopInvariantCodeMotion {
    /// The pass with every tier on (the default pipeline configuration).
    pub const fn new() -> Self {
        Self {
            frame_speculation: true,
        }
    }

    /// The pass without the dereferenceable-frame speculation of loads that
    /// are not guaranteed to execute (the load rules before 2026-09-28).
    pub const fn without_frame_speculation() -> Self {
        Self {
            frame_speculation: false,
        }
    }
}

impl MachinePass for LoopInvariantCodeMotion {
    fn name(&self) -> &str {
        "licm"
    }

    fn run(&mut self, func: &mut MachFunction) -> bool {
        let dom = DomTree::compute(func);
        let loop_analysis = LoopAnalysis::compute(func, &dom);
        Self::run_with_loop_analysis(func, &dom, &loop_analysis, self.frame_speculation)
    }

    fn run_with_analyses(&mut self, func: &mut MachFunction, analyses: &mut AnalysisCache) -> bool {
        // Borrowed from the cache (no clone, no dominator recompute): the
        // cache's tree and loops are the ones computed for this CFG, which no
        // pass since has changed (the manager invalidates them when it does).
        let (dom, loop_analysis) = analyses.domtree_and_loops(func);
        Self::run_with_loop_analysis(func, dom, loop_analysis, self.frame_speculation)
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
        // Borrowed from the cache (no clone, no dominator recompute): the
        // cache's tree and loops are the ones computed for this CFG, which no
        // pass since has changed (the manager invalidates them when it does).
        let (dom, loop_analysis) = analyses.domtree_and_loops(func);
        Self::run_with_loop_analysis(func, dom, loop_analysis, self.frame_speculation)
    }
}

impl LoopInvariantCodeMotion {
    fn run_with_loop_analysis(
        func: &mut MachFunction,
        dom: &DomTree,
        loop_analysis: &LoopAnalysis,
        frame_speculation: bool,
    ) -> bool {
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
        let recomputed_dom;
        let (dom, loop_analysis) = if region_licm_enabled() && region_licm_run(func) {
            changed = true;
            recomputed_dom = DomTree::compute(func);
            recomputed_after_region = LoopAnalysis::compute(func, &recomputed_dom);
            (&recomputed_dom, &recomputed_after_region)
        } else {
            (dom, loop_analysis)
        };

        // The dominator tree is needed by the load speculation guard. The
        // instruction tiers below only ever MOVE existing instructions between
        // existing blocks (they refuse synthetic preheaders), so they never
        // mutate the CFG: the tree passed in (the cache's, computed for this
        // very CFG — or the one recomputed after region surgery above) stays
        // valid across every hoist in this function.

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
        let def_map = crate::effects::build_reaching_def_map_by_vreg(func);
        // Each block's position in `block_order`, so a loop visits its own
        // body blocks in layout order without walking the whole layout (see
        // `body_blocks_in_layout`). The instruction tiers below never change
        // the layout, so one map, built by the second loop that asks, serves
        // every later loop.
        let layout = LayoutPositions::new();

        // Built lazily by the first loop that reaches the constant-chain tier,
        // shared by the rest, and brought up to date after any loop that
        // hoisted (`ConstChainIndex::refresh`).
        let mut chain_index: Option<ConstChainIndex> = None;
        // Def-site index shared by frame speculation and bounded-stack alias
        // admission: built on demand, shared by later loops, and dropped after
        // any loop that hoisted (a move changes def positions).
        let mut frame_defs: Option<FrameDefSites> = None;
        // Invoke blocks are refused as preheaders (`hoist_loop_invariants`).
        // The tiers below move no call, so one collection serves every loop.
        let unwind_exits = crate::eh_call_custody::UnwindExits::collect(func);
        for (loop_index, lp) in loops.iter().enumerate() {
            if dump_chains_enabled() {
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
            let mut touched: Vec<BlockId> = Vec::new();
            if hoist_loop_invariants(
                func,
                lp,
                dom,
                &unwind_exits,
                &def_counts,
                &def_map,
                &layout,
                &mut chain_index,
                &mut frame_defs,
                frame_speculation,
                &mut touched,
            ) {
                changed = true;
                // After the last loop nothing reads the index again.
                let later_loops = loop_index + 1 < loops.len();
                if let Some(index) = &mut chain_index
                    && (!later_loops
                        || force_chain_index_rebuild()
                        || !index.refresh(func, &touched))
                {
                    chain_index = None;
                }
                frame_defs = None;
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
            let protected = crate::eh_call_custody::ProtectedCalls::collect(func);
            let def_counts = build_def_counts(func);
            for lp in &loops {
                if hoist_pure_call_clusters(func, lp, &def_counts, dom, &protected) {
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
#[allow(clippy::too_many_arguments)]
fn hoist_loop_invariants(
    func: &mut MachFunction,
    lp: &NaturalLoop,
    dom: &DomTree,
    unwind_exits: &crate::eh_call_custody::UnwindExits,
    def_counts: &HashMap<VReg, usize>,
    def_map: &HashMap<VReg, InstId>,
    layout: &LayoutPositions,
    chain_index: &mut Option<ConstChainIndex>,
    frame_defs: &mut Option<FrameDefSites>,
    frame_speculation: bool,
    touched: &mut Vec<BlockId>,
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

    // An invoke block is not a preheader to hoist into. Its call leaves the
    // block for a landing pad in the middle, and hoisted code goes after every
    // preheader call (`preheader_insert_pos`), so it would not run on that
    // edge although the block dominates the pad. Two readers would then see a
    // register the unwind path never wrote. CSE or GVN can reuse the hoisted
    // def in a pad outside the loop; their mid-block exit rule covers that.
    // When the pad is itself the loop header (a catch-and-retry loop, entered
    // only over exception edges, whose preheader is therefore always an
    // invoke block), the loop reads the hoisted def directly, and only this
    // refusal keeps the O2/O3 code right. Hoisting ahead of the call is no
    // remedy: a load must read memory after the call's writes.
    if unwind_exits.leaves_mid_block(preheader) {
        return false;
    }

    // Build def maps before classifying invariants. Trust Codegen machine IR is not
    // guaranteed to be strict SSA after lowering: block-argument copies and
    // materialization chains can reuse VRegs along different paths. LICM's
    // invariant set is keyed by full VReg identity, so hoisting a multi-def
    // VReg is unsound unless the pass models those path-sensitive definitions.
    // `def_counts` and `def_map` are supplied by the caller and built ONCE per
    // pass run — see `run_with_loop_analysis`.

    // The body's blocks in `block_order` order: every scan of the body below
    // visits them in that order, as filtering `block_order` did.
    let body_blocks = layout.body_blocks_in_layout(func, &lp.body);

    // Build a map: VReg -> (inst_id, block_id) for definitions inside the loop.
    let loop_defs = build_loop_defs(func, &body_blocks);

    // Per-loop memory-write facts drive load admission: whether the loop writes
    // memory at all (tier a vs b), whether any writer is opaque (fails tier b
    // closed), and the classified base of every simple in-loop store.
    let mem_facts =
        compute_loop_memory_facts(func, dom, &body_blocks, def_map, def_counts, frame_defs);

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
    let mut invariant_vregs: HashSet<VReg> = HashSet::default();

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
    // DEPTH POLICY. The tier only ever relocates a chain to a strictly-less-
    // frequent region. At `lp.depth >= 2` (loop is itself nested) that region is
    // STILL inside a loop, the move is close to free, and every chain length is
    // admitted. At `lp.depth == 1` the move is the final "pull out of the
    // OUTERMOST loop" step, which shrinks a single hot loop's body and perturbs
    // downstream passes, so a chain-length FLOOR applies there.
    // `depth` is 1-based (outermost == 1). Deeply-nested kernels (perlin's
    // fade/lerp coefficients, live in the depth-3/4 inner loops) lift across every
    // inner level and out of the hottest loops regardless of that floor.
    //
    // DEPTH-1 FLOOR: chains of >= 3 instructions hoist BY DEFAULT (a
    // 4-instruction 64-bit magic reciprocal rebuilt every iteration is the
    // motivating shape). `TCG_LICM_DEPTH1_MULTI` lowers the floor to >= 2 and
    // stays OPT-IN: a 2-instruction hoist perturbs downstream passes (for
    // example it can suppress an unroll), the sign of the effect is not
    // predicted by instruction count, and the corpus result of floor 2 is
    // within measurement noise. The effect is not fetch alignment; it
    // reproduces with `TCG_NO_LOOP_HEAD_ALIGN=1`. Treat any new depth-1
    // regression as this downstream-perturbation class first, and re-price
    // (`tools/perf_sweep_interleaved.py`) before lowering the floor. The
    // measurements are in commit `90b28b615`.
    let depth1_floor = if crate::env_lock::var_os("TCG_LICM_DEPTH1_MULTI").is_some() {
        2
    } else {
        3
    };
    let chains = {
        let index = chain_index.get_or_insert_with(|| ConstChainIndex::build(func));
        find_hoistable_constant_chains(func, &lp.body, def_counts, index)
    };
    for (carrier, chain) in chains {
        // At depth 1 admit only chains long enough that the removed
        // per-iteration fetches dominate the downstream-pass perturbation the
        // move causes (see DEPTH-1 FLOOR above).
        if lp.depth == 1 && chain.len() < depth1_floor {
            continue;
        }
        invariant_vregs.insert(carrier);
        constant_chains.push((carrier, chain.iter().map(|(id, _)| *id).collect()));
        for site in chain {
            to_hoist.push(site);
        }
    }

    // Iteratively find loop-invariant instructions.
    // Keep iterating until no new invariants are found (transitive closure).
    let mut found_new = true;
    while found_new {
        found_new = false;

        for &block_id in &body_blocks {
            let block = func.block(block_id);
            for (inst_pos, &inst_id) in block.insts.iter().enumerate() {
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
                        is_operand_loop_invariant(op, &loop_defs, &invariant_vregs, def_counts)
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
                        (block_id, inst_pos),
                        inst,
                        preheader_enters_loop,
                        &mem_facts,
                        def_map,
                        def_counts,
                        frame_defs,
                        frame_speculation,
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

    // Hoist instructions to the preheader, each right before its control-
    // transfer tail (`preheader_insert_pos` states the placement rule). The
    // blocks whose instruction lists change are reported to the caller.
    touched.push(preheader);
    for (_, source_block) in &to_hoist {
        if !touched.contains(source_block) {
            touched.push(*source_block);
        }
    }
    for (inst_id, source_block) in &to_hoist {
        // Remove from source block.
        let block = func.block_mut(*source_block);
        block.insts.retain(|id| id != inst_id);

        // Recompute per insertion (immutable borrows) so successive hoists
        // land in discovery order: each before the tail, after its deps.
        let insert_pos = preheader_insert_pos(func, preheader);
        func.block_mut(preheader).insts.insert(insert_pos, *inst_id);
    }

    // X5 value-level nets: ordinary moved values use the single-def check;
    // MOVZ/MOVK materialization carriers are intentionally multi-def and use a
    // separate tied-chain order/consumer check.
    verify_preheader_defs_precede_uses(func, preheader, def_counts);
    verify_preheader_constant_chains(func, preheader, &constant_chains);

    true
}

/// Where an instruction hoisted out of a loop is inserted into its preheader:
/// right before the block's control-transfer tail, after every other
/// instruction of the block.
///
/// Placement is part of LICM's soundness argument, not a layout choice:
///
/// * Every path out of the preheader, including the edge into the loop, must
///   execute the hoisted instruction. Inserting at `len - 1` of a rotated
///   loop's guard preheader (`CmpRR; BCond(cc, header); B exit`) put it
///   between the `BCond` and the `B`, on the loop-skipped path only — a
///   miscompile revmapfuzz found (`x ^ x` rewritten to `MovI 0`, hoisted,
///   sunk below the guard's `BCond`). The tail therefore starts at the FIRST
///   real branch or terminator. An exception edge leaves earlier, at a call:
///   `hoist_loop_invariants` refuses a preheader that holds a call an
///   exception can leave through (an invoke block, `UnwindExits`).
/// * A hoisted load must read memory in the state the loop is entered with:
///   the value-stability tiers of `load_is_admissible` examine in-loop writers
///   only. The insertion point therefore stays after every preheader store and
///   call. It also stays after every mid-block trap guard
///   ([`AArch64Opcode::is_falls_through_trap_pseudo`]: `TrapBoundsCheckExact`
///   and the other carriers that are flagged `IS_BRANCH | IS_TERMINATOR` but
///   fall through to live code in the same block), so a hoisted load never
///   runs before a guard that would trap first, and never before the stores
///   behind that guard. Placing it before such a carrier, or stepping back over
///   a store that ends the preheader, read a stack slot before the preheader
///   wrote it (the dereferenceable-frame tier hoisting `acc += a[2]` above
///   `a[x & 3] = x + 4`: `e2e_aarch64_vec_len_guard_differential`'s
///   preheader-writer rows).
/// * The one instruction the point steps back over is a flag-only compare
///   (no register result, no memory access: `CmpRR`/`CmpRI`/`Tst`/`Fcmp` and
///   their spellings) right before the tail, so hoisted code never sits
///   between a compare and its conditional branch. Hoisted instructions are
///   flag-free today (`is_pure` rejects NZCV writers), so this is defensive.
///   Value-producing flag setters (`AddsRR`) are not stepped over: a hoisted
///   instruction may read their result.
///
/// Every vreg a hoisted instruction reads is defined before this point:
/// preheader defs precede the tail (branches and bare compares define none),
/// loop-external defs dominate the preheader, and earlier-hoisted invariants
/// were inserted at this same position before it.
fn preheader_insert_pos(func: &MachFunction, preheader: BlockId) -> usize {
    let insts = &func.block(preheader).insts;
    let tail = insts
        .iter()
        .position(|&id| {
            let inst = func.inst(id);
            (inst.is_branch() || inst.is_terminator())
                && !inst.opcode.is_falls_through_trap_pseudo()
        })
        .unwrap_or(insts.len());
    let steps_over_compare = tail
        .checked_sub(1)
        .and_then(|prev| insts.get(prev))
        .is_some_and(|&id| {
            let opcode = func.inst(id).opcode;
            writes_flags(opcode) && !produces_value(opcode) && opcode_effect(opcode).is_pure()
        });
    if steps_over_compare { tail - 1 } else { tail }
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
    protected: &crate::eh_call_custody::ProtectedCalls,
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

    let body_blocks: Vec<BlockId> = func
        .block_order
        .iter()
        .copied()
        .filter(|b| lp.body.contains(b))
        .collect();
    let loop_defs = build_loop_defs(func, &body_blocks);
    // v1 does not chain a hoisted cluster's result into a later cluster's
    // invariance, so the invariant seed stays empty: argument sources must be
    // defined OUTSIDE the loop.
    let invariant_vregs: HashSet<VReg> = HashSet::default();

    // Discover clusters in deterministic order (block_order, then ascending
    // in-block index). `claimed` guards against overlapping `InstId` ranges.
    let mut clusters: Vec<Vec<InstId>> = Vec::new();
    let mut claimed: HashSet<InstId> = HashSet::default();
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
                && !protected.contains(iid)
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

    // Insert before the preheader's control-transfer tail (the placement rule
    // of `preheader_insert_pos`, shared with the value-producer splice at the
    // top of this file): every path out of the preheader — including into the
    // loop — executes the cluster after every preheader store, call and trap
    // guard, and a flag-free cluster never lands between a compare and its
    // conditional branch. The hoisted cluster's argument sources are
    // loop-invariant (defined outside the loop), so they dominate the
    // preheader and are defined before this point.
    let insert_pos = preheader_insert_pos(func, preheader);
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

/// Cached `TCG_DUMP_CHAINS` gate.
///
/// PURE DIAGNOSTIC: it selects only whether the chain trace prints. It is read
/// once per natural loop in the hoist driver and once per multi-def carrier in
/// the chain scan, so uncached it was a `getenv` proportional to the function's
/// loop and carrier counts on every compile with the consumer off.
fn dump_chains_enabled() -> bool {
    use std::sync::OnceLock;
    static ENABLED: OnceLock<bool> = OnceLock::new();
    *ENABLED.get_or_init(|| std::env::var_os("TCG_DUMP_CHAINS").is_some())
}

fn build_def_counts(func: &MachFunction) -> HashMap<VReg, usize> {
    let mut counts: HashMap<VReg, usize> = HashMap::default();

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
    body_blocks: &[BlockId],
) -> HashMap<VReg, (InstId, BlockId)> {
    let mut defs: HashMap<VReg, (InstId, BlockId)> = HashMap::default();

    for &block_id in body_blocks {
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
        MachOperand::Imm(_)
        | MachOperand::FImm(_)
        | MachOperand::Symbol(_)
        | MachOperand::ExactModuleSymbol(_) => true,
        _ => false,
    }
}

// ===========================================================================
// Constant-chain hoisting: lift `MOVZ/MOVK` immediate materialization chains
// ===========================================================================

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
///   existing hoists. Behind the depth-1 chain-length floor at the
///   call site (>= 3 instructions by default, >= 2 under
///   `TCG_LICM_DEPTH1_MULTI`), which keeps the documented short-chain
///   "pull out of the OUTERMOST loop" regression class (flops-1/2/7) excluded
///   for integer chains too. That class is downstream-pass perturbation, not
///   fetch alignment — see the DEPTH-1 FLOOR note at the call site.
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
///
/// The loop-INDEPENDENT half of `find_hoistable_constant_chains`, built once
/// per LICM run and shared by every loop of the function: it reads only
/// `block_order`, each block's instruction list and each instruction's
/// opcode/operands, so between two loops that hoisted nothing it is
/// bit-for-bit what a rebuild would produce. A hoist moves instructions
/// (in-block indices change) between the blocks it reports, so after any loop
/// that returned `true` the caller brings the index up to date for exactly
/// those blocks ([`Self::refresh`]); rebuilding it for every such loop made a
/// function with many hoisting loops quadratic in them (L14-P6).
struct ConstChainIndex {
    /// Whole-function def sites of each vreg: (block, index-in-block, inst).
    defs: HashMap<VReg, Vec<(BlockId, usize, InstId)>>,
    /// GPRs consumed by an `FMOV Dn, Xv` (FP-literal chain carriers).
    fmov_gpr_sources: HashSet<VReg>,
    /// Position of each block in `block_order` (stable program order).
    block_pos: HashMap<BlockId, usize>,
}

impl ConstChainIndex {
    fn build(func: &MachFunction) -> Self {
        let mut defs: HashMap<VReg, Vec<(BlockId, usize, InstId)>> = HashMap::default();
        let mut fmov_gpr_sources: HashSet<VReg> = HashSet::default();
        // Position of each block in the (deterministic) `block_order`, so the
        // returned chains can be sorted into a stable program order below — the
        // `defs` HashMap iteration order is nondeterministic and would otherwise
        // leak into which chain lands first in the preheader (a reproducibility
        // break for a verified compiler; cf. LoopAnalysis's BTreeMap rationale).
        let mut block_pos: HashMap<BlockId, usize> = HashMap::default();
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
        Self {
            defs,
            fmov_gpr_sources,
            block_pos,
        }
    }

    /// Make the index what [`Self::build`] would build now, after a hoist
    /// that moved instructions only between the blocks in `touched` (the
    /// preheader and the loop's source blocks). `false` when this cannot be
    /// done exactly (a block appears twice in `block_order`, or a touched
    /// block is not in it); the caller then drops the index.
    ///
    /// The instructions inside `touched` are the same before and after such a
    /// hoist, only their blocks and positions differ, so the def sites to
    /// replace are exactly those of the vregs defined in `touched` now, and
    /// the FMOV sources (a set over all instructions of the layout) and the
    /// block positions do not change. Each touched vreg's sites are rebuilt
    /// from the touched blocks' current lists and put back in (layout
    /// position, index) order, the order `build` records them in.
    fn refresh(&mut self, func: &MachFunction, touched: &[BlockId]) -> bool {
        if self.block_pos.len() != func.block_order.len()
            || touched.iter().any(|b| !self.block_pos.contains_key(b))
        {
            return false;
        }
        let touched_set: HashSet<BlockId> = touched.iter().copied().collect();
        let mut fresh: HashMap<VReg, Vec<(BlockId, usize, InstId)>> = HashMap::default();
        for &block_id in touched {
            for (idx, &inst_id) in func.block(block_id).insts.iter().enumerate() {
                for_each_inst_def(func.inst(inst_id), |def| {
                    fresh.entry(def).or_default().push((block_id, idx, inst_id));
                });
            }
        }
        for (vreg, sites) in fresh {
            let entry = self.defs.entry(vreg).or_default();
            entry.retain(|(block_id, _, _)| !touched_set.contains(block_id));
            entry.extend(sites);
            let block_pos = &self.block_pos;
            entry.sort_by_key(|&(block_id, idx, _)| (block_pos[&block_id], idx));
        }
        true
    }
}

#[cfg(test)]
thread_local! {
    /// Tests set this to drop the constant-chain index after every hoisting
    /// loop (the per-loop rebuild `ConstChainIndex::refresh` replaces).
    static FORCE_CHAIN_INDEX_REBUILD: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

fn force_chain_index_rebuild() -> bool {
    #[cfg(test)]
    return FORCE_CHAIN_INDEX_REBUILD.with(std::cell::Cell::get);
    #[cfg(not(test))]
    false
}

/// Each block's position in `block_order` (`None` when a block appears there
/// twice), built by the second [`Self::body_blocks_in_layout`] question: a
/// function with one loop pays only the literal filter, as it did before.
struct LayoutPositions {
    positions: std::cell::OnceCell<Option<HashMap<BlockId, usize>>>,
    literal_answers: std::cell::Cell<u32>,
}

impl LayoutPositions {
    fn new() -> Self {
        Self {
            positions: std::cell::OnceCell::new(),
            literal_answers: std::cell::Cell::new(0),
        }
    }

    fn of(func: &MachFunction) -> Option<HashMap<BlockId, usize>> {
        let mut positions: HashMap<BlockId, usize> = HashMap::default();
        for (position, &block_id) in func.block_order.iter().enumerate() {
            if positions.insert(block_id, position).is_some() {
                return None;
            }
        }
        Some(positions)
    }

    /// `block_order` filtered by membership in `body`: sorted from the
    /// positions when the layout lists each block once, the literal filter
    /// for the first question and when a block is listed twice.
    fn body_blocks_in_layout(&self, func: &MachFunction, body: &HashSet<BlockId>) -> Vec<BlockId> {
        let literal = || {
            func.block_order
                .iter()
                .copied()
                .filter(|b| body.contains(b))
                .collect()
        };
        if self.positions.get().is_none() && self.literal_answers.get() == 0 {
            self.literal_answers.set(1);
            return literal();
        }
        let Some(positions) = self.positions.get_or_init(|| Self::of(func)) else {
            return literal();
        };
        let mut blocks: Vec<(usize, BlockId)> = body
            .iter()
            .filter_map(|b| positions.get(b).map(|&position| (position, *b)))
            .collect();
        blocks.sort_unstable();
        blocks.into_iter().map(|(_, b)| b).collect()
    }
}

fn find_hoistable_constant_chains(
    func: &MachFunction,
    body: &HashSet<BlockId>,
    def_counts: &HashMap<VReg, usize>,
    index: &ConstChainIndex,
) -> Vec<(VReg, Vec<(InstId, BlockId)>)> {
    // Whole-function def sites of each vreg: (block, index-in-block, inst).
    // Function-wide (not body-restricted) so a def OUTSIDE the loop
    // disqualifies the carrier — we must account for every definition.
    // Simultaneously collect the set of GPRs consumed by an `FMOV Dn, Xv`;
    // such carriers are FP-literal chains, admitted at any length (the
    // integer class needs >= 2 defs — see the scope note above).
    let ConstChainIndex {
        defs,
        fmov_gpr_sources,
        block_pos,
    } = index;
    type ConstantChain = ((usize, usize), VReg, Vec<(InstId, BlockId)>);

    // DIAGNOSTIC (default off, TCG_DUMP_CHAINS=1): why each multi-def carrier
    // was declined. Only multi-def carriers are reported — single-def vregs are
    // the overwhelming majority and are not chain candidates.
    let dump = dump_chains_enabled();
    let mut chains: Vec<ConstantChain> = Vec::new();
    for (&carrier, sites) in defs.iter() {
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
        if !(fmov_gpr_sources.contains(&carrier) || sites.len() >= 2) {
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
            if dump_chains_enabled() && sites.len() >= 2 {
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
    /// A complete access inside a real fixed slot, through a direct reaching
    /// `AddPCRel dst, SP, StackSlot` definition. Frame layout places distinct
    /// positive-sized fixed slots separately; an unbounded offset is not one.
    Stack(StackSlotId),
    /// Anything we cannot prove — an arbitrary pointer. Fails disjointness.
    Unknown,
}

/// Classify only a complete, bounded direct-frame access. Symbol spellings do
/// not bind link-time object identity or size, and ADRP supplies only a page.
/// Copies, pointer/integer casts and arithmetic get no new alias permission.
fn classify_addr_base(
    func: &MachFunction,
    dom: &DomTree,
    at: (BlockId, usize),
    access: &MachInst,
    def_map: &HashMap<VReg, InstId>,
    def_counts: &HashMap<VReg, usize>,
    frame_defs: &mut Option<FrameDefSites>,
) -> AddrBase {
    if access.flags != access.opcode.default_flags()
        || !access.implicit_defs.is_empty()
        || !access.implicit_uses.is_empty()
    {
        return AddrBase::Unknown;
    }
    let [
        MachOperand::VReg(_),
        MachOperand::VReg(base),
        MachOperand::Imm(off),
    ] = access.operands.as_slice()
    else {
        return AddrBase::Unknown;
    };
    if base.class != RegClass::Gpr64
        || base.id >= func.next_vreg
        || def_counts.get(base).copied() != Some(1)
    {
        return AddrBase::Unknown;
    }
    let Some(&def_inst) = def_map.get(base) else {
        return AddrBase::Unknown;
    };
    let inst = func.inst(def_inst);
    if inst.opcode != AArch64Opcode::AddPCRel
        || inst.flags != inst.opcode.default_flags()
        || !inst.implicit_defs.is_empty()
        || !inst.implicit_uses.is_empty()
        || !matches!(inst.operands.as_slice(),
            [MachOperand::VReg(dst), sp, MachOperand::StackSlot(_)]
                if dst == base && is_stack_pointer(sp))
    {
        return AddrBase::Unknown;
    }
    let width = plain_load_width(access).or_else(|| plain_store_width(access));
    let Some(width) = width else {
        return AddrBase::Unknown;
    };
    let sites = frame_defs.get_or_insert_with(|| FrameDefSites::build(func));
    // The older frame-speculation resolver remains unchanged; ONLY this new
    // tier checks numeric W/X definition aliases in addition to typed sites.
    if sites.numeric_definition_count(func, base.id) != 1 {
        return AddrBase::Unknown;
    }
    let Some((slot, base_off)) = resolve_frame_address(func, dom, sites, *base, at, 1) else {
        return AddrBase::Unknown;
    };
    let Some(info) = func.stack_slots.get(slot.0 as usize) else {
        return AddrBase::Unknown;
    };
    if !info.align.is_power_of_two()
        || i32::try_from(info.size).is_err()
        || i32::try_from(info.align).is_err()
    {
        return AddrBase::Unknown;
    }
    let Some(start) = base_off.checked_add(*off) else {
        return AddrBase::Unknown;
    };
    if fixed_frame_interval_in_bounds(func, slot, start, width) {
        AddrBase::Stack(slot)
    } else {
        AddrBase::Unknown
    }
}

/// Returns true when a load from `load` provably cannot alias a store to
/// `store`. Only rock-solid facts admit; anything `Unknown` refuses.
fn addr_bases_disjoint(load: &AddrBase, store: &AddrBase) -> bool {
    match (load, store) {
        (AddrBase::Unknown, _) | (_, AddrBase::Unknown) => false,
        // Distinct stack slots are distinct frame allocations.
        (AddrBase::Stack(a), AddrBase::Stack(b)) => a != b,
    }
}

/// Per-loop memory-write summary consumed by [`load_is_admissible`].
struct LoopMemFacts {
    /// Any body instruction writes memory / calls / is a barrier, or is a
    /// load-acquire (after which this thread may observe other threads'
    /// writes).
    writes_memory: bool,
    /// Some memory writer is not a simple, classifiable base+immediate store
    /// (a call, barrier, atomic, store-pair, writeback store, load-acquire,
    /// …). When set, tier (b) admits nothing: we cannot bound what the loop
    /// clobbers.
    opaque_writer: bool,
    /// Classified base of every simple in-loop store (only meaningful when
    /// `opaque_writer` is false).
    store_bases: Vec<AddrBase>,
}

/// Summarize the memory writes of a loop body in one pass.
fn compute_loop_memory_facts(
    func: &MachFunction,
    dom: &DomTree,
    body_blocks: &[BlockId],
    def_map: &HashMap<VReg, InstId>,
    def_counts: &HashMap<VReg, usize>,
    frame_defs: &mut Option<FrameDefSites>,
) -> LoopMemFacts {
    let mut writes_memory = false;
    let mut store_bases: Vec<AddrBase> = Vec::new();
    // This summary has one consumer: load admission. One opaque or unknown
    // writer makes every tier-(b) load impossible; no later writer can restore
    // permission. Drop partial rows, but keep any shared frame cache intact.
    // The separate instruction-motion scan still visits the complete body.
    let opaque = || LoopMemFacts {
        writes_memory: true,
        opaque_writer: true,
        store_bases: Vec::new(),
    };

    for &block_id in body_blocks {
        for (pos, &inst_id) in func.block(block_id).insts.iter().enumerate() {
            let inst = func.inst(inst_id);
            // A load-acquire writes nothing (effect class `Load`), yet once it
            // reads a value a release wrote, this thread may observe every
            // write another thread made before that release. A plain load
            // hoisted to the preheader reads before every in-loop acquire, so
            // no store base can bound what the acquire makes visible.
            if is_load_acquire(inst.opcode) {
                return opaque();
            }
            let eff = opcode_effect(inst.opcode);
            // `writes_memory()` already covers stores, calls and barriers
            // (all `MemoryEffect::Call`); `is_barrier()` is included for
            // explicitness.
            if eff.writes_memory() || eff.is_barrier() {
                writes_memory = true;
                if simple_store_base(inst).is_none() {
                    return opaque();
                }
                let base = classify_addr_base(
                    func,
                    dom,
                    (block_id, pos),
                    inst,
                    def_map,
                    def_counts,
                    frame_defs,
                );
                if matches!(base, AddrBase::Unknown) {
                    return opaque();
                }
                store_bases.push(base);
            }
        }
    }

    LoopMemFacts {
        writes_memory,
        opaque_writer: false,
        store_bases,
    }
}

/// The classic LICM "guaranteed to execute" (a.k.a. must-execute) test for a
/// candidate load at `load_pos` in `load_block`: the first iteration of every
/// entry into the loop reaches the load, so hoisting it to the preheader
/// introduces no fault that the original program did not already have.
///
/// Four conditions:
/// - **Its block dominates EVERY latch** — i.e. every back-edge source, not
///   merely the one `lp.latch` happens to cache. The load then runs on every
///   complete iteration (which is also what rules out a load buried in a
///   conditional inside an infinite loop with no exiting block, where the exit
///   test below is vacuous).
/// - **Its block dominates every loop-exiting block** — the load runs before
///   control can leave the loop, so it is not skipped on an early-exit path.
/// - **Nothing the first iteration runs before it can stop it.** Dominance is
///   block-granular and sees only CFG edges, but the first iteration can stop
///   before the load inside a block: at an earlier branch in the load's own
///   block (`select_assert`'s mid-block `b.eq trap`), or at an instruction
///   that ends the program or leaves the loop with no CFG edge
///   ([`stops_without_cfg_edge`]: a guard carrier such as
///   `TrapBoundsCheckExact`) anywhere in the load's block before it or in a
///   loop block the header reaches without passing through the load's block.
///   Hoisting past such a stop turns a program that trapped (`BRK`) before the
///   load into one that faults on the hoisted load. The blocks before the
///   load's block need no branch check: a CFG exit from one of them already
///   fails the dominance condition above.
/// - **Nothing the first iteration runs before it can spin.** The blocks the
///   header reaches without passing through the load's block
///   ([`blocks_before_first_reaching`]) contain no cycle. A cycle there is an
///   inner loop, reducible or not, that the first iteration can enter before
///   the load and may never leave. Rust and trust-ir do not assume forward
///   progress, so that non-termination is the program's behavior, and hoisting
///   the load turns it into a fault. Dominance cannot see such a cycle: it
///   neither leaves the loop nor returns to the header, so it adds no exiting
///   block and no latch. Without a cycle every path from the header through
///   those blocks is finite, and since none of them is a latch or an exiting
///   block (each is reached avoiding the load's block, which dominates all of
///   those), it ends by entering the load's block.
///
/// The caller separately requires the preheader to unconditionally enter the
/// loop. Together: whenever the preheader executes, the original program's
/// first iteration reaches the load, unless an earlier memory access of that
/// iteration faults first, in which case the hoisted program faults on the
/// hoisted load instead.
///
/// This is the one must-execute test for loads: LICM's guaranteed tier and
/// alias-versioned load hoisting ([`crate::alias_hoist`]) both call it.
pub(crate) fn load_guaranteed_to_execute(
    func: &MachFunction,
    dom: &DomTree,
    lp: &NaturalLoop,
    (load_block, load_pos): (BlockId, usize),
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
    // The load's block before the load: any branch, terminator or stop.
    let before_load = func.block(load_block).insts.iter().take(load_pos);
    if before_load
        .map(|&id| func.inst(id))
        .any(|inst| inst.is_branch() || inst.is_terminator() || stops_without_cfg_edge(inst))
    {
        return false;
    }
    // Every loop block the header reaches without passing through the load's
    // block (none when the load is in the header): no cycle, and no stop.
    let Some(before_block) = blocks_before_first_reaching(func, lp, load_block) else {
        return false;
    };
    !before_block.iter().any(|&b| {
        func.block(b)
            .insts
            .iter()
            .any(|&id| stops_without_cfg_edge(func.inst(id)))
    })
}

/// Whether `inst` can end the program or leave the loop without a CFG edge,
/// so that the dominance conditions of [`load_guaranteed_to_execute`] cannot
/// see it:
/// - every `Trap*` guard carrier ([`AArch64Opcode::is_trap_pseudo`]). The
///   falls-through ones (`TrapBoundsCheckExact`, `TrapNullIfZero`, ...) trap
///   only when their condition holds and continue to live code in the same
///   block; none of them adds a successor.
/// - `BRK`, which is flagged `HAS_SIDE_EFFECTS` only, not as a terminator.
/// - a call, which need not return. Both callers of
///   [`load_guaranteed_to_execute`] already refuse every loop that calls (the
///   value-stability tiers of [`load_is_admissible`], and alias hoisting's
///   store bounding); this keeps the must-execute argument from depending on
///   that.
fn stops_without_cfg_edge(inst: &MachInst) -> bool {
    inst.opcode.is_trap_pseudo() || inst.opcode == AArch64Opcode::Brk || inst.is_call()
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
    (load_block, load_pos): (BlockId, usize),
    inst: &MachInst,
    preheader_enters_loop: bool,
    mem_facts: &LoopMemFacts,
    def_map: &HashMap<VReg, InstId>,
    def_counts: &HashMap<VReg, usize>,
    frame_defs: &mut Option<FrameDefSites>,
    frame_speculation: bool,
) -> bool {
    // (1) Speculation guard — do not introduce a fault on a zero-trip or
    // early-exit path. Either the load runs on every entry into the loop, or
    // it reads inside one fixed-size stack slot and so cannot fault wherever
    // it executes (only when frame speculation is enabled).
    let guaranteed =
        preheader_enters_loop && load_guaranteed_to_execute(func, dom, lp, (load_block, load_pos));
    if !guaranteed {
        if !frame_speculation {
            return false;
        }
        let sites = frame_defs.get_or_insert_with(|| FrameDefSites::build(func));
        if !frame_access_in_bounds(func, dom, sites, (load_block, load_pos), inst) {
            return false;
        }
    }

    // (2a) Tier (a): a loop that never writes memory (no stores, no calls, no
    // barriers, no load-acquires) cannot clobber the invariant address, so
    // the load is stable.
    if !mem_facts.writes_memory {
        return true;
    }

    // (2b) Tier (b): the loop writes memory. Admit only if every writer is a
    // simple store we could classify AND each is provably disjoint from the
    // load's own (classifiable) address.
    if mem_facts.opaque_writer {
        return false;
    }
    let load_base = classify_addr_base(
        func,
        dom,
        (load_block, load_pos),
        inst,
        def_map,
        def_counts,
        frame_defs,
    );
    if matches!(load_base, AddrBase::Unknown) {
        return false;
    }
    mem_facts
        .store_bases
        .iter()
        .all(|store_base| addr_bases_disjoint(&load_base, store_base))
}

/// Every definition site `(block, position, inst)` of every VReg, in block
/// order. Built lazily and reused until a hoist changes instruction positions.
struct FrameDefSites {
    sites: HashMap<VReg, Vec<(BlockId, usize, InstId)>>,
    /// All stored definition references, including other W/X views and blocks
    /// outside layout. Used ONLY by the direct-slot tier-(b) admission.
    numeric_counts: Option<HashMap<u32, usize>>,
}

impl FrameDefSites {
    fn build(func: &MachFunction) -> Self {
        let mut sites: HashMap<VReg, Vec<(BlockId, usize, InstId)>> = HashMap::default();
        for &block_id in &func.block_order {
            for (pos, &inst_id) in func.block(block_id).insts.iter().enumerate() {
                for_each_inst_def(func.inst(inst_id), |def| {
                    sites.entry(def).or_default().push((block_id, pos, inst_id));
                });
            }
        }
        Self {
            sites,
            numeric_counts: None,
        }
    }

    fn numeric_definition_count(&mut self, func: &MachFunction, id: u32) -> usize {
        let counts = self.numeric_counts.get_or_insert_with(|| {
            let mut counts = HashMap::default();
            for block in &func.blocks {
                for &inst in &block.insts {
                    for_each_inst_def(func.inst(inst), |def| {
                        *counts.entry(def.id).or_default() += 1;
                    });
                }
            }
            counts
        });
        counts.get(&id).copied().unwrap_or(0)
    }
}

/// Most copy / immediate-offset links [`resolve_frame_address`] follows.
const FRAME_ADDRESS_FUEL: u32 = 8;

/// Bytes a plain hoistable load reads, or `None` for a shape this rule does
/// not model (the width of an `LdrRI` is its destination register's).
fn plain_load_width(inst: &MachInst) -> Option<i64> {
    match inst.opcode {
        AArch64Opcode::LdrbRI | AArch64Opcode::LdrsbRI => Some(1),
        AArch64Opcode::LdrhRI | AArch64Opcode::LdrshRI => Some(2),
        AArch64Opcode::LdrRI => match inst.operands.first() {
            Some(MachOperand::VReg(dst)) => match dst.class {
                RegClass::Gpr64
                | RegClass::Gpr32
                | RegClass::Fpr128
                | RegClass::Fpr64
                | RegClass::Fpr32
                | RegClass::Fpr16
                | RegClass::Fpr8 => Some(i64::from(dst.class.size_bytes())),
                RegClass::System => None,
            },
            _ => None,
        },
        _ => None,
    }
}

/// Bytes a simple scalar store writes, using the opcode's narrow width or
/// its value carrier's width exactly as the ordinary memory lowering does.
fn plain_store_width(inst: &MachInst) -> Option<i64> {
    match inst.opcode {
        AArch64Opcode::StrbRI => Some(1),
        AArch64Opcode::StrhRI => Some(2),
        AArch64Opcode::StrRI => match inst.operands.first() {
            Some(MachOperand::VReg(src)) if src.class != RegClass::System => {
                Some(i64::from(src.class.size_bytes()))
            }
            _ => None,
        },
        _ => None,
    }
}

/// The stack pointer, in either operand spelling (`PReg` 31 or `Special(SP)`).
fn is_stack_pointer(op: &MachOperand) -> bool {
    match op {
        MachOperand::PReg(p) => *p == trust_cg_ir::regs::SP,
        MachOperand::Special(s) => *s == trust_cg_ir::SpecialReg::SP,
        _ => false,
    }
}

/// `MovR v, v` / `Copy v, v`: a definition that never changes `v`.
fn is_self_copy(inst: &MachInst, v: VReg) -> bool {
    matches!(inst.opcode, AArch64Opcode::MovR | AArch64Opcode::Copy)
        && matches!(
            inst.operands.as_slice(),
            [MachOperand::VReg(d), MachOperand::VReg(s)] if *d == v && *s == v
        )
}

/// The one definition of `v` that can change its value, when it reaches the use
/// at `(use_block, use_pos)` on every path: every other definition of `v` is a
/// self-copy, and this one lies in a block that strictly dominates `use_block`
/// or earlier in `use_block`. `None` for a register with no definition (a
/// parameter), two value-changing definitions, or one that does not reach.
fn reaching_value_def(
    func: &MachFunction,
    dom: &DomTree,
    sites: &FrameDefSites,
    v: VReg,
    (use_block, use_pos): (BlockId, usize),
) -> Option<(BlockId, usize, InstId)> {
    let mut changing = sites
        .sites
        .get(&v)?
        .iter()
        .filter(|&&(_, _, id)| !is_self_copy(func.inst(id), v));
    let &(def_block, def_pos, def_id) = changing.next()?;
    if changing.next().is_some() {
        return None;
    }
    let reaches_use = if def_block == use_block {
        def_pos < use_pos
    } else {
        dom.dominates(def_block, use_block)
    };
    reaches_use.then_some((def_block, def_pos, def_id))
}

/// The constant `v` holds at the use, when its reaching value definition is a
/// plain `Movz dst, #imm` (no shift) or `MovI dst, #imm`.
fn frame_offset_constant(
    func: &MachFunction,
    dom: &DomTree,
    sites: &FrameDefSites,
    v: VReg,
    at: (BlockId, usize),
) -> Option<i64> {
    let (_, _, def_id) = reaching_value_def(func, dom, sites, v, at)?;
    let def = func.inst(def_id);
    match (def.opcode, def.operands.as_slice()) {
        (
            AArch64Opcode::Movz | AArch64Opcode::MovI,
            [MachOperand::VReg(d), MachOperand::Imm(c)],
        ) if *d == v => Some(*c),
        _ => None,
    }
}

/// Resolve the value `v` holds at `at = (use_block, use_pos)` to a stack slot
/// and a byte offset from its start, or `None` when that is not provable.
///
/// The value comes from its [`reaching_value_def`], which must be the slot
/// address itself (`AddPCRel dst, SP, StackSlot`), a full-width copy of a
/// resolvable register, `AddRI` / `SubRI` of one with an immediate, `AddRR`
/// of one with a constant register, or `Madd dst, x, y, base` (a
/// constant-index GEP) of one with `x` and `y` constants
/// ([`frame_offset_constant`]). Anything else (a loaded pointer, a call
/// result, a parameter, other register arithmetic) is unresolved.
fn resolve_frame_address(
    func: &MachFunction,
    dom: &DomTree,
    sites: &FrameDefSites,
    v: VReg,
    at: (BlockId, usize),
    fuel: u32,
) -> Option<(StackSlotId, i64)> {
    if fuel == 0 || v.class != RegClass::Gpr64 {
        return None;
    }
    let (def_block, def_pos, def_id) = reaching_value_def(func, dom, sites, v, at)?;
    let def = func.inst(def_id);
    let at_def = (def_block, def_pos);
    match (def.opcode, def.operands.as_slice()) {
        (AArch64Opcode::AddPCRel, [MachOperand::VReg(d), base, MachOperand::StackSlot(slot)])
            if *d == v && is_stack_pointer(base) =>
        {
            Some((*slot, 0))
        }
        (
            AArch64Opcode::MovR | AArch64Opcode::Copy,
            [MachOperand::VReg(d), MachOperand::VReg(src)],
        ) if *d == v => resolve_frame_address(func, dom, sites, *src, at_def, fuel - 1),
        (
            AArch64Opcode::AddRI,
            [
                MachOperand::VReg(d),
                MachOperand::VReg(src),
                MachOperand::Imm(k),
            ],
        ) if *d == v => {
            let (slot, off) = resolve_frame_address(func, dom, sites, *src, at_def, fuel - 1)?;
            Some((slot, off.checked_add(*k)?))
        }
        (
            AArch64Opcode::SubRI,
            [
                MachOperand::VReg(d),
                MachOperand::VReg(src),
                MachOperand::Imm(k),
            ],
        ) if *d == v => {
            let (slot, off) = resolve_frame_address(func, dom, sites, *src, at_def, fuel - 1)?;
            Some((slot, off.checked_sub(*k)?))
        }
        (
            AArch64Opcode::Madd,
            [
                MachOperand::VReg(d),
                MachOperand::VReg(x),
                MachOperand::VReg(y),
                MachOperand::VReg(src),
            ],
        ) if *d == v => {
            let x = frame_offset_constant(func, dom, sites, *x, at_def)?;
            let y = frame_offset_constant(func, dom, sites, *y, at_def)?;
            let (slot, off) = resolve_frame_address(func, dom, sites, *src, at_def, fuel - 1)?;
            Some((slot, off.checked_add(x.checked_mul(y)?)?))
        }
        // `AddRR dst, a, b` with one side a resolvable slot address and the
        // other a constant register: the `AddRI` case after GVN/CSE has
        // replaced the immediate by an equal constant already in a register
        // (the field address `&vec.ptr = slot + 8` beside `MovZ 8`).
        (
            AArch64Opcode::AddRR,
            [
                MachOperand::VReg(d),
                MachOperand::VReg(a),
                MachOperand::VReg(b),
            ],
        ) if *d == v => {
            let (base, k) = match frame_offset_constant(func, dom, sites, *b, at_def) {
                Some(k) => (*a, k),
                None => (*b, frame_offset_constant(func, dom, sites, *a, at_def)?),
            };
            let (slot, off) = resolve_frame_address(func, dom, sites, base, at_def, fuel - 1)?;
            Some((slot, off.checked_add(k)?))
        }
        _ => None,
    }
}

/// Whether the plain load `inst` at `(block, pos)` reads only bytes inside one
/// fixed-size stack slot, so executing it anywhere in this activation cannot
/// fault. The access `[start, start + width)`, `start = base + off`, must
/// satisfy `0 <= start` and `start + width <= slot.size` for the slot the base
/// resolves to.
fn frame_access_in_bounds(
    func: &MachFunction,
    dom: &DomTree,
    sites: &FrameDefSites,
    at: (BlockId, usize),
    inst: &MachInst,
) -> bool {
    let Some(width) = plain_load_width(inst) else {
        return false;
    };
    let (base, off) = match inst.operands.as_slice() {
        [
            MachOperand::VReg(_),
            MachOperand::VReg(base),
            MachOperand::Imm(off),
        ] => (*base, *off),
        _ => return false,
    };
    let Some((slot, base_off)) =
        resolve_frame_address(func, dom, sites, base, at, FRAME_ADDRESS_FUEL)
    else {
        return false;
    };
    let Some(start) = base_off.checked_add(off) else {
        return false;
    };
    fixed_frame_interval_in_bounds(func, slot, start, width)
}

/// Shared interval check for the existing frame-speculation path and the
/// direct-slot alias tier. Distinct-slot permission also checks frame layout
/// size/alignment domains and direct reaching address custody above.
fn fixed_frame_interval_in_bounds(
    func: &MachFunction,
    slot: StackSlotId,
    start: i64,
    width: i64,
) -> bool {
    let Some(info) = usize::try_from(slot.0)
        .ok()
        .and_then(|i| func.stack_slots.get(i))
    else {
        return false;
    };
    if info.allocation != StackSlotAllocationKind::Fixed || info.size == 0 {
        return false;
    }
    let Some(end) = start.checked_add(width) else {
        return false;
    };
    start >= 0 && end <= i64::from(info.size)
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
    let mut untrusted: HashSet<VReg> = HashSet::default();
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

    let mut vals: HashMap<VReg, i64> = HashMap::default();
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
    let mut seen: HashSet<BlockId> = HashSet::default();
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
    let mut def_pos: HashMap<VReg, usize> = HashMap::default();
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
        let mut exits: HashSet<BlockId> = HashSet::default();
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
        let mut inner_defs: HashSet<VReg> = HashSet::default();
        for &b in &inner.body {
            for &iid in &func.block(b).insts {
                for_each_inst_def(func.inst(iid), |d| {
                    inner_defs.insert(d);
                });
            }
        }
        let mut inner_reads: HashSet<VReg> = HashSet::default();
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
        let mut ip_def_idx: HashMap<VReg, usize> = HashMap::default();
        for (idx, &iid) in ip_insts.iter().enumerate() {
            for_each_inst_def(func.inst(iid), |d| {
                ip_def_idx.entry(d).or_insert(idx);
            });
        }
        // Seed: `ip` defs of a vreg the inner body reads or carries (redefines).
        let mut init_set: HashSet<usize> = HashSet::default();
        let mut init_defs: HashSet<VReg> = HashSet::default();
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

        let mut licm = LoopInvariantCodeMotion::new();
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

    /// `make_loop_with_invariant` whose preheader `bb0` ends in an invoke's
    /// call, `bl may_throw`, before its `b bb1`. With `invoke`, the call's
    /// exception edge leaves bb0 for the landing pad `bb3`, as instruction
    /// selection lowers `Invoke` whose normal destination is a loop header.
    fn make_invoke_preheader_loop(invoke: bool) -> (MachFunction, InstId, InstId) {
        let mut func = make_loop_with_invariant();
        let bb0 = func.entry;
        let pad = func.create_block();
        let pad_ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(pad, pad_ret);
        let call = func.push_inst(MachInst::new(
            AArch64Opcode::Bl,
            vec![MachOperand::Symbol("may_throw".into())],
        ));
        let tail = func.block(bb0).insts.len() - 1;
        func.block_mut(bb0).insts.insert(tail, call);
        if invoke {
            crate::eh_call_custody::tests::bind_invoke(&mut func, call, bb0, pad);
        }
        let invariant = func.block(BlockId(1)).insts[0];
        (func, call, invariant)
    }

    #[test]
    fn test_licm_does_not_hoist_into_an_invoke_block() {
        // Hoisted code goes after every preheader call, so in an invoke block
        // it would not run on the exception edge although the block dominates
        // the landing pad; CSE/GVN then reused such a hoisted constant in the
        // pad (an O3 wrong value). The invoke block is refused as preheader.
        let (mut func, _, invariant) = make_invoke_preheader_loop(true);
        let mut licm = LoopInvariantCodeMotion::new();
        assert!(
            !licm.run(&mut func),
            "LICM hoisted into a preheader whose call an exception leaves through"
        );
        assert!(func.block(BlockId(1)).insts.contains(&invariant));

        // Control: the same preheader without the exception edge hoists the
        // invariant, after the call, so the refusal above is the invoke's.
        let (mut func, call, invariant) = make_invoke_preheader_loop(false);
        assert!(LoopInvariantCodeMotion::new().run(&mut func));
        let preheader = &func.block(func.entry).insts;
        let at = |id| preheader.iter().position(|&x| x == id);
        assert!(at(call).unwrap() < at(invariant).expect("hoisted into the preheader"));
    }

    /// A catch-and-retry loop whose header is the landing pad `bb2`. A pad is
    /// entered only over exception edges, so the loop's one outside
    /// predecessor, its preheader, is the invoke block `bb0`; the latch `bb3`
    /// re-enters the pad through a second invoke's exception edge:
    ///
    /// ```text
    ///   bb0: v0 = 10; v1 = 20; bl may_throw; b bb1   (unwind -> bb2)
    ///   bb1: ret                                     (normal destination)
    ///   bb2: v2 = v0 + v1; b.cond bb4, bb3           (pad, loop header)
    ///   bb3: bl may_throw; b bb1                     (unwind -> bb2)
    ///   bb4: ret
    /// ```
    ///
    /// Without `invoke` the same CFG carries no EH rows. Returns the function,
    /// bb0's call and the invariant `v2 = v0 + v1`.
    fn make_pad_headed_retry_loop(invoke: bool) -> (MachFunction, InstId, InstId) {
        let mut func =
            MachFunction::new("licm_pad_loop".to_string(), Signature::new(vec![], vec![]));
        let bb0 = func.entry;
        let bb1 = func.create_block();
        let bb2 = func.create_block();
        let bb3 = func.create_block();
        let bb4 = func.create_block();
        let push = |func: &mut MachFunction,
                    block: BlockId,
                    opcode: AArch64Opcode,
                    operands: Vec<MachOperand>| {
            let id = func.push_inst(MachInst::new(opcode, operands));
            func.append_inst(block, id);
            id
        };
        let call = |name: &str| vec![MachOperand::Symbol(name.into())];

        push(&mut func, bb0, AArch64Opcode::MovI, vec![vreg(0), imm(10)]);
        push(&mut func, bb0, AArch64Opcode::MovI, vec![vreg(1), imm(20)]);
        let entry_call = push(&mut func, bb0, AArch64Opcode::Bl, call("may_throw"));
        push(
            &mut func,
            bb0,
            AArch64Opcode::B,
            vec![MachOperand::Block(bb1)],
        );
        push(&mut func, bb1, AArch64Opcode::Ret, vec![]);
        let invariant = push(
            &mut func,
            bb2,
            AArch64Opcode::AddRR,
            vec![vreg(2), vreg(0), vreg(1)],
        );
        push(
            &mut func,
            bb2,
            AArch64Opcode::BCond,
            vec![MachOperand::Block(bb4), MachOperand::Block(bb3)],
        );
        let retry_call = push(&mut func, bb3, AArch64Opcode::Bl, call("may_throw"));
        push(
            &mut func,
            bb3,
            AArch64Opcode::B,
            vec![MachOperand::Block(bb1)],
        );
        push(&mut func, bb4, AArch64Opcode::Ret, vec![]);

        func.add_edge(bb0, bb1);
        func.add_edge(bb2, bb4);
        func.add_edge(bb2, bb3);
        func.add_edge(bb3, bb1);
        if invoke {
            crate::eh_call_custody::tests::bind_invoke(&mut func, entry_call, bb0, bb2);
            crate::eh_call_custody::tests::bind_invoke(&mut func, retry_call, bb3, bb2);
        } else {
            func.add_edge(bb0, bb2);
            func.add_edge(bb3, bb2);
        }
        (func, entry_call, invariant)
    }

    #[test]
    fn test_licm_does_not_hoist_into_the_invoke_block_of_a_pad_headed_loop() {
        // The loop reads what is hoisted into bb0 directly over the exception
        // edge, with no CSE or GVN reuse in between, so this refusal alone
        // keeps the pad from reading a register the unwind path never wrote
        // (e2e: `eh_pad_reads_its_own_constant_as_the_header_of_a_retry_loop`).
        let (mut func, _, invariant) = make_pad_headed_retry_loop(true);
        let dom = DomTree::compute(&func);
        let loops = LoopAnalysis::compute(&func, &dom);
        let lp = loops.get_loop(BlockId(2)).expect("the pad heads a loop");
        assert_eq!(
            lp.preheader,
            Some(func.entry),
            "its preheader is the invoke block"
        );
        assert!(
            !LoopInvariantCodeMotion::new().run(&mut func),
            "LICM hoisted into the invoke block that preheads a landing-pad loop"
        );
        assert!(func.block(BlockId(2)).insts.contains(&invariant));

        // Control: the same CFG without the exception edges hoists the
        // invariant after the call, so the refusal above is the invoke's.
        let (mut func, call, invariant) = make_pad_headed_retry_loop(false);
        assert!(LoopInvariantCodeMotion::new().run(&mut func));
        let preheader = &func.block(func.entry).insts;
        let at = |id| preheader.iter().position(|&x| x == id);
        assert!(at(call).unwrap() < at(invariant).expect("hoisted into the preheader"));
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

        let mut licm = LoopInvariantCodeMotion::new();
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

        let mut licm = LoopInvariantCodeMotion::new();
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

        let mut licm = LoopInvariantCodeMotion::new();
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

        let mut licm = LoopInvariantCodeMotion::new();
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

        let mut licm = LoopInvariantCodeMotion::new();
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

        let mut licm = LoopInvariantCodeMotion::new();
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

        let mut licm = LoopInvariantCodeMotion::new();
        assert!(!licm.run(&mut func));
    }

    #[test]
    fn test_licm_no_loops() {
        // No loops → LICM should be a no-op.
        let mut func = MachFunction::new("no_loops".to_string(), Signature::new(vec![], vec![]));
        let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(func.entry, ret);

        let mut licm = LoopInvariantCodeMotion::new();
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

        let mut licm = LoopInvariantCodeMotion::new();
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

        let mut licm = LoopInvariantCodeMotion::new();
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

        let mut licm = LoopInvariantCodeMotion::new();
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

        let mut licm = LoopInvariantCodeMotion::new();
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

        let mut licm = LoopInvariantCodeMotion::new();
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
        // loop (depth >= 2, where the tier admits every chain length) the whole
        // chain AND the consuming FMOV must move to the inner preheader.
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

        let mut licm = LoopInvariantCodeMotion::new();
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
        let mut licm = LoopInvariantCodeMotion::new();
        licm.run(&mut func);
        assert_eq!(
            func.block(inner_body).insts,
            original,
            "two-head (ambiguous) constant must not hoist"
        );
    }

    #[test]
    fn test_licm_no_hoist_constant_chain_in_single_loop() {
        // Depth-1 chain-length floor: this 2-instruction chain in a NON-nested
        // (depth-1) loop is left in place, because the floor at depth 1 is >= 3
        // instructions by default. The depth-1→0 pull-out shrinks a single hot
        // loop's body and perturbs downstream passes; a 2-instruction chain
        // (flops-1's `mov`+`movk` loop bound) is exactly the measured regressor,
        // so it only hoists under `TCG_LICM_DEPTH1_MULTI`. See the tier note at
        // the call site.
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
        let mut licm = LoopInvariantCodeMotion::new();
        licm.run(&mut func);
        assert_eq!(
            func.block(bb1).insts,
            original,
            "depth-1 loop constant chain shorter than the floor must stay in \
             place (depth-1 chain-length floor)"
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

        let mut licm = LoopInvariantCodeMotion::new();
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
        let mut licm = LoopInvariantCodeMotion::new();
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

        let mut licm = LoopInvariantCodeMotion::new();
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

        let mut licm = LoopInvariantCodeMotion::new();
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

        let mut licm = LoopInvariantCodeMotion::new();
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

        let mut licm = LoopInvariantCodeMotion::new();
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

        let mut licm = LoopInvariantCodeMotion::new();
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

        let mut licm = LoopInvariantCodeMotion::new();
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
            body: HashSet::from_iter([bb0, bb1]),
            preheader: Some(bb1),
            depth: 1,
            parent: None,
        };
        let dom = DomTree::compute(&func);
        // The whole-function maps are now built by the caller, once per scan.
        let def_counts = build_def_counts(&func);
        let def_map = crate::effects::build_reaching_def_map_by_vreg(&func);
        let layout = LayoutPositions::new();
        let unwind_exits = crate::eh_call_custody::UnwindExits::collect(&func);

        assert!(
            !hoist_loop_invariants(
                &mut func,
                &stale,
                &dom,
                &unwind_exits,
                &def_counts,
                &def_map,
                &layout,
                &mut None,
                &mut None,
                false,
                &mut Vec::new(),
            ),
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

        let mut licm = LoopInvariantCodeMotion::new();
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

        let mut licm = LoopInvariantCodeMotion::new();
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

        let mut licm = LoopInvariantCodeMotion::new();
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

        let mut licm = LoopInvariantCodeMotion::new();
        assert!(!licm.run(&mut func));
        assert!(func.block(bb1).insts.contains(&load));
    }

    /// Where [`store_free_loop_with_acquire`] puts the load-acquire relative
    /// to the invariant plain load.
    #[derive(Clone, Copy, Debug)]
    enum AcquireAt {
        BeforeLoad,
        AfterLoad,
        Preheader,
    }

    /// The tier (a) loop of `test_licm_hoists_invariant_load_store_free`
    /// (`v1 = ldr [v0, #0]`, no writer) plus `acq v9, [v5]` at `at`. Returns
    /// the function, the preheader, the loop block and the plain load.
    fn store_free_loop_with_acquire(
        acq: AArch64Opcode,
        at: AcquireAt,
    ) -> (MachFunction, BlockId, BlockId, InstId) {
        let (mut func, bb0, bb1, bb2) = single_block_loop();
        append(
            &mut func,
            bb0,
            AArch64Opcode::MovI,
            vec![vreg(0), imm(4096)],
        );
        append(
            &mut func,
            bb0,
            AArch64Opcode::MovI,
            vec![vreg(5), imm(8192)],
        );
        let acquire = |func: &mut MachFunction, block| {
            append(func, block, acq, vec![vreg(9), vreg(5)]);
        };
        if let AcquireAt::Preheader = at {
            acquire(&mut func, bb0);
        }
        finish_preheader_branch(&mut func, bb0, bb1);
        if let AcquireAt::BeforeLoad = at {
            acquire(&mut func, bb1);
        }
        let load = append(
            &mut func,
            bb1,
            AArch64Opcode::LdrRI,
            vec![vreg(1), vreg(0), imm(0)],
        );
        if let AcquireAt::AfterLoad = at {
            acquire(&mut func, bb1);
        }
        finish_loop_tail(&mut func, bb1, bb2);
        (func, bb0, bb1, load)
    }

    /// The load-acquire opcodes ([`is_load_acquire`]).
    const ACQUIRE_LOADS: [AArch64Opcode; 4] = [
        AArch64Opcode::Ldar,
        AArch64Opcode::Ldarb,
        AArch64Opcode::Ldarh,
        AArch64Opcode::Ldaxr,
    ];

    #[test]
    fn test_licm_no_hoist_plain_load_out_of_a_loop_with_an_acquire() {
        // Tier (a) sees no writer, but after an in-loop acquire this thread
        // may observe what another thread published: a read that follows it
        // (iteration 1's when it comes first, later iterations' when it comes
        // after) must not be replaced by one read in the preheader.
        let mut hoisted = Vec::new();
        for acq in ACQUIRE_LOADS {
            for at in [AcquireAt::BeforeLoad, AcquireAt::AfterLoad] {
                let (mut func, bb0, bb1, load) = store_free_loop_with_acquire(acq, at);
                LoopInvariantCodeMotion::new().run(&mut func);
                if func.block(bb0).insts.contains(&load) || !func.block(bb1).insts.contains(&load) {
                    hoisted.push((acq, at));
                }
            }
        }
        assert!(
            hoisted.is_empty(),
            "hoisted a plain load out of a loop that contains a load-acquire: {hoisted:?}"
        );
    }

    #[test]
    fn test_licm_hoists_plain_load_when_the_acquire_precedes_the_loop() {
        // POSITIVE CONTROL: an acquire in the preheader runs before the
        // hoisted load's new position too, so tier (a) still applies.
        for acq in ACQUIRE_LOADS {
            let (mut func, bb0, bb1, load) =
                store_free_loop_with_acquire(acq, AcquireAt::Preheader);
            assert!(LoopInvariantCodeMotion::new().run(&mut func), "{acq:?}");
            assert!(func.block(bb0).insts.contains(&load), "{acq:?}");
            assert!(!func.block(bb1).insts.contains(&load), "{acq:?}");
        }
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

        let mut licm = LoopInvariantCodeMotion::new();
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

        let mut licm = LoopInvariantCodeMotion::new();
        assert!(
            !licm.run(&mut func),
            "zero-trip guard preheader must block load"
        );
        assert!(func.block(bb1).insts.contains(&load));
    }

    // -----------------------------------------------------------------------
    // Dereferenceable-frame speculation: a load that is NOT guaranteed to run
    // (it sits behind the loop's exit test) hoists only when it reads inside
    // one fixed-size stack slot.
    // -----------------------------------------------------------------------

    /// Early-exit loop with the load in the body:
    ///
    /// ```text
    ///   bb0: <setup> ; b bb1
    ///   bb1 (header): bcond bb3, bb2        (exit test)
    ///   bb2 (body/latch): <body> ; b bb1
    ///   bb3: ret
    /// ```
    ///
    /// `setup` fills bb0 (before its branch) and `body` fills bb2 (before its
    /// branch). Returns `(func, bb0, bb2)`.
    fn early_exit_loop(
        setup: impl FnOnce(&mut MachFunction, BlockId),
        body: impl FnOnce(&mut MachFunction, BlockId),
    ) -> (MachFunction, BlockId, BlockId) {
        let mut func = MachFunction::new(
            "licm_frame_spec".to_string(),
            Signature::new(vec![], vec![]),
        );
        let bb0 = func.entry;
        let bb1 = func.create_block();
        let bb2 = func.create_block();
        let bb3 = func.create_block();
        setup(&mut func, bb0);
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
        body(&mut func, bb2);
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
        (func, bb0, bb2)
    }

    /// A 24-byte (`Vec`-sized) fixed stack slot whose address is `v0`.
    fn vec_slot_setup(func: &mut MachFunction, bb0: BlockId) {
        let slot = func.alloc_stack_slot(trust_cg_ir::StackSlot::new(24, 8));
        append(
            func,
            bb0,
            AArch64Opcode::AddPCRel,
            vec![vreg(0), sp(), MachOperand::StackSlot(slot)],
        );
    }

    fn load_at(func: &mut MachFunction, block: BlockId, dst: u32, base: u32, off: i64) -> InstId {
        append(
            func,
            block,
            AArch64Opcode::LdrRI,
            vec![vreg(dst), vreg(base), imm(off)],
        )
    }

    #[test]
    fn test_licm_frame_speculation_hoists_in_bounds_slot_loads_behind_exit_test() {
        // The `while k < v.len() { .. v[k] .. }` shape: the Vec's pointer and
        // length loads sit behind the exit test in a store-free loop.
        let mut loads = Vec::new();
        let (mut func, bb0, bb2) = early_exit_loop(vec_slot_setup, |f, b| {
            loads.push(load_at(f, b, 1, 0, 0));
            loads.push(load_at(f, b, 2, 0, 16));
        });
        let mut licm = LoopInvariantCodeMotion::new();
        assert!(licm.run(&mut func), "in-bounds slot loads must hoist");
        for load in loads {
            assert!(func.block(bb0).insts.contains(&load));
            assert!(!func.block(bb2).insts.contains(&load));
        }
    }

    #[test]
    fn test_licm_frame_speculation_off_keeps_the_old_rule() {
        let mut load = None;
        let (mut func, _, bb2) = early_exit_loop(vec_slot_setup, |f, b| {
            load = Some(load_at(f, b, 1, 0, 16));
        });
        let mut licm = LoopInvariantCodeMotion::without_frame_speculation();
        assert!(!licm.run(&mut func));
        assert!(func.block(bb2).insts.contains(&load.expect("load")));
    }

    #[test]
    fn test_licm_frame_speculation_refuses_access_past_the_slot() {
        // Bytes [20, 28) of a 24-byte slot: the last four are outside it.
        let mut load = None;
        let (mut func, _, bb2) = early_exit_loop(vec_slot_setup, |f, b| {
            load = Some(load_at(f, b, 1, 0, 20));
        });
        let mut licm = LoopInvariantCodeMotion::new();
        assert!(!licm.run(&mut func));
        assert!(func.block(bb2).insts.contains(&load.expect("load")));
    }

    #[test]
    fn test_licm_frame_speculation_refuses_access_below_the_slot() {
        // `v3 = v0 - 8` then `[v3, #0]`: eight bytes before the slot.
        let mut load = None;
        let (mut func, _, bb2) = early_exit_loop(
            |f, b| {
                vec_slot_setup(f, b);
                append(f, b, AArch64Opcode::SubRI, vec![vreg(3), vreg(0), imm(8)]);
            },
            |f, b| {
                load = Some(load_at(f, b, 1, 3, 0));
            },
        );
        let mut licm = LoopInvariantCodeMotion::new();
        // The SubRI is already outside the loop; nothing may move.
        assert!(!licm.run(&mut func));
        assert!(func.block(bb2).insts.contains(&load.expect("load")));
    }

    #[test]
    fn test_licm_frame_speculation_follows_offsets_inside_the_slot() {
        // `v3 = v0 + 8` then `[v3, #8]`: bytes [16, 24), inside the slot.
        let mut load = None;
        let (mut func, bb0, _) = early_exit_loop(
            |f, b| {
                vec_slot_setup(f, b);
                append(f, b, AArch64Opcode::AddRI, vec![vreg(3), vreg(0), imm(8)]);
            },
            |f, b| {
                load = Some(load_at(f, b, 1, 3, 8));
            },
        );
        let mut licm = LoopInvariantCodeMotion::new();
        assert!(licm.run(&mut func));
        assert!(func.block(bb0).insts.contains(&load.expect("load")));
    }

    /// `v9 = Madd(v3, v8, v0)` with `v3 = #index`, `v8 = #8`: the adapter's
    /// constant-index `gep i64` into the slot, then `[v9, #0]`.
    fn gep_slot_load(index: i64) -> (MachFunction, BlockId, BlockId, InstId) {
        let mut load = None;
        let (func, bb0, bb2) = early_exit_loop(
            |f, b| {
                vec_slot_setup(f, b);
                append(f, b, AArch64Opcode::Movz, vec![vreg(3), imm(index)]);
                append(f, b, AArch64Opcode::Movz, vec![vreg(8), imm(8)]);
                append(
                    f,
                    b,
                    AArch64Opcode::Madd,
                    vec![vreg(9), vreg(3), vreg(8), vreg(0)],
                );
            },
            |f, b| {
                load = Some(load_at(f, b, 1, 9, 0));
            },
        );
        (func, bb0, bb2, load.expect("load"))
    }

    #[test]
    fn test_licm_frame_speculation_follows_constant_index_gep() {
        // Element 2 of the three-word slot: bytes [16, 24).
        let (mut func, bb0, _, load) = gep_slot_load(2);
        let mut licm = LoopInvariantCodeMotion::new();
        assert!(licm.run(&mut func));
        assert!(func.block(bb0).insts.contains(&load));
    }

    #[test]
    fn test_licm_frame_speculation_refuses_constant_index_gep_past_the_slot() {
        // Element 3: bytes [24, 32), past the 24-byte slot.
        let (mut func, _, bb2, load) = gep_slot_load(3);
        let mut licm = LoopInvariantCodeMotion::new();
        assert!(!licm.run(&mut func));
        assert!(func.block(bb2).insts.contains(&load));
    }

    /// `v9 = AddRR(v0, v8)` (or `AddRR(v8, v0)` when `swapped`) with `v8 =
    /// #k` or, when `runtime`, a loaded `k`: the field address `&vec.ptr`
    /// after GVN reused an equal constant register, then `[v9, #0]`.
    fn addrr_slot_load(
        k: i64,
        swapped: bool,
        runtime: bool,
    ) -> (MachFunction, BlockId, BlockId, InstId) {
        let mut load = None;
        let (func, bb0, bb2) = early_exit_loop(
            |f, b| {
                vec_slot_setup(f, b);
                if runtime {
                    append(f, b, AArch64Opcode::LdrRI, vec![vreg(8), vreg(0), imm(0)]);
                } else {
                    append(f, b, AArch64Opcode::Movz, vec![vreg(8), imm(k)]);
                }
                let (a, c) = if swapped { (8, 0) } else { (0, 8) };
                append(f, b, AArch64Opcode::AddRR, vec![vreg(9), vreg(a), vreg(c)]);
            },
            |f, b| {
                load = Some(load_at(f, b, 1, 9, 0));
            },
        );
        (func, bb0, bb2, load.expect("load"))
    }

    #[test]
    fn test_licm_frame_speculation_follows_constant_register_offset() {
        // `&vec.ptr = slot + 8` in either operand order: bytes [8, 16).
        for swapped in [false, true] {
            let (mut func, bb0, bb2, load) = addrr_slot_load(8, swapped, false);
            let mut licm = LoopInvariantCodeMotion::new();
            assert!(licm.run(&mut func), "swapped={swapped}");
            assert!(func.block(bb0).insts.contains(&load));
            assert!(!func.block(bb2).insts.contains(&load));
        }
    }

    #[test]
    fn test_licm_frame_speculation_refuses_constant_register_offset_past_the_slot() {
        // `slot + 24`: bytes [24, 32), past the 24-byte slot.
        let (mut func, _, bb2, load) = addrr_slot_load(24, false, false);
        let mut licm = LoopInvariantCodeMotion::new();
        assert!(!licm.run(&mut func));
        assert!(func.block(bb2).insts.contains(&load));
    }

    #[test]
    fn test_licm_frame_speculation_refuses_runtime_register_offset() {
        // `slot + <loaded value>`: the offset is not a constant, so the address
        // is not provably inside the slot.
        let (mut func, _, bb2, load) = addrr_slot_load(0, false, true);
        let mut licm = LoopInvariantCodeMotion::new();
        assert!(!licm.run(&mut func));
        assert!(func.block(bb2).insts.contains(&load));
    }

    #[test]
    fn test_licm_frame_speculation_refuses_runtime_sized_slot() {
        let mut load = None;
        let (mut func, _, bb2) = early_exit_loop(
            |f, b| {
                let mut slot = trust_cg_ir::StackSlot::new(24, 8);
                slot.allocation = StackSlotAllocationKind::RuntimeSized {
                    size_source: trust_cg_ir::function::StackSlotSizeSource::Unknown,
                };
                let slot = f.alloc_stack_slot(slot);
                append(
                    f,
                    b,
                    AArch64Opcode::AddPCRel,
                    vec![vreg(0), sp(), MachOperand::StackSlot(slot)],
                );
            },
            |f, b| {
                load = Some(load_at(f, b, 1, 0, 0));
            },
        );
        let mut licm = LoopInvariantCodeMotion::new();
        assert!(!licm.run(&mut func));
        assert!(func.block(bb2).insts.contains(&load.expect("load")));
    }

    #[test]
    fn test_licm_frame_speculation_refuses_non_frame_pointer() {
        // A materialized integer is not a frame address, so the old rule holds.
        let mut load = None;
        let (mut func, _, bb2) = early_exit_loop(
            |f, b| {
                append(f, b, AArch64Opcode::MovI, vec![vreg(0), imm(4096)]);
            },
            |f, b| {
                load = Some(load_at(f, b, 1, 0, 0));
            },
        );
        let mut licm = LoopInvariantCodeMotion::new();
        assert!(!licm.run(&mut func));
        assert!(func.block(bb2).insts.contains(&load.expect("load")));
    }

    #[test]
    fn test_licm_frame_speculation_refuses_when_the_loop_stores_the_slot() {
        // Tier (b) still applies: an in-loop store to the same slot keeps the load.
        let mut load = None;
        let (mut func, _, bb2) = early_exit_loop(
            |f, b| {
                vec_slot_setup(f, b);
                append(f, b, AArch64Opcode::MovI, vec![vreg(6), imm(7)]);
            },
            |f, b| {
                load = Some(load_at(f, b, 1, 0, 16));
                append(f, b, AArch64Opcode::StrRI, vec![vreg(6), vreg(0), imm(0)]);
            },
        );
        let mut licm = LoopInvariantCodeMotion::new();
        assert!(!licm.run(&mut func));
        assert!(func.block(bb2).insts.contains(&load.expect("load")));
    }

    #[test]
    fn test_licm_frame_speculation_through_self_copied_carrier() {
        // The bridge's out-of-SSA shape: `v7` is defined once from the slot
        // address and otherwise only re-copied to itself on the back edge, and
        // the preheader copies it into the load's base.
        let mut load = None;
        let (mut func, bb0, _) = early_exit_loop(
            |f, b| {
                vec_slot_setup(f, b);
                append(f, b, AArch64Opcode::MovR, vec![vreg(7), vreg(0)]);
                append(f, b, AArch64Opcode::MovR, vec![vreg(2), vreg(7)]);
            },
            |f, b| {
                load = Some(load_at(f, b, 1, 2, 8));
                append(f, b, AArch64Opcode::MovR, vec![vreg(7), vreg(7)]);
            },
        );
        let mut licm = LoopInvariantCodeMotion::new();
        assert!(licm.run(&mut func));
        assert!(func.block(bb0).insts.contains(&load.expect("load")));
    }

    #[test]
    fn test_licm_frame_speculation_refuses_second_value_changing_def() {
        // `v7` has a second value-changing definition (`v7 = v7 + 16` on the
        // back edge). The resolver does not decide which definition reaches
        // the preheader copy, so it refuses (conservatively: here it is the
        // first one).
        let mut load = None;
        let (mut func, _, bb2) = early_exit_loop(
            |f, b| {
                vec_slot_setup(f, b);
                append(f, b, AArch64Opcode::MovR, vec![vreg(7), vreg(0)]);
                append(f, b, AArch64Opcode::MovR, vec![vreg(2), vreg(7)]);
            },
            |f, b| {
                load = Some(load_at(f, b, 1, 2, 8));
                append(f, b, AArch64Opcode::AddRI, vec![vreg(7), vreg(7), imm(16)]);
            },
        );
        let mut licm = LoopInvariantCodeMotion::new();
        assert!(!licm.run(&mut func));
        assert!(func.block(bb2).insts.contains(&load.expect("load")));
    }

    /// Position of `id` in `block`, which must hold it.
    fn position_in(func: &MachFunction, block: BlockId, id: InstId) -> usize {
        func.block(block)
            .insts
            .iter()
            .position(|&x| x == id)
            .expect("instruction in block")
    }

    /// The hoisted load sits in `bb0` after `writer` and right before the
    /// preheader's closing `B`.
    fn assert_load_after_writer(func: &MachFunction, bb0: BlockId, writer: InstId, load: InstId) {
        let insts = &func.block(bb0).insts;
        let load_pos = position_in(func, bb0, load);
        assert!(
            position_in(func, bb0, writer) < load_pos,
            "the hoisted load must read the slot after the preheader wrote it: {insts:?}"
        );
        assert_eq!(load_pos + 1, insts.len() - 1, "load right before the tail");
        let last = func.inst(*insts.last().expect("preheader branch"));
        assert_eq!(last.opcode, AArch64Opcode::B);
    }

    #[test]
    fn test_licm_frame_speculation_lands_after_a_store_ending_the_preheader() {
        // The preheader's last instruction before its branch stores the bytes
        // the loop reads (`a[2] = v6`, then `b header`). The old placement
        // stepped back over any non-value side effect before the tail, so the
        // speculated load read the slot before this store.
        let (mut store, mut load) = (None, None);
        let (mut func, bb0, bb2) = early_exit_loop(
            |f, b| {
                vec_slot_setup(f, b);
                append(f, b, AArch64Opcode::MovI, vec![vreg(6), imm(7)]);
                store = Some(append(
                    f,
                    b,
                    AArch64Opcode::StrRI,
                    vec![vreg(6), vreg(0), imm(16)],
                ));
            },
            |f, b| {
                load = Some(load_at(f, b, 1, 0, 16));
            },
        );
        let (store, load) = (store.expect("store"), load.expect("load"));
        let mut licm = LoopInvariantCodeMotion::new();
        assert!(licm.run(&mut func), "the in-bounds slot load hoists");
        assert!(!func.block(bb2).insts.contains(&load));
        assert_load_after_writer(&func, bb0, store, load);
    }

    /// `v5 = #1 ; TrapBoundsCheckExact v5 <u 3 ; v6 = #7 ; str v6, [v0, #16]`:
    /// a mid-block guard carrier (flagged `IS_BRANCH | IS_TERMINATOR`, falls
    /// through) followed by a store to the slot the loop reads.
    fn carrier_then_store(f: &mut MachFunction, b: BlockId) -> (InstId, InstId) {
        append(f, b, AArch64Opcode::MovI, vec![vreg(5), imm(1)]);
        let carrier = append(
            f,
            b,
            AArch64Opcode::TrapBoundsCheckExact,
            vec![vreg(5), vreg(5), imm(3)],
        );
        append(f, b, AArch64Opcode::MovI, vec![vreg(6), imm(7)]);
        let store = append(f, b, AArch64Opcode::StrRI, vec![vreg(6), vreg(0), imm(16)]);
        (carrier, store)
    }

    #[test]
    fn test_licm_frame_speculation_lands_after_a_trap_carrier_and_its_store() {
        // The old placement inserted before the first `is_branch()` instruction,
        // which is the carrier: the speculated load then ran before the carrier
        // and before the store behind it.
        let (mut written, mut load) = (None, None);
        let (mut func, bb0, _) = early_exit_loop(
            |f, b| {
                vec_slot_setup(f, b);
                written = Some(carrier_then_store(f, b));
            },
            |f, b| {
                load = Some(load_at(f, b, 1, 0, 16));
            },
        );
        let ((carrier, store), load) = (written.expect("preheader"), load.expect("load"));
        let mut licm = LoopInvariantCodeMotion::new();
        assert!(licm.run(&mut func), "the in-bounds slot load hoists");
        assert!(position_in(&func, bb0, carrier) < position_in(&func, bb0, load));
        assert_load_after_writer(&func, bb0, store, load);
    }

    #[test]
    fn test_licm_guaranteed_load_lands_after_a_trap_carrier_and_its_store() {
        // The same placement bug for a load that runs on every iteration (it
        // is in the single-block loop's header, before the exit test), and
        // so independent of the frame tier: switched off here.
        let (mut func, bb0, bb1, bb2) = single_block_loop();
        append(
            &mut func,
            bb0,
            AArch64Opcode::MovI,
            vec![vreg(0), imm(4096)],
        );
        let (carrier, store) = carrier_then_store(&mut func, bb0);
        finish_preheader_branch(&mut func, bb0, bb1);
        let load = load_at(&mut func, bb1, 1, 0, 16);
        finish_loop_tail(&mut func, bb1, bb2);
        let mut licm = LoopInvariantCodeMotion::without_frame_speculation();
        assert!(licm.run(&mut func), "the guaranteed store-free load hoists");
        assert!(position_in(&func, bb0, carrier) < position_in(&func, bb0, load));
        assert_load_after_writer(&func, bb0, store, load);
    }

    #[test]
    fn test_licm_frame_speculation_refuses_a_base_def_that_does_not_dominate_the_load() {
        // `v0`'s only value-changing definition (the slot address) is on one
        // arm of a diamond before the loop; on the other arm `v0` keeps
        // whatever it held on entry (a live-in, e.g. a reused argument
        // register), which need not be a frame address.
        //
        //   bb0: bcond bb_a, bb_b
        //   bb_a: v0 = &slot ; b bb_j        bb_b: b bb_j
        //   bb_j (preheader): b bb1
        //   bb1 (header): bcond bb3, bb2     bb2: [v0, #0] ; b bb1     bb3: ret
        let mut func = MachFunction::new(
            "licm_frame_nondom".to_string(),
            Signature::new(vec![], vec![]),
        );
        let bb0 = func.entry;
        let (bb_a, bb_b, bb_j) = (
            func.create_block(),
            func.create_block(),
            func.create_block(),
        );
        let (bb1, bb2, bb3) = (
            func.create_block(),
            func.create_block(),
            func.create_block(),
        );
        append(
            &mut func,
            bb0,
            AArch64Opcode::BCond,
            vec![MachOperand::Block(bb_a), MachOperand::Block(bb_b)],
        );
        vec_slot_setup(&mut func, bb_a);
        append(
            &mut func,
            bb_a,
            AArch64Opcode::B,
            vec![MachOperand::Block(bb_j)],
        );
        append(
            &mut func,
            bb_b,
            AArch64Opcode::B,
            vec![MachOperand::Block(bb_j)],
        );
        append(
            &mut func,
            bb_j,
            AArch64Opcode::B,
            vec![MachOperand::Block(bb1)],
        );
        append(
            &mut func,
            bb1,
            AArch64Opcode::BCond,
            vec![MachOperand::Block(bb3), MachOperand::Block(bb2)],
        );
        let load = load_at(&mut func, bb2, 1, 0, 0);
        append(
            &mut func,
            bb2,
            AArch64Opcode::B,
            vec![MachOperand::Block(bb1)],
        );
        append(&mut func, bb3, AArch64Opcode::Ret, vec![]);
        for (from, to) in [
            (bb0, bb_a),
            (bb0, bb_b),
            (bb_a, bb_j),
            (bb_b, bb_j),
            (bb_j, bb1),
            (bb1, bb3),
            (bb1, bb2),
            (bb2, bb1),
        ] {
            func.add_edge(from, to);
        }
        let mut licm = LoopInvariantCodeMotion::new();
        assert!(!licm.run(&mut func));
        assert!(func.block(bb2).insts.contains(&load));
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
    fn test_licm_tier_b_distinct_global_authority_is_withdrawn() {
        // Different symbol spellings do not authenticate distinct objects or
        // the complete accessed intervals. Retain the former positive fixture
        // as a named capability-withdrawal control.
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

        let mut licm = LoopInvariantCodeMotion::new();
        assert!(
            !licm.run(&mut func),
            "unbound distinct-symbol load/store authority must not hoist"
        );
        assert!(!func.block(bb0).insts.contains(&load));
        assert!(func.block(bb1).insts.contains(&load));
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

        let mut licm = LoopInvariantCodeMotion::new();
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
        assert_eq!(
            func.alloc_stack_slot(trust_cg_ir::StackSlot::new(16, 8)),
            StackSlotId(0)
        );
        assert_eq!(
            func.alloc_stack_slot(trust_cg_ir::StackSlot::new(16, 8)),
            StackSlotId(1)
        );
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

        let mut licm = LoopInvariantCodeMotion::new();
        assert!(func.try_sync_vreg_counter().is_some());
        let mut without_speculation = func.clone();
        assert!(LoopInvariantCodeMotion::without_frame_speculation().run(&mut without_speculation));
        assert!(without_speculation.block(bb0).insts.contains(&load));
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
        assert_eq!(
            func.alloc_stack_slot(trust_cg_ir::StackSlot::new(16, 8)),
            StackSlotId(0)
        );
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

        let mut licm = LoopInvariantCodeMotion::new();
        assert!(!licm.run(&mut func), "same-slot load/store must not hoist");
        assert!(func.block(bb1).insts.contains(&load));
    }

    #[test]
    fn test_licm_tier_b_stack_vs_global_authority_is_withdrawn() {
        // A stack interval does not authenticate the address/extent denoted by
        // a bare symbol spelling. Keep the original positive as lost coverage.
        let (mut func, bb0, bb1, bb2) = single_block_loop();
        assert_eq!(
            func.alloc_stack_slot(trust_cg_ir::StackSlot::new(16, 8)),
            StackSlotId(0)
        );
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

        let mut licm = LoopInvariantCodeMotion::new();
        assert!(
            !licm.run(&mut func),
            "stack/global names are not disjointness authority"
        );
        assert!(!func.block(bb0).insts.contains(&load));
        assert!(func.block(bb1).insts.contains(&load));
    }

    #[test]
    fn test_licm_tier_b_bare_adrp_same_page_authority_is_withdrawn() {
        // ADRP computes page(symbol), not the object's address. Distinct
        // symbols can share that page; a page-rooted store may alias even a
        // correctly materialized full symbol address at a static page offset.
        for full_load_address in [false, true] {
            let (mut func, bb0, bb1, bb2) = single_block_loop();
            if full_load_address {
                materialize_global(&mut func, bb0, 0, 1, "same_page_A");
            } else {
                append(
                    &mut func,
                    bb0,
                    AArch64Opcode::Adrp,
                    vec![vreg(1), sym("same_page_A")],
                );
            }
            append(
                &mut func,
                bb0,
                AArch64Opcode::Adrp,
                vec![vreg(3), sym("same_page_B")],
            );
            append(&mut func, bb0, AArch64Opcode::MovI, vec![vreg(9), imm(7)]);
            finish_preheader_branch(&mut func, bb0, bb1);
            let load = load_at(&mut func, bb1, 4, 1, 0);
            append(
                &mut func,
                bb1,
                AArch64Opcode::StrRI,
                vec![vreg(9), vreg(3), imm(0)],
            );
            finish_loop_tail(&mut func, bb1, bb2);
            assert!(func.try_sync_vreg_counter().is_some());
            let original = func.block(bb1).insts.clone();
            assert!(
                !LoopInvariantCodeMotion::new().run(&mut func),
                "full_load_address={full_load_address}"
            );
            assert_eq!(func.block(bb1).insts, original);
            assert!(!func.block(bb0).insts.contains(&load));
        }
    }

    #[test]
    fn test_licm_tier_b_integer_pointer_alias_shape_refuses() {
        // Core PtrToInt/IntToPtr become full-width copies. A + (B - A)
        // denotes B, not an allocation that remains disjoint merely because
        // an additive trace encounters A. No new alias interpreter is used.
        let (mut func, bb0, bb1, bb2) = single_block_loop();
        materialize_global(&mut func, bb0, 0, 1, "A");
        materialize_global(&mut func, bb0, 2, 3, "B");
        append(
            &mut func,
            bb0,
            AArch64Opcode::SubRR,
            vec![vreg(5), vreg(3), vreg(1)],
        );
        append(
            &mut func,
            bb0,
            AArch64Opcode::AddRR,
            vec![vreg(6), vreg(1), vreg(5)],
        );
        append(&mut func, bb0, AArch64Opcode::MovR, vec![vreg(7), vreg(6)]);
        append(&mut func, bb0, AArch64Opcode::MovI, vec![vreg(9), imm(7)]);
        finish_preheader_branch(&mut func, bb0, bb1);
        let load = load_at(&mut func, bb1, 4, 3, 0);
        append(
            &mut func,
            bb1,
            AArch64Opcode::StrRI,
            vec![vreg(9), vreg(7), imm(0)],
        );
        finish_loop_tail(&mut func, bb1, bb2);
        assert!(func.try_sync_vreg_counter().is_some());
        let original = func.block(bb1).insts.clone();
        assert!(!LoopInvariantCodeMotion::new().run(&mut func));
        assert_eq!(func.block(bb1).insts, original);
        assert!(!func.block(bb0).insts.contains(&load));
    }

    #[test]
    fn test_licm_tier_b_stack_access_requires_actual_fixed_bounds() {
        for mutation in 0..7 {
            let (mut func, bb0, bb1, bb2) = single_block_loop();
            func.alloc_stack_slot(trust_cg_ir::StackSlot::new(16, 8));
            func.alloc_stack_slot(trust_cg_ir::StackSlot::new(16, 8));
            match mutation {
                0 => {
                    func.stack_slots.pop();
                }
                1 => {
                    func.stack_slots[1].size = 0;
                }
                2 => {
                    func.stack_slots[1].allocation = StackSlotAllocationKind::RuntimeSized {
                        size_source: trust_cg_ir::function::StackSlotSizeSource::Unknown,
                    };
                }
                _ => {}
            }
            materialize_slot(&mut func, bb0, 0, 0);
            materialize_slot(&mut func, bb0, 1, 1);
            if mutation == 6 {
                let source = func.block(bb0).insts[1];
                func.inst_mut(source).operands[1] = vreg(7); // not SP custody
            }
            append(&mut func, bb0, AArch64Opcode::MovI, vec![vreg(9), imm(7)]);
            finish_preheader_branch(&mut func, bb0, bb1);
            let load_offset = if mutation == 5 { 9 } else { 0 };
            let load = load_at(&mut func, bb1, 4, 0, load_offset);
            let store_offset = match mutation {
                3 => -1,
                4 => 9,
                _ => 0,
            };
            append(
                &mut func,
                bb1,
                AArch64Opcode::StrRI,
                vec![vreg(9), vreg(1), imm(store_offset)],
            );
            finish_loop_tail(&mut func, bb1, bb2);
            assert!(func.try_sync_vreg_counter().is_some());
            let original = func.block(bb1).insts.clone();
            assert!(
                !LoopInvariantCodeMotion::new().run(&mut func),
                "stack bounds mutation={mutation}"
            );
            assert_eq!(func.block(bb1).insts, original);
            assert!(!func.block(bb0).insts.contains(&load));
        }
    }

    #[test]
    fn test_licm_tier_b_stack_other_register_view_refuses() {
        // Numeric virtual-register storage is shared by W/X views. A typed
        // unique X definition is not reaching-address authority after W writes.
        let (mut func, bb0, bb1, bb2) = single_block_loop();
        func.alloc_stack_slot(trust_cg_ir::StackSlot::new(16, 8));
        func.alloc_stack_slot(trust_cg_ir::StackSlot::new(16, 8));
        materialize_slot(&mut func, bb0, 0, 0);
        materialize_slot(&mut func, bb0, 1, 1);
        append(
            &mut func,
            bb0,
            AArch64Opcode::MovI,
            vec![vreg_class(0, RegClass::Gpr32), imm(0)],
        );
        append(&mut func, bb0, AArch64Opcode::MovI, vec![vreg(9), imm(7)]);
        finish_preheader_branch(&mut func, bb0, bb1);
        let load = load_at(&mut func, bb1, 4, 0, 0);
        append(
            &mut func,
            bb1,
            AArch64Opcode::StrRI,
            vec![vreg(9), vreg(1), imm(0)],
        );
        finish_loop_tail(&mut func, bb1, bb2);
        assert!(func.try_sync_vreg_counter().is_some());
        let original = func.block(bb1).insts.clone();
        assert!(!LoopInvariantCodeMotion::new().run(&mut func));
        assert_eq!(func.block(bb1).insts, original);
        assert!(!func.block(bb0).insts.contains(&load));
    }

    #[test]
    fn test_licm_tier_b_stack_definition_must_reach_load() {
        // One arm defines v0 as a slot address; the other preserves its live-in
        // value. A whole-function unique definition does not dominate the use.
        let mut func = MachFunction::new(
            "licm_stack_nondom".to_string(),
            Signature::new(vec![], vec![]),
        );
        func.alloc_stack_slot(trust_cg_ir::StackSlot::new(16, 8));
        func.alloc_stack_slot(trust_cg_ir::StackSlot::new(16, 8));
        let bb0 = func.entry;
        let left = func.create_block();
        let right = func.create_block();
        let preheader = func.create_block();
        let header = func.create_block();
        let exit = func.create_block();
        append(
            &mut func,
            bb0,
            AArch64Opcode::BCond,
            vec![MachOperand::Block(left), MachOperand::Block(right)],
        );
        materialize_slot(&mut func, left, 0, 0);
        append(
            &mut func,
            left,
            AArch64Opcode::B,
            vec![MachOperand::Block(preheader)],
        );
        append(
            &mut func,
            right,
            AArch64Opcode::B,
            vec![MachOperand::Block(preheader)],
        );
        materialize_slot(&mut func, preheader, 1, 1);
        append(
            &mut func,
            preheader,
            AArch64Opcode::MovI,
            vec![vreg(9), imm(7)],
        );
        finish_preheader_branch(&mut func, preheader, header);
        let load = load_at(&mut func, header, 4, 0, 0);
        append(
            &mut func,
            header,
            AArch64Opcode::StrRI,
            vec![vreg(9), vreg(1), imm(0)],
        );
        finish_loop_tail(&mut func, header, exit);
        for (from, to) in [
            (bb0, left),
            (bb0, right),
            (left, preheader),
            (right, preheader),
            (preheader, header),
            (header, header),
            (header, exit),
        ] {
            func.add_edge(from, to);
        }
        assert!(func.try_sync_vreg_counter().is_some());
        let original = func.block(header).insts.clone();
        assert!(!LoopInvariantCodeMotion::new().run(&mut func));
        assert_eq!(func.block(header).insts, original);
        assert!(!func.block(preheader).insts.contains(&load));
    }

    #[test]
    fn test_licm_tier_b_numeric_census_is_lazy_and_counts_all_stored_references() {
        let (mut func, bb0, _, _) = single_block_loop();
        func.alloc_stack_slot(trust_cg_ir::StackSlot::new(16, 8));
        materialize_slot(&mut func, bb0, 0, 0);
        let root = func.block(bb0).insts[0];
        let hidden = func.create_block();
        append(
            &mut func,
            hidden,
            AArch64Opcode::MovI,
            vec![vreg_class(0, RegClass::Gpr32), imm(0)],
        );
        func.append_inst(hidden, root); // repeated actual definition reference
        func.block_order.retain(|id| *id != hidden);
        let mut sites = FrameDefSites::build(&func);
        assert!(
            sites.numeric_counts.is_none(),
            "legacy typed setup performs no numeric census"
        );
        assert_eq!(
            sites
                .sites
                .get(&VReg::new(0, RegClass::Gpr64))
                .expect("active root")
                .len(),
            1
        );
        assert_eq!(sites.numeric_definition_count(&func, 0), 3);
        assert!(
            sites.numeric_counts.is_some(),
            "new TierB demand owns one cached census"
        );
        assert_eq!(sites.numeric_definition_count(&func, 0), 3);
        assert_eq!(sites.numeric_definition_count(&func, 99), 0);
    }

    #[test]
    fn test_licm_tier_b_rejecting_writer_summary_stops_unused_census() {
        for kind in [
            AArch64Opcode::Bl,
            AArch64Opcode::Dmb,
            AArch64Opcode::Ldar,
            AArch64Opcode::StrRI,
        ] {
            for canonical_first in [false, true] {
                let (mut func, bb0, bb1, bb2) = single_block_loop();
                func.alloc_stack_slot(trust_cg_ir::StackSlot::new(16, 8));
                materialize_slot(&mut func, bb0, 1, 0);
                append(
                    &mut func,
                    bb0,
                    AArch64Opcode::MovI,
                    vec![vreg(5), imm(4096)],
                );
                append(&mut func, bb0, AArch64Opcode::MovI, vec![vreg(9), imm(7)]);
                finish_preheader_branch(&mut func, bb0, bb1);
                // Nonwriters must not end the scan: it reaches the later call,
                // barrier, acquire or unclassified store in every case.
                append(&mut func, bb1, AArch64Opcode::MovI, vec![vreg(12), imm(11)]);
                load_at(&mut func, bb1, 13, 5, 0);
                let canonical = |f: &mut MachFunction| {
                    append(f, bb1, AArch64Opcode::StrRI, vec![vreg(9), vreg(1), imm(0)]);
                };
                if canonical_first {
                    canonical(&mut func);
                }
                let operands = match kind {
                    AArch64Opcode::Bl => vec![sym("opaque_call")],
                    AArch64Opcode::Dmb => vec![imm(15)],
                    AArch64Opcode::Ldar => vec![vreg(14), vreg(5)],
                    AArch64Opcode::StrRI => vec![vreg(9), vreg(5), imm(0)],
                    _ => unreachable!(),
                };
                append(&mut func, bb1, kind, operands);
                if !canonical_first {
                    canonical(&mut func);
                }
                finish_loop_tail(&mut func, bb1, bb2);
                assert!(func.try_sync_vreg_counter().is_some());
                let original = func.block(bb1).insts.clone();
                let dom = DomTree::compute(&func);
                let counts = build_def_counts(&func);
                let defs = crate::effects::build_reaching_def_map_by_vreg(&func);
                let mut sites = None;
                let facts =
                    compute_loop_memory_facts(&func, &dom, &[bb1], &defs, &counts, &mut sites);
                assert!(
                    facts.writes_memory && facts.opaque_writer,
                    "{kind:?}/{canonical_first}"
                );
                assert!(
                    facts.store_bases.is_empty(),
                    "partial rows are not authority: {kind:?}/{canonical_first}"
                );
                assert_eq!(
                    sites.is_some(),
                    canonical_first,
                    "census demand: {kind:?}/{canonical_first}"
                );
                if let Some(sites) = &sites {
                    assert!(
                        sites.numeric_counts.is_some(),
                        "retain an already-demanded cache"
                    );
                }
                assert_eq!(func.block(bb1).insts, original);
            }
        }
    }

    #[test]
    fn test_licm_tier_b_nonwriter_prefix_still_demands_later_bounded_store() {
        let (mut func, bb0, bb1, bb2) = single_block_loop();
        func.alloc_stack_slot(trust_cg_ir::StackSlot::new(16, 8));
        materialize_slot(&mut func, bb0, 1, 0);
        append(
            &mut func,
            bb0,
            AArch64Opcode::MovI,
            vec![vreg(5), imm(4096)],
        );
        append(&mut func, bb0, AArch64Opcode::MovI, vec![vreg(9), imm(7)]);
        finish_preheader_branch(&mut func, bb0, bb1);
        append(&mut func, bb1, AArch64Opcode::MovI, vec![vreg(12), imm(11)]);
        load_at(&mut func, bb1, 13, 5, 0);
        append(
            &mut func,
            bb1,
            AArch64Opcode::StrRI,
            vec![vreg(9), vreg(1), imm(0)],
        );
        finish_loop_tail(&mut func, bb1, bb2);
        assert!(func.try_sync_vreg_counter().is_some());
        let dom = DomTree::compute(&func);
        let counts = build_def_counts(&func);
        let defs = crate::effects::build_reaching_def_map_by_vreg(&func);
        let mut sites = None;
        let facts = compute_loop_memory_facts(&func, &dom, &[bb1], &defs, &counts, &mut sites);
        assert!(facts.writes_memory);
        assert!(!facts.opaque_writer);
        assert_eq!(facts.store_bases, vec![AddrBase::Stack(StackSlotId(0))]);
        let sites = sites.expect("one demanded shared index");
        assert_eq!(
            sites.numeric_counts.expect("one demanded census").get(&1),
            Some(&1)
        );
    }

    #[test]
    fn test_licm_tier_b_unknown_writer_keeps_load_but_pure_hoist_continues() {
        let (mut func, bb0, bb1, bb2) = single_block_loop();
        append(
            &mut func,
            bb0,
            AArch64Opcode::MovI,
            vec![vreg(0), imm(4096)],
        );
        finish_preheader_branch(&mut func, bb0, bb1);
        let load = load_at(&mut func, bb1, 4, 0, 0);
        let pure = append(&mut func, bb1, AArch64Opcode::MovI, vec![vreg(9), imm(7)]);
        let store = append(
            &mut func,
            bb1,
            AArch64Opcode::StrRI,
            vec![vreg(9), vreg(0), imm(0)],
        );
        finish_loop_tail(&mut func, bb1, bb2);
        assert!(func.try_sync_vreg_counter().is_some());
        assert!(LoopInvariantCodeMotion::new().run(&mut func));
        assert!(func.block(bb0).insts.contains(&pure));
        assert!(!func.block(bb1).insts.contains(&pure));
        assert!(func.block(bb1).insts.contains(&load));
        assert!(func.block(bb1).insts.contains(&store));
        assert!(!func.block(bb0).insts.contains(&load));
        assert!(!func.block(bb0).insts.contains(&store));
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

        let mut licm = LoopInvariantCodeMotion::new();
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

        let mut licm = LoopInvariantCodeMotion::new();
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

        let mut licm = LoopInvariantCodeMotion::new();
        assert!(licm.run(&mut func), "header load must still hoist");
        assert!(func.block(bb0).insts.contains(&load));
        assert!(!func.block(bb1).insts.contains(&load));
    }

    // ---------------------------------------------------------------------
    // Must-execute across an inner cycle the first iteration can spin in
    // ---------------------------------------------------------------------

    /// Where [`loop_with_inner_cycle`] puts an inner cycle relative to the
    /// invariant load `v1 = ldr [v0]`.
    #[derive(Clone, Copy, Debug)]
    enum InnerCycle {
        /// `bb1 -> bb2 (self-loop) -> bb3`, the load in bb3.
        SelfLoopThenLoad,
        /// `bb1 -> {bb2, bb3}` with `bb2 <-> bb3` (two entries, so not a
        /// natural loop) and both `-> bb4`, the load in bb4.
        IrreducibleThenLoad,
        /// `bb1 -> bb2 (self-loop) -> bb3`, the load in the header bb1.
        LoadThenSelfLoop,
    }

    /// A loop entered unconditionally from `bb0` (`v0 = 4096 ; b bb1`) whose
    /// last block is its only latch and only exiting block. The load's block
    /// therefore dominates every latch and exit in every shape. Returns the
    /// function, the load and the block it starts in.
    fn loop_with_inner_cycle(shape: InnerCycle) -> (MachFunction, InstId, BlockId) {
        let mut func = MachFunction::new("inner".to_string(), Signature::new(vec![], vec![]));
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
        finish_preheader_branch(&mut func, bb0, bb1);
        func.add_edge(bb0, bb1);
        let load_in = |func: &mut MachFunction, block| {
            append(
                func,
                block,
                AArch64Opcode::LdrRI,
                vec![vreg(1), vreg(0), imm(0)],
            )
        };
        let branch = |func: &mut MachFunction, from, taken, other| {
            append(
                func,
                from,
                AArch64Opcode::BCond,
                vec![MachOperand::Block(taken), MachOperand::Block(other)],
            );
            func.add_edge(from, taken);
            func.add_edge(from, other);
        };
        let (load, load_block, latch) = match shape {
            InnerCycle::SelfLoopThenLoad | InnerCycle::LoadThenSelfLoop => {
                let early = matches!(shape, InnerCycle::LoadThenSelfLoop);
                let header_load = early.then(|| load_in(&mut func, bb1));
                append(
                    &mut func,
                    bb1,
                    AArch64Opcode::B,
                    vec![MachOperand::Block(bb2)],
                );
                func.add_edge(bb1, bb2);
                append(&mut func, bb2, AArch64Opcode::CmpRI, vec![vreg(9), imm(0)]);
                branch(&mut func, bb2, bb2, bb3);
                match header_load {
                    Some(load) => (load, bb1, bb3),
                    None => (load_in(&mut func, bb3), bb3, bb3),
                }
            }
            InnerCycle::IrreducibleThenLoad => {
                let bb4 = func.create_block();
                branch(&mut func, bb1, bb2, bb3);
                branch(&mut func, bb2, bb3, bb4);
                branch(&mut func, bb3, bb2, bb4);
                (load_in(&mut func, bb4), bb4, bb4)
            }
        };
        let exit = func.create_block();
        append(
            &mut func,
            latch,
            AArch64Opcode::SubRI,
            vec![vreg(8), vreg(8), imm(1)],
        );
        branch(&mut func, latch, exit, bb1);
        append(&mut func, exit, AArch64Opcode::Ret, vec![]);
        (func, load, load_block)
    }

    /// WRONG-CODE REGRESSION: `loop { while c != 0 {} v = *q; ... }`. The load's
    /// block dominates the only latch and exit, yet with `c != 0` the first
    /// iteration spins forever in the inner cycle and never loads. Hoisting
    /// `*q` into the preheader would turn that non-termination into a fault
    /// when `q` is unmapped. Both the reducible and the irreducible inner
    /// cycle must keep the load in place.
    #[test]
    fn test_licm_no_hoist_load_behind_an_inner_cycle() {
        let mut wrong = Vec::new();
        for shape in [
            InnerCycle::SelfLoopThenLoad,
            InnerCycle::IrreducibleThenLoad,
        ] {
            let (mut func, load, load_block) = loop_with_inner_cycle(shape);
            let dom = DomTree::compute(&func);
            let loops = LoopAnalysis::compute(&func, &dom);
            let outer = loops.get_loop(BlockId(1)).expect("outer loop");
            let pos = func
                .block(load_block)
                .insts
                .iter()
                .position(|&id| id == load)
                .expect("the load is in its block");
            if load_guaranteed_to_execute(&func, &dom, outer, (load_block, pos)) {
                wrong.push(format!("{shape:?}: judged guaranteed to execute"));
            }
            LoopInvariantCodeMotion::new().run(&mut func);
            if !func.block(load_block).insts.contains(&load)
                || func.block(func.entry).insts.contains(&load)
            {
                wrong.push(format!("{shape:?}: hoisted into the preheader"));
            }
        }
        assert!(
            wrong.is_empty(),
            "the first iteration can spin before the load: {wrong:?}"
        );
    }

    /// POSITIVE CONTROL: an inner loop AFTER the load cannot stop the first
    /// iteration from reaching it, so the header load still hoists.
    #[test]
    fn test_licm_hoists_load_ahead_of_an_inner_loop() {
        let (mut func, load, load_block) = loop_with_inner_cycle(InnerCycle::LoadThenSelfLoop);
        assert!(LoopInvariantCodeMotion::new().run(&mut func));
        assert!(func.block(func.entry).insts.contains(&load));
        assert!(!func.block(load_block).insts.contains(&load));
    }

    // ---------------------------------------------------------------------
    // Must-execute inside the loop: an in-loop stop that runs before the load
    // ---------------------------------------------------------------------

    /// `TrapBoundsCheckExact v1, v1, #16`: the guard `k <u 16` on the
    /// invariant index `v1`, as isel selects a fused `GuardBoundsCheck`. It is
    /// flagged `IS_BRANCH | IS_TERMINATOR` but falls through to the rest of
    /// its block and has no CFG edge, so the dominance test cannot see it.
    fn bounds_guard(func: &mut MachFunction, block: BlockId) -> InstId {
        append(
            func,
            block,
            AArch64Opcode::TrapBoundsCheckExact,
            vec![vreg(1), vreg(1), imm(16)],
        )
    }

    /// The preheader `bb0`: `v0 = a` (the array pointer), `v1 = k` (the index
    /// the guard checks), then `b bb1`. `v0` is an ordinary pointer, not a
    /// frame slot address, so only the must-execute rule can admit a load
    /// through it.
    fn enter_loop(func: &mut MachFunction, bb0: BlockId, bb1: BlockId) {
        append(func, bb0, AArch64Opcode::MovI, vec![vreg(0), imm(4096)]);
        append(func, bb0, AArch64Opcode::MovI, vec![vreg(1), imm(1 << 44)]);
        finish_preheader_branch(func, bb0, bb1);
    }

    /// `sub v8, v8, #1 ; bcond exit, header`: the counted exit test and back
    /// edge of a do-while latch.
    fn latch_tail(func: &mut MachFunction, latch: BlockId, exit: BlockId, header: BlockId) {
        append(
            func,
            latch,
            AArch64Opcode::SubRI,
            vec![vreg(8), vreg(8), imm(1)],
        );
        append(
            func,
            latch,
            AArch64Opcode::BCond,
            vec![MachOperand::Block(exit), MachOperand::Block(header)],
        );
        append(func, exit, AArch64Opcode::Ret, vec![]);
    }

    /// Run both LICM configurations on a fresh `build()` and require each to
    /// leave every block unchanged.
    fn assert_licm_declines(build: impl Fn() -> MachFunction) {
        let blocks = |func: &MachFunction| -> Vec<Vec<InstId>> {
            func.block_order
                .iter()
                .map(|&b| func.block(b).insts.clone())
                .collect()
        };
        for mut licm in [
            LoopInvariantCodeMotion::new(),
            LoopInvariantCodeMotion::without_frame_speculation(),
        ] {
            let mut func = build();
            let before = blocks(&func);
            assert!(
                !licm.run(&mut func),
                "{licm:?} hoisted a load above an in-loop stop that runs first"
            );
            assert_eq!(blocks(&func), before, "{licm:?} changed the function");
        }
    }

    #[test]
    fn test_licm_no_hoist_load_behind_in_block_trap_carrier() {
        // `loop { s += a[k]; i += 1; if i >= m { break } }` with `k` out of
        // bounds traps on the guard in the first iteration before it reads
        // `a + 8k`. Hoisted to the preheader, that read runs first: a fault
        // (SIGSEGV) where the program trapped (BRK).
        //
        //   bb0: v0 = a ; v1 = k ; b bb1
        //   bb1 (header, latch, exiting): guard ; ldr v2, [v0] ; bcond bb2, bb1
        //   bb2: ret
        assert_licm_declines(|| {
            let (mut func, bb0, bb1, bb2) = single_block_loop();
            enter_loop(&mut func, bb0, bb1);
            bounds_guard(&mut func, bb1);
            load_at(&mut func, bb1, 2, 0, 0);
            finish_loop_tail(&mut func, bb1, bb2);
            func
        });
    }

    #[test]
    fn test_licm_no_hoist_load_behind_header_trap_carrier() {
        // The rustc bridge's shape: MIR's `Assert(BoundsCheck)` ends the
        // header, so the fused guard sits in the header and the load in its
        // success block, which is the latch and the exiting block. That block
        // dominates every latch and exit, yet the guard runs before it.
        //
        //   bb0: v0 = a ; v1 = k ; b bb1
        //   bb1 (header): guard ; b bb2
        //   bb2 (latch, exiting): ldr v2, [v0] ; bcond bb3, bb1
        //   bb3: ret
        assert_licm_declines(|| {
            let mut func = MachFunction::new(
                "licm_header_guard".to_string(),
                Signature::new(vec![], vec![]),
            );
            let bb0 = func.entry;
            let (bb1, bb2, bb3) = (
                func.create_block(),
                func.create_block(),
                func.create_block(),
            );
            func.add_edge(bb0, bb1);
            func.add_edge(bb1, bb2);
            func.add_edge(bb2, bb3);
            func.add_edge(bb2, bb1);
            enter_loop(&mut func, bb0, bb1);
            bounds_guard(&mut func, bb1);
            append(
                &mut func,
                bb1,
                AArch64Opcode::B,
                vec![MachOperand::Block(bb2)],
            );
            load_at(&mut func, bb2, 2, 0, 0);
            latch_tail(&mut func, bb2, bb3, bb1);
            func
        });
    }

    #[test]
    fn test_licm_no_hoist_load_behind_trap_carrier_on_one_arm() {
        // The guard need not dominate the load: an iteration that takes the
        // guarded arm stops before the load as surely as one that always runs
        // the guard.
        //
        //   bb0: v0 = a ; v1 = k ; b bb1
        //   bb1 (header): bcond bb2, bb3
        //   bb2: guard ; b bb4          bb3: b bb4
        //   bb4 (latch, exiting): ldr v2, [v0] ; bcond bb5, bb1
        //   bb5: ret
        assert_licm_declines(|| {
            let mut func =
                MachFunction::new("licm_arm_guard".to_string(), Signature::new(vec![], vec![]));
            let bb0 = func.entry;
            let (bb1, bb2, bb3, bb4, bb5) = (
                func.create_block(),
                func.create_block(),
                func.create_block(),
                func.create_block(),
                func.create_block(),
            );
            func.add_edge(bb0, bb1);
            func.add_edge(bb1, bb2);
            func.add_edge(bb1, bb3);
            func.add_edge(bb2, bb4);
            func.add_edge(bb3, bb4);
            func.add_edge(bb4, bb5);
            func.add_edge(bb4, bb1);
            enter_loop(&mut func, bb0, bb1);
            append(
                &mut func,
                bb1,
                AArch64Opcode::BCond,
                vec![MachOperand::Block(bb2), MachOperand::Block(bb3)],
            );
            bounds_guard(&mut func, bb2);
            append(
                &mut func,
                bb2,
                AArch64Opcode::B,
                vec![MachOperand::Block(bb4)],
            );
            append(
                &mut func,
                bb3,
                AArch64Opcode::B,
                vec![MachOperand::Block(bb4)],
            );
            load_at(&mut func, bb4, 2, 0, 0);
            latch_tail(&mut func, bb4, bb5, bb1);
            func
        });
    }

    #[test]
    fn test_licm_no_hoist_load_behind_mid_block_assert_branch() {
        // `select_assert`'s spelling of an unfused `Assert`: `cmp c, #0 ;
        // b.eq trap` in the middle of the block, then the load. The block is
        // the exiting block and dominates itself, but the branch leaves the
        // loop before the load runs.
        //
        //   bb0: v0 = a ; v1 = k ; b bb1
        //   bb1 (header, latch, exiting): cmp v1, #0 ; b.eq bb3 ;
        //        ldr v2, [v0] ; bcond bb2, bb1
        //   bb2: ret      bb3: brk
        assert_licm_declines(|| {
            let (mut func, bb0, bb1, bb2) = single_block_loop();
            let bb3 = func.create_block();
            func.add_edge(bb1, bb3);
            enter_loop(&mut func, bb0, bb1);
            append(&mut func, bb1, AArch64Opcode::CmpRI, vec![vreg(1), imm(0)]);
            append(
                &mut func,
                bb1,
                AArch64Opcode::BCond,
                vec![imm(0), MachOperand::Block(bb3)],
            );
            load_at(&mut func, bb1, 2, 0, 0);
            finish_loop_tail(&mut func, bb1, bb2);
            append(&mut func, bb3, AArch64Opcode::Brk, vec![]);
            func
        });
    }

    /// POSITIVE CONTROL: a guard that runs only AFTER the load (later in its
    /// block, or in a block the load's block reaches) cannot stop it, so the
    /// load still hoists.
    #[test]
    fn test_licm_hoists_load_that_runs_before_the_trap_carrier() {
        // Same block: ldr ; guard.
        let (mut func, bb0, bb1, bb2) = single_block_loop();
        enter_loop(&mut func, bb0, bb1);
        let load = load_at(&mut func, bb1, 2, 0, 0);
        let carrier = bounds_guard(&mut func, bb1);
        finish_loop_tail(&mut func, bb1, bb2);
        let mut licm = LoopInvariantCodeMotion::without_frame_speculation();
        assert!(licm.run(&mut func), "a load before the guard hoists");
        assert!(func.block(bb0).insts.contains(&load));
        assert!(func.block(bb1).insts.contains(&carrier));

        // Header load, guard in the latch.
        let mut func = MachFunction::new(
            "licm_latch_guard".to_string(),
            Signature::new(vec![], vec![]),
        );
        let bb0 = func.entry;
        let (bb1, bb2, bb3) = (
            func.create_block(),
            func.create_block(),
            func.create_block(),
        );
        func.add_edge(bb0, bb1);
        func.add_edge(bb1, bb2);
        func.add_edge(bb2, bb3);
        func.add_edge(bb2, bb1);
        enter_loop(&mut func, bb0, bb1);
        let load = load_at(&mut func, bb1, 2, 0, 0);
        append(
            &mut func,
            bb1,
            AArch64Opcode::B,
            vec![MachOperand::Block(bb2)],
        );
        let carrier = bounds_guard(&mut func, bb2);
        latch_tail(&mut func, bb2, bb3, bb1);
        let mut licm = LoopInvariantCodeMotion::without_frame_speculation();
        assert!(
            licm.run(&mut func),
            "a header load before a latch guard hoists"
        );
        assert!(func.block(bb0).insts.contains(&load));
        assert!(func.block(bb2).insts.contains(&carrier));
    }
}

#[cfg(test)]
mod region_tests {
    mod eh_call_custody_tests;
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
        let protected = crate::eh_call_custody::ProtectedCalls::collect(func);
        hoist_pure_call_clusters(func, &loops[0], &def_counts, &dom, &protected)
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

/// L14-P6: LICM over a function with many loops costs linearly in them.
#[cfg(test)]
mod many_loops_tests {
    use super::*;
    use trust_cg_ir::{AArch64Opcode, MachFunction, MachInst, MachOperand, RegClass, Signature};

    fn vreg(id: u32) -> MachOperand {
        MachOperand::VReg(VReg::new(id, RegClass::Gpr64))
    }

    fn imm(val: i64) -> MachOperand {
        MachOperand::Imm(val)
    }

    fn push(func: &mut MachFunction, block: BlockId, opcode: AArch64Opcode, ops: Vec<MachOperand>) {
        let id = func.push_inst(MachInst::new(opcode, ops));
        func.append_inst(block, id);
    }

    /// `loops` single-block loops in sequence. Each has a three-instruction
    /// constant chain (`MOVZ` + two `MOVK`), an invariant add of values
    /// defined before every loop, and a loop-variant multiply of the chain's
    /// carrier; the exit of one loop is the preheader of the next.
    fn make_loop_chain(loops: u32) -> MachFunction {
        use AArch64Opcode::*;
        let mut func = MachFunction::new("licm_chain".to_string(), Signature::new(vec![], vec![]));
        let mut pre = func.entry;
        push(&mut func, pre, MovI, vec![vreg(0), imm(10)]);
        push(&mut func, pre, MovI, vec![vreg(1), imm(20)]);
        for k in 0..loops {
            let header = func.create_block();
            let exit = func.create_block();
            let base = 10 + 10 * k;
            let (carrier, invariant, product, counter) = (base, base + 1, base + 2, base + 3);
            push(&mut func, pre, MovI, vec![vreg(counter), imm(100)]);
            push(&mut func, pre, B, vec![MachOperand::Block(header)]);
            func.add_edge(pre, header);
            push(
                &mut func,
                header,
                Movz,
                vec![vreg(carrier), imm(0x1234 + i64::from(k))],
            );
            push(
                &mut func,
                header,
                Movk,
                vec![vreg(carrier), imm(0x5678), imm(16)],
            );
            push(
                &mut func,
                header,
                Movk,
                vec![vreg(carrier), imm(0x9abc), imm(32)],
            );
            push(
                &mut func,
                header,
                AddRR,
                vec![vreg(invariant), vreg(0), vreg(1)],
            );
            push(
                &mut func,
                header,
                MulRR,
                vec![vreg(product), vreg(counter), vreg(carrier)],
            );
            push(
                &mut func,
                header,
                SubRI,
                vec![vreg(counter), vreg(counter), imm(1)],
            );
            push(
                &mut func,
                header,
                BCond,
                vec![MachOperand::Block(exit), MachOperand::Block(header)],
            );
            func.add_edge(header, exit);
            func.add_edge(header, header);
            pre = exit;
        }
        push(&mut func, pre, Ret, vec![]);
        func
    }

    fn same_index(a: &ConstChainIndex, b: &ConstChainIndex) -> bool {
        a.defs == b.defs && a.fmov_gpr_sources == b.fmov_gpr_sources && a.block_pos == b.block_pos
    }

    /// After every loop that hoists, the refreshed constant-chain index is
    /// exactly what a rebuild of the changed function produces.
    #[test]
    fn a_refreshed_chain_index_equals_a_rebuild() {
        for loops in [1, 3, 6] {
            let mut func = make_loop_chain(loops);
            let dom = DomTree::compute(&func);
            let analysis = LoopAnalysis::compute(&func, &dom);
            let mut ordered: Vec<NaturalLoop> = analysis.all_loops().cloned().collect();
            ordered.sort_by_key(|lp| std::cmp::Reverse(lp.depth));
            assert_eq!(ordered.len(), loops as usize);
            let def_counts = build_def_counts(&func);
            let def_map = crate::effects::build_reaching_def_map_by_vreg(&func);
            let layout = LayoutPositions::new();
            let mut chain_index = Some(ConstChainIndex::build(&func));
            let unwind_exits = crate::eh_call_custody::UnwindExits::collect(&func);
            let mut hoisted = 0;
            for lp in &ordered {
                let mut touched = Vec::new();
                if hoist_loop_invariants(
                    &mut func,
                    lp,
                    &dom,
                    &unwind_exits,
                    &def_counts,
                    &def_map,
                    &layout,
                    &mut chain_index,
                    &mut None,
                    false,
                    &mut touched,
                ) {
                    hoisted += 1;
                    let index = chain_index.as_mut().expect("index kept");
                    assert!(index.refresh(&func, &touched));
                    assert!(same_index(index, &ConstChainIndex::build(&func)));
                }
            }
            assert_eq!(hoisted, loops, "every loop hoists its chain");
        }
    }

    /// The whole pass gives the same function whether the index is refreshed
    /// or rebuilt after each hoisting loop.
    #[test]
    fn refreshing_the_chain_index_changes_no_hoist() {
        for loops in [2, 5, 9] {
            let mut refreshed = make_loop_chain(loops);
            let mut rebuilt = refreshed.clone();
            assert!(LoopInvariantCodeMotion::new().run(&mut refreshed));
            FORCE_CHAIN_INDEX_REBUILD.with(|force| force.set(true));
            let changed = LoopInvariantCodeMotion::new().run(&mut rebuilt);
            FORCE_CHAIN_INDEX_REBUILD.with(|force| force.set(false));
            assert!(changed);
            assert_eq!(
                format!("{refreshed:?}"),
                format!("{rebuilt:?}"),
                "{loops} loops"
            );
        }
    }

    /// A loop's body blocks come out in layout order, as filtering
    /// `block_order` gives them, with a unique layout and with one that lists
    /// a block twice.
    #[test]
    fn body_blocks_in_layout_match_the_layout_filter() {
        let func = make_loop_chain(4);
        let mut repeated = func.clone();
        repeated.block_order.push(BlockId(1));
        for f in [&func, &repeated] {
            let dom = DomTree::compute(f);
            let analysis = LoopAnalysis::compute(f, &dom);
            let layout = LayoutPositions::new();
            for lp in analysis.all_loops() {
                let literal: Vec<BlockId> = f
                    .block_order
                    .iter()
                    .copied()
                    .filter(|b| lp.body.contains(b))
                    .collect();
                assert_eq!(layout.body_blocks_in_layout(f, &lp.body), literal);
            }
        }
    }
}
