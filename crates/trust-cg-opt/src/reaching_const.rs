// trust-cg-opt - SOUND reaching-definitions constant resolution (aarch64)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! # Reaching-definitions constant resolution for non-SSA machine IR
//!
//! The machine IR is **not SSA**: a vreg id can be written by several
//! instructions (isel reuses ids; the latch writebacks redefine the iv/acc
//! every iteration). A naive "def map" (`vreg -> the one defining inst`)
//! silently resolves a multi-def vreg to an ARBITRARY def — the exact bug
//! class that miscompiles a pass which then folds the wrong constant.
//!
//! This module answers one question soundly:
//!
//! > **At instruction `u`, does vreg `v` always hold the compile-time
//! > constant `k`?** ([`unique_reaching_const`])
//!
//! via an honest forward may-reach dataflow, per query, specialized to the
//! single vreg id:
//!
//! * **Def model.** An instruction defines `v` iff one of its
//!   [`crate::effects::aarch64_def_operand_positions`] operands is a vreg with
//!   `v`'s id — the same audited role table register allocation is built on
//!   (post/pre-index writebacks, LDP double defs, LSE atomics, `Movk`'s tied
//!   def-use are all modeled there; "operand 0 is the def" is NOT assumed).
//!   Defs are matched by **id only**, ignoring the register class: a W-view
//!   write clobbers the X view and vice versa, so class-blind matching only
//!   ever ADDS reaching defs (fail-closed for uniqueness).
//! * **GEN/KILL.** Per block, for the queried id: `GEN[b]` = the LAST
//!   instruction in `b` defining the id (later defs kill earlier ones inside
//!   the straight-line block — exact); `KILL[b]` = everything, whenever the
//!   block contains any def. Blocks without a def pass their input through:
//!   `OUT[b] = GEN[b].is_some() ? {GEN[b]} : IN[b]`, with
//!   `IN[b] = ⋃ OUT[preds]` — the textbook union/worklist iteration to a
//!   fixpoint over the blocks reachable from `entry`. Worklist dependents are
//!   derived from those SAME predecessor lists, rather than trusting the
//!   reverse `succs` metadata to agree while CFG rewrites are in flight.
//! * **Uninitialized paths.** `IN[entry]` is seeded with a synthetic
//!   `DefSite::Uninit` so any path on which `v` is never written (function
//!   arguments arrive in physical registers and are copied — but the copy is a
//!   def; a genuinely def-free path means the value is unknowable) poisons the
//!   query to `None`.
//! * **CFG coherence.** An in-block answer is independent of CFG metadata.
//!   Cross-block queries require `preds` and `succs` to be exact inverses over
//!   reachable blocks and otherwise return `None`; a one-sided executable edge
//!   could hide a bypass path or an additional reaching definition.
//! * **Uniqueness is established at the USE POINT**: reaching set at `u` = the
//!   last def of the id textually before `u` inside `u`'s block if one exists
//!   (straight-line — exact), else `IN[block(u)]`. The query succeeds only if
//!   that set is EXACTLY one real instruction. Two reaching defs (e.g. the id
//!   is redefined inside a loop, so the guard's def AND the loop's def both
//!   reach the header) ⇒ `None`. An `Uninit` member ⇒ `None`.
//! * **Folding.** The unique def must be a proof-covered, shift-zero `Movz` or
//!   `Movn` (16-bit immediate; an explicit `lsl #0` is accepted, while nonzero
//!   base shifts fail closed); each `Movk` on top recursively requires
//!   the value REACHING THE MOVK (its tied def-use input) to itself resolve
//!   uniquely — the standard `Movz`/`Movn`+`Movk` materialization chain and
//!   nothing else. Any
//!   other opcode, malformed immediate, or ambiguity ⇒ `None`. Writes through
//!   a `Gpr32` destination mask to 32 bits mid-chain (a W write zeroes the X
//!   upper half), and the final value is truncated to the QUERIED vreg's
//!   class width — bit-exact hardware semantics.
//!
//! `None` always means "not provably a unique constant" and callers MUST
//! fail closed (keep the scalar loop / skip the fold). O(defs x blocks) per
//! query — trivial at machine-function sizes, and only consulted on the rare
//! recognition paths where the cheap single-def map came up empty.

use std::collections::{HashMap, HashSet, VecDeque};

use trust_cg_ir::{
    AArch64Opcode, BlockId, InstId, MachFunction, MachInst, MachOperand, RegClass, VReg,
};

use crate::effects::aarch64_def_operand_positions;

/// A definition site reaching a program point.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
enum DefSite {
    /// Function entry reached with no definition of the id on some path —
    /// the value is unknowable; poisons any query it reaches.
    Uninit,
    /// The instruction that (last) writes the id.
    Inst(InstId),
}

/// Maximum `Movz` + `Movk` chain length followed while folding (a 64-bit
/// constant needs at most 1 `Movz` + 3 `Movk`; anything deeper is not the
/// isel materialization idiom and bails).
const MAX_CHAIN: u32 = 4;

/// The vreg ids `inst` writes, per the audited operand-role table.
///
/// SINGLE SOURCE OF TRUTH for the def model described in the module docs: the
/// [`ReachingCtx`] index is built from this and nothing else, so there is no
/// second copy of "what counts as a definition" that could drift out of step —
/// such a divergence would be a soundness bug, not a performance one.
/// Class-blind by design (see the module docs). May yield the same id twice when
/// an instruction names it at two def operand positions; callers that build sets
/// must tolerate that.
fn defined_ids(inst: &MachInst) -> impl Iterator<Item = u32> + '_ {
    aarch64_def_operand_positions(inst.opcode, inst.operands.len())
        .into_iter()
        .filter_map(|pos| match inst.operands.get(pos) {
            Some(MachOperand::VReg(v)) => Some(v.id),
            _ => None,
        })
}

/// True iff `inst` writes a vreg with `id`. Expressed through [`defined_ids`],
/// so the scan path and the indexed path share ONE def model.
fn defines_id(func: &MachFunction, inst_id: InstId, id: u32) -> bool {
    defined_ids(func.inst(inst_id)).any(|defined| defined == id)
}

/// The block containing `inst`, by scan. Used only on the one-shot path, where
/// building a whole-function index to answer a single query is the more
/// expensive option — see [`reaching_defs_at`].
fn block_of(func: &MachFunction, inst: InstId) -> Option<BlockId> {
    for (idx, block) in func.blocks.iter().enumerate() {
        if block.insts.contains(&inst) {
            return Some(BlockId(idx as u32));
        }
    }
    None
}

/// The blocks reachable from `func.entry` via CFG successor edges. Only these
/// participate in the dataflow; instructions parked in unreachable blocks (or
/// unlinked from every block) cannot execute and must not contribute defs.
fn reachable_blocks(func: &MachFunction) -> HashSet<BlockId> {
    let mut seen: HashSet<BlockId> = HashSet::new();
    let mut work = vec![func.entry];
    while let Some(b) = work.pop() {
        if !seen.insert(b) {
            continue;
        }
        for &s in &func.block(b).succs {
            if !seen.contains(&s) {
                work.push(s);
            }
        }
    }
    seen
}

/// Function-wide indexes shared by a batch of reaching-defs queries.
///
/// # Why this exists
///
/// Every query used to redo three whole-function walks before doing any actual
/// dataflow: `reachable_blocks` (a full CFG traversal plus a fresh allocation),
/// `block_of` (a scan of every block's instruction list to locate the use), and
/// a linear `insts.iter().position(..)` to find the use's index. All three are
/// invariant across a batch of queries against an unmutated function.
///
/// A pass that resolves one constant per candidate therefore paid O(n) per site
/// with O(n) sites. Measured on a 3200-statement function, `mul-shift-reduce` —
/// which calls `unique_reaching_const` for every multiply — cost 253ms and
/// scaled 4.07x for a 2x input, i.e. cleanly quadratic, making it 59% of the
/// optimization budget once the scheduler quadratics were fixed.
///
/// Building this once and reusing it across the batch makes each query O(log k)
/// in the number of defs of the queried vreg, plus the (unchanged) cross-block
/// fixpoint.
///
/// # Validity
///
/// The indexes describe ONE function state. A caller must rebuild after any
/// mutation. `unique_reaching_const` keeps the old signature by building a fresh
/// context per call, so existing callers are bit-for-bit unaffected.
pub(crate) struct ReachingCtx {
    reachable: HashSet<BlockId>,
    /// Whether the two redundant CFG edge views agree over executable blocks.
    /// Cross-block answers fail closed when this is false; see
    /// [`reachable_cfg_is_symmetric`].
    cfg_symmetric: bool,
    /// `InstId -> (containing block, index within that block)`.
    loc: HashMap<InstId, (BlockId, usize)>,
    /// `block -> vreg id -> ascending in-block positions that define it`.
    defs: HashMap<BlockId, HashMap<u32, Vec<usize>>>,
    /// The ALL-IDS cross-block solution, built lazily on the first cross-block
    /// query and answering every later one by projection.
    ///
    /// Valid for exactly as long as the rest of the context: it describes ONE
    /// function state, and a caller must rebuild after any mutation. Interior
    /// mutability because queries take `&ReachingCtx`.
    all_ids: std::cell::OnceCell<AllIdsReaching>,
}

/// The reaching-definitions solution for EVERY vreg id at once.
///
/// # Why all ids at once
///
/// The per-id fixpoint is O(blocks) per queried id, so a recognition sweep that
/// resolves one constant per candidate — with a DISTINCT id per candidate, the
/// `many_fns` shape — pays O(ids x blocks): measured at 1000 fixpoint solves /
/// 123.3ms for one compile, scaling 3.98x for a 2x input, the backend's last
/// quadratic. Per-id memoization cannot help (no id repeats), and an
/// adversarially-reviewed single-def dominance shortcut turned out never to
/// apply (every hot query is multi-def). What removes the quadratic is solving
/// the PRODUCT LATTICE once: one bitvector fixpoint whose universe is every GEN
/// site plus every id's Uninit marker, then answering each query by projecting
/// `IN[use_block]` onto the queried id's bits.
///
/// # Exactness
///
/// Projection of the product solution onto one id IS the per-id solution: the
/// join (bitwise OR over the same reachable-filtered `preds`), the transfer
/// (per-block kill of exactly that id's bits, gen of its last in-block site)
/// and the seed (entry carries every Uninit bit) all commute with restriction
/// to one id's coordinates. The differential harness
/// (`reaching_const_differential`) enforces this against the retained per-id
/// path and an independent oracle over 13,603 queries, including asymmetric
/// and irreducible CFGs; the one-shot `ctx = None` path still runs the per-id
/// fixpoint verbatim, so the two formulations police each other in every run
/// of the suite.
///
/// # Universe layout
///
/// * one bit per (block, id) GEN site — the LAST def of `id` in that block;
/// * one Uninit bit per id that has at least one reachable GEN site;
/// * one SHARED Uninit bit for every id with no reachable def at all: such ids
///   are never killed anywhere, so their Uninit propagation is identical and
///   one bit serves them all.
struct AllIdsReaching {
    /// Site bit index -> the GEN instruction it stands for.
    site_insts: Vec<InstId>,
    /// id -> (its Uninit bit, the site bits belonging to it).
    per_id: HashMap<u32, (usize, Vec<usize>)>,
    /// The shared Uninit bit for ids with no reachable GEN site.
    shared_uninit: usize,
    /// `IN[b]` for every reachable block, as packed 64-bit words.
    in_sets: HashMap<BlockId, Vec<u64>>,
}

impl AllIdsReaching {
    fn build(func: &MachFunction, ctx: &ReachingCtx) -> Self {
        // ---- Universe ----
        // Deterministic bit assignment: reachable blocks in ascending BlockId,
        // ids within a block in ascending order. (The solution is a set union,
        // so determinism here is for debuggability, not correctness.)
        let mut reachable_sorted: Vec<BlockId> = ctx.reachable.iter().copied().collect();
        reachable_sorted.sort_by_key(|b| b.0);

        let mut site_insts: Vec<InstId> = Vec::new();
        let mut per_id: HashMap<u32, (usize, Vec<usize>)> = HashMap::new();
        // (block -> its gen (site_bit, id) pairs), for transfer construction.
        let mut block_gens: HashMap<BlockId, Vec<(usize, u32)>> = HashMap::new();

        let mut ids_in_block: Vec<u32> = Vec::new();
        for &b in &reachable_sorted {
            let Some(per_block) = ctx.defs.get(&b) else {
                continue;
            };
            ids_in_block.clear();
            ids_in_block.extend(per_block.keys().copied());
            ids_in_block.sort_unstable();
            for &id in &ids_in_block {
                let positions = &per_block[&id];
                let last_pos = *positions.last().expect("non-empty by construction");
                let site_bit = site_insts.len();
                site_insts.push(func.block(b).insts[last_pos]);
                per_id
                    .entry(id)
                    .or_insert((usize::MAX, Vec::new()))
                    .1
                    .push(site_bit);
                block_gens.entry(b).or_default().push((site_bit, id));
            }
        }
        // Uninit bits after all site bits.
        let mut next_bit = site_insts.len();
        let mut id_list: Vec<u32> = per_id.keys().copied().collect();
        id_list.sort_unstable();
        for id in id_list {
            per_id.get_mut(&id).expect("just listed").0 = next_bit;
            next_bit += 1;
        }
        let shared_uninit = next_bit;
        next_bit += 1;
        let words = next_bit.div_ceil(64);

        // ---- Per-block transfer masks ----
        let set_bit = |v: &mut [u64], bit: usize| v[bit / 64] |= 1u64 << (bit % 64);
        let mut kill: HashMap<BlockId, Vec<u64>> = HashMap::new();
        let mut gen_masks: HashMap<BlockId, Vec<u64>> = HashMap::new();
        for (&b, gens) in &block_gens {
            let k = kill.entry(b).or_insert_with(|| vec![0; words]);
            for &(_, id) in gens {
                let (uninit_bit, site_bits) = &per_id[&id];
                set_bit(k, *uninit_bit);
                for &sb in site_bits {
                    set_bit(k, sb);
                }
            }
            let g = gen_masks.entry(b).or_insert_with(|| vec![0; words]);
            for &(site_bit, _) in gens {
                set_bit(g, site_bit);
            }
        }

        // ---- Fixpoint ----
        // IN[entry] seeds every Uninit bit (per-id and shared); everything else
        // starts empty. Iterate reachable blocks in a fixed order until stable;
        // sets only grow, so termination is bounded by the lattice height.
        let mut in_sets: HashMap<BlockId, Vec<u64>> = HashMap::new();
        for &b in &reachable_sorted {
            in_sets.insert(b, vec![0; words]);
        }
        {
            let entry_in = in_sets.get_mut(&func.entry).expect("entry is reachable");
            for (_, &(uninit_bit, _)) in per_id.iter() {
                entry_in[uninit_bit / 64] |= 1u64 << (uninit_bit % 64);
            }
            entry_in[shared_uninit / 64] |= 1u64 << (shared_uninit % 64);
        }
        let empty: Vec<u64> = vec![0; words];
        let mut out_buf: Vec<u64> = vec![0; words];
        let mut changed = true;
        while changed {
            changed = false;
            for &b in &reachable_sorted {
                // The ENTRY block is not exempt: its Uninit seed is already in
                // `in_sets` and the merge below only ever ORs, so the seed
                // survives — but a BACK EDGE into entry contributes its
                // predecessors' OUT exactly as the per-id fixpoint does. The
                // differential harness caught the version of this loop that
                // skipped entry: `entry_use_with_back_edge_def` expects
                // {Uninit, Inst(d)} and the skip produced {Uninit}.
                out_buf.iter_mut().for_each(|w| *w = 0);
                for &p in &func.block(b).preds {
                    if !ctx.reachable.contains(&p) {
                        continue;
                    }
                    // OUT[p] = (IN[p] & !kill[p]) | gen[p], computed on the fly.
                    let pin = in_sets.get(&p).expect("reachable => present");
                    let pkill = kill.get(&p).unwrap_or(&empty);
                    let pgen = gen_masks.get(&p).unwrap_or(&empty);
                    for w in 0..words {
                        out_buf[w] |= (pin[w] & !pkill[w]) | pgen[w];
                    }
                }
                let cur = in_sets.get_mut(&b).expect("reachable => present");
                let mut grew = false;
                for w in 0..words {
                    let merged = cur[w] | out_buf[w];
                    if merged != cur[w] {
                        cur[w] = merged;
                        grew = true;
                    }
                }
                if grew {
                    changed = true;
                }
            }
        }

        Self {
            site_insts,
            per_id,
            shared_uninit,
            in_sets,
        }
    }

    /// Project `IN[use_block]` onto one id — exactly `assemble_in`'s answer.
    fn project(&self, use_block: BlockId, id: u32) -> HashSet<DefSite> {
        let mut result = HashSet::new();
        let Some(inb) = self.in_sets.get(&use_block) else {
            return result;
        };
        let bit = |b: usize| inb[b / 64] & (1u64 << (b % 64)) != 0;
        match self.per_id.get(&id) {
            Some(&(uninit_bit, ref site_bits)) => {
                if bit(uninit_bit) {
                    result.insert(DefSite::Uninit);
                }
                for &sb in site_bits {
                    if bit(sb) {
                        result.insert(DefSite::Inst(self.site_insts[sb]));
                    }
                }
            }
            None => {
                if bit(self.shared_uninit) {
                    result.insert(DefSite::Uninit);
                }
            }
        }
        result
    }
}

impl ReachingCtx {
    pub(crate) fn new(func: &MachFunction) -> Self {
        let reachable = reachable_blocks(func);
        let cfg_symmetric = reachable_cfg_is_symmetric(func, &reachable);
        let mut loc: HashMap<InstId, (BlockId, usize)> = HashMap::new();
        let mut defs: HashMap<BlockId, HashMap<u32, Vec<usize>>> = HashMap::new();
        for (idx, block) in func.blocks.iter().enumerate() {
            let bid = BlockId(idx as u32);
            let per_block = defs.entry(bid).or_default();
            for (pos, &inst_id) in block.insts.iter().enumerate() {
                // `block_of` returned the FIRST block containing the id, so a
                // duplicate linkage must not be re-pointed at a later block.
                loc.entry(inst_id).or_insert((bid, pos));
                for id in defined_ids(func.inst(inst_id)) {
                    let positions = per_block.entry(id).or_default();
                    // The def model is a PREDICATE over instructions, so an
                    // instruction naming the same id at two def operand
                    // positions must still contribute a single position.
                    if positions.last() != Some(&pos) {
                        positions.push(pos);
                    }
                }
            }
        }
        Self {
            reachable,
            cfg_symmetric,
            loc,
            defs,
            all_ids: std::cell::OnceCell::new(),
        }
    }

    /// Ascending in-block positions defining `id` in `block`.
    fn def_positions(&self, block: BlockId, id: u32) -> Option<&Vec<usize>> {
        self.defs.get(&block)?.get(&id)
    }
}

/// The set of definitions of vreg-id `id` reaching instruction `use_inst`
/// (immediately BEFORE it executes). Fail-closed: `None` when `use_inst`
/// is not linked into a reachable block.
/// DIAGNOSTIC (default off, `TCG_TIME_BOI=1`): splits this function's cost into
/// the cheap in-block early-return and the whole-function cross-block fixpoint,
/// so their shares are measured rather than argued.
pub(crate) static RD_INBLOCK_NANOS: std::sync::atomic::AtomicU64 =
    std::sync::atomic::AtomicU64::new(0);
pub(crate) static RD_INBLOCK_HITS: std::sync::atomic::AtomicU64 =
    std::sync::atomic::AtomicU64::new(0);
pub(crate) static RD_FIXPOINT_NANOS: std::sync::atomic::AtomicU64 =
    std::sync::atomic::AtomicU64::new(0);
pub(crate) static RD_FIXPOINT_HITS: std::sync::atomic::AtomicU64 =
    std::sync::atomic::AtomicU64::new(0);
/// Queries answered from an already-built all-ids product solution.
pub(crate) static RD_MEMO_HITS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

/// `ctx = Some(..)` uses the shared index; `None` uses the original scans.
///
/// BOTH PATHS ARE REQUIRED. The index amortizes beautifully across many queries
/// against one function state, but building it to answer a SINGLE query is
/// strictly more expensive than the scans it replaces — it materializes two
/// nested hash maps over every instruction. Routing one-shot callers through it
/// regressed `mul-shift-reduce` on block-dense code from 49.4ms to 88.4ms
/// (branchy, 200 blocks), an 18-24% whole-compile loss, because every query
/// after the first mutation rebuilt the whole index.
///
/// So the one-shot path keeps the scans, and only a caller that can hold a
/// context across many queries pays for the index. The def model is shared via
/// [`defined_ids`], so the two paths cannot disagree about what a definition is.
fn reaching_defs_at(
    func: &MachFunction,
    ctx: Option<&ReachingCtx>,
    use_inst: InstId,
    id: u32,
) -> Option<HashSet<DefSite>> {
    let t_start = std::time::Instant::now();
    let (use_block, use_pos) = match ctx {
        Some(ctx) => ctx.loc.get(&use_inst).copied()?,
        None => {
            let b = block_of(func, use_inst)?;
            let p = func.block(b).insts.iter().position(|&i| i == use_inst)?;
            (b, p)
        }
    };
    let owned_reachable;
    let reachable: &HashSet<BlockId> = match ctx {
        Some(ctx) => &ctx.reachable,
        None => {
            owned_reachable = reachable_blocks(func);
            &owned_reachable
        }
    };
    if !reachable.contains(&use_block) {
        return None;
    }

    // In-block: the last def strictly before the use kills everything else
    // (straight-line execution within a block — exact). Indexed positions are
    // ascending, so the entry below the partition point is the same instruction
    // the backward scan finds.
    let in_block = match ctx {
        Some(ctx) => ctx.def_positions(use_block, id).and_then(|positions| {
            let below = positions.partition_point(|&p| p < use_pos);
            (below > 0).then(|| func.block(use_block).insts[positions[below - 1]])
        }),
        None => func.block(use_block).insts[..use_pos]
            .iter()
            .rev()
            .copied()
            .find(|&i| defines_id(func, i, id)),
    };
    if let Some(d) = in_block {
        if crate::neon_array::boi_timing_enabled() {
            RD_INBLOCK_NANOS.fetch_add(
                t_start.elapsed().as_nanos() as u64,
                std::sync::atomic::Ordering::Relaxed,
            );
            RD_INBLOCK_HITS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        }
        return Some(HashSet::from([DefSite::Inst(d)]));
    }

    // `preds` and `succs` are redundant public metadata and can temporarily
    // drift during a CFG rewrite. A cross-block fact cannot pick one view and
    // remain sound: a succ-only path may bypass the purported definition,
    // while a pred-only dependency can add a reaching definition. Preserve the
    // exact in-block answer above, but otherwise decline until the CFG is
    // coherent. The indexed path computes this once; one-shot callers pay the
    // O(edges) check only when they actually need cross-block dataflow.
    let cfg_symmetric = match ctx {
        Some(ctx) => ctx.cfg_symmetric,
        None => reachable_cfg_is_symmetric(func, reachable),
    };
    if !cfg_symmetric {
        return None;
    }

    // Cross-block. The GEN map and the OUT fixpoint depend ONLY on `id` and the
    // function state — NOT on the use site — so with a context they are computed
    // once per vreg id and reused by every later query for that id.
    //
    // Measured on `branchy`: the in-block fast path essentially never hits (1 hit
    // across the whole compile) and every query ran this fixpoint —
    // 199 hits/31.3ms at 200 rungs, 399 hits/134.0ms at 400. Hits grow linearly
    // while per-hit cost doubles with block count, i.e. O(candidates x blocks).
    let timing = crate::neon_array::boi_timing_enabled();
    let out = match ctx {
        Some(ctx) => {
            // ALL-IDS PATH. Solve the product lattice once for the whole
            // context, then answer this and every later query by projection.
            // See `AllIdsReaching` for why this is exact and why it exists.
            let solved = ctx.all_ids.get().is_some();
            let all = ctx.all_ids.get_or_init(|| AllIdsReaching::build(func, ctx));
            if timing {
                if solved {
                    RD_MEMO_HITS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                } else {
                    RD_FIXPOINT_NANOS.fetch_add(
                        t_start.elapsed().as_nanos() as u64,
                        std::sync::atomic::Ordering::Relaxed,
                    );
                    RD_FIXPOINT_HITS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                }
            }
            return Some(all.project(use_block, id));
        }
        None => compute_out(func, None, reachable, id),
    };

    // IN[use_block], recomputed from the fixpoint OUTs.
    let inb = assemble_in(func, reachable, &out, use_block);
    if crate::neon_array::boi_timing_enabled() {
        RD_FIXPOINT_NANOS.fetch_add(
            t_start.elapsed().as_nanos() as u64,
            std::sync::atomic::Ordering::Relaxed,
        );
        RD_FIXPOINT_HITS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    }
    Some(inb)
}

/// The single definition of `id` reaching `use_inst`, if EXACTLY one does and
/// no uninitialized path reaches it. Anything else ⇒ `None` (fail closed).
fn unique_reaching_def_with(
    func: &MachFunction,
    ctx: Option<&ReachingCtx>,
    use_inst: InstId,
    id: u32,
) -> Option<InstId> {
    let defs = reaching_defs_at(func, ctx, use_inst, id)?;
    if defs.len() != 1 {
        return None;
    }
    match defs.into_iter().next()? {
        DefSite::Inst(d) => Some(d),
        DefSite::Uninit => None,
    }
}

/// The one-shot form of [`unique_reaching_def_with`].
///
/// Crate-visible so passes that must chase ONE copy level (e.g.
/// `resid_collapse`'s entry-constant resolution through the scalar-unroll tail
/// writeback `MovR iv, t`) can do so on the same audited reaching-defs engine
/// instead of a naive def map. The scan path deliberately avoids constructing a
/// whole-function [`ReachingCtx`] for a single query.
pub(crate) fn unique_reaching_def(
    func: &MachFunction,
    use_inst: InstId,
    id: u32,
) -> Option<InstId> {
    unique_reaching_def_with(func, None, use_inst, id)
}

fn imm_of(op: &MachOperand) -> Option<i64> {
    match op {
        MachOperand::Imm(v) => Some(*v),
        _ => None,
    }
}

/// Parse a move-wide `[dst, imm16(, lsl)]` operand list into
/// `(dst, imm, shift)` with hardware-valid ranges; anything malformed ⇒ `None`.
///
/// This is crate-visible so other optimization passes do not accidentally
/// accept a shifted `Movz` while reading operand 1 as the complete value.
pub(crate) fn parse_move_wide_inst(inst: &MachInst) -> Option<(VReg, u64, u32)> {
    if inst.operands.len() != 2 && inst.operands.len() != 3 {
        return None;
    }
    let dst = match inst.operands.first()? {
        MachOperand::VReg(v) => *v,
        _ => return None,
    };
    let imm = imm_of(inst.operands.get(1)?)?;
    if !(0..=0xFFFF).contains(&imm) {
        return None;
    }
    let shift = match inst.operands.get(2) {
        None => 0,
        Some(op) => imm_of(op)?,
    };
    if !matches!(shift, 0 | 16 | 32 | 48) {
        return None;
    }
    let width = match dst.class {
        RegClass::Gpr32 => 32,
        RegClass::Gpr64 => 64,
        _ => return None,
    };
    if shift >= width {
        return None; // W-form MOVZ/MOVK only encodes lsl #0/#16
    }
    Some((dst, imm as u64, shift as u32))
}

/// Decode an encoder-emittable canonical `Movz`.
///
/// The publication proof inventory covers only the shift-zero form.  A
/// nonzero-shift `Movz` is therefore deliberately not a constant fact here:
/// optimizer consumers must leave it untouched so the encoder can reject the
/// unsupported MachIR form instead of accidentally normalizing it away.
pub(crate) fn movz_value(inst: &MachInst) -> Option<(VReg, u64)> {
    if inst.opcode != AArch64Opcode::Movz {
        return None;
    }
    let (dst, imm, shift) = parse_move_wide_inst(inst)?;
    (shift == 0).then_some((dst, imm))
}

/// Decode an encoder-emittable canonical `Movn` (shift-zero only).
pub(crate) fn movn_value(inst: &MachInst) -> Option<(VReg, u64)> {
    if inst.opcode != AArch64Opcode::Movn {
        return None;
    }
    let (dst, imm, shift) = parse_move_wide_inst(inst)?;
    if shift != 0 {
        return None;
    }
    let width_mask = if dst.class == RegClass::Gpr32 {
        0xFFFF_FFFF
    } else {
        u64::MAX
    };
    Some((dst, (!imm) & width_mask))
}

/// Apply one well-formed `Movk` to an already-known value.
pub(crate) fn apply_movk(inst: &MachInst, expected_dst: VReg, current: u64) -> Option<u64> {
    if inst.opcode != AArch64Opcode::Movk {
        return None;
    }
    let (dst, imm, shift) = parse_move_wide_inst(inst)?;
    if dst != expected_dst {
        return None;
    }
    let field_mask = 0xFFFFu64 << shift;
    let mut value = (current & !field_mask) | (imm << shift);
    if dst.class == RegClass::Gpr32 {
        value &= 0xFFFF_FFFF;
    }
    Some(value)
}

/// Fold the 64-bit register value produced by the unique `Movz`(+`Movk`) chain
/// reaching `use_inst` for vreg-id `id`. Recursion: each `Movk` reads the
/// value reaching ITSELF (its tied def-use input), which must in turn resolve
/// uniquely.
fn fold_chain(
    func: &MachFunction,
    ctx: Option<&ReachingCtx>,
    use_inst: InstId,
    id: u32,
    depth: u32,
) -> Option<u64> {
    if depth == 0 {
        return None;
    }
    let d = unique_reaching_def_with(func, ctx, use_inst, id)?;
    let inst = func.inst(d);
    match inst.opcode {
        AArch64Opcode::Movz => {
            let (dst, value) = movz_value(inst)?;
            if dst.id != id {
                return None;
            }
            let mut v = value;
            if dst.class == RegClass::Gpr32 {
                v &= 0xFFFF_FFFF;
            }
            Some(v)
        }
        AArch64Opcode::Movn => {
            // MOVN Rd, #imm16, LSL #shift -> Rd = NOT(imm16 << shift). Like
            // `Movz` it is a FULL write (all bits established), so it is a fold
            // base case — no recursion. This is the isel materialization for a
            // small NEGATIVE constant (`-3` -> `MOVN #2`). W-form NOTs within 32
            // bits (upper half zeroed), matching the encoder.
            let (dst, value) = movn_value(inst)?;
            if dst.id != id {
                return None;
            }
            Some(value)
        }
        AArch64Opcode::Movk => {
            let dst = inst.operands.first()?.as_vreg()?;
            if dst.id != id {
                return None;
            }
            // The Movk's input is the value of the SAME id reaching the Movk.
            let prev = fold_chain(func, ctx, d, id, depth - 1)?;
            apply_movk(inst, dst, prev)
        }
        _ => None,
    }
}

/// **The public query**: the compile-time constant `v` is GUARANTEED to hold
/// when `use_inst` executes, or `None`.
///
/// `Some(k)` requires ALL of:
/// * `use_inst` is linked into a block reachable from entry;
/// * EXACTLY ONE definition of `v`'s id reaches `use_inst` (no uninitialized
///   path, no second def — e.g. a redefinition inside a loop body reaching
///   around the back edge);
/// * that definition is a well-formed `Movz` immediate, or a `Movk` whose own
///   input resolves recursively under the same rules (the isel `Movz`+`Movk`
///   materialization chain).
///
/// The value is truncated to `v`'s register-class width (`Gpr32` reads see
/// the low 32 bits) and returned zero-extended in an `i64`. `None` means
/// "not provably constant" — callers must fail closed.
pub fn unique_reaching_const(func: &MachFunction, use_inst: InstId, v: VReg) -> Option<i64> {
    resolve_const(func, None, use_inst, v)
}

/// [`unique_reaching_const`] against a caller-owned [`ReachingCtx`].
///
/// Identical results; the context just hoists the three whole-function walks out
/// of the query so a pass resolving one constant per candidate is linear in the
/// function rather than quadratic. The caller is responsible for rebuilding the
/// context after any mutation — see [`ReachingCtx`].
pub(crate) fn unique_reaching_const_with(
    func: &MachFunction,
    ctx: &ReachingCtx,
    use_inst: InstId,
    v: VReg,
) -> Option<i64> {
    resolve_const(func, Some(ctx), use_inst, v)
}

fn resolve_const(
    func: &MachFunction,
    ctx: Option<&ReachingCtx>,
    use_inst: InstId,
    v: VReg,
) -> Option<i64> {
    let mut val = fold_chain(func, ctx, use_inst, v.id, MAX_CHAIN)?;
    if v.class.size_bits() <= 32 {
        val &= 0xFFFF_FFFF;
    }
    Some(val as i64)
}

// Differential harness: an independent oracle + pointed CFG corpus + a runner
// asserting per-query agreement across the one-shot, fresh-ctx and warm-product
// paths. Declared HERE (not in lib.rs) so it is a child of this module and can
// see `DefSite`, `reaching_defs_at` and `ReachingCtx`'s internals — the layer
// the differential must observe. See the module docs for what it pins.
#[cfg(test)]
#[path = "reaching_const_differential.rs"]
mod differential;

#[cfg(test)]
mod tests {
    use super::*;
    use trust_cg_ir::{MachInst, Signature};

    fn v32(id: u32) -> VReg {
        VReg::new(id, RegClass::Gpr32)
    }
    fn v64(id: u32) -> VReg {
        VReg::new(id, RegClass::Gpr64)
    }
    fn vr(v: VReg) -> MachOperand {
        MachOperand::VReg(v)
    }
    fn im(x: i64) -> MachOperand {
        MachOperand::Imm(x)
    }
    fn bl(b: BlockId) -> MachOperand {
        MachOperand::Block(b)
    }

    fn new_func() -> MachFunction {
        MachFunction::new("t".into(), Signature::new(vec![], vec![]))
    }

    fn emit(f: &mut MachFunction, b: BlockId, op: AArch64Opcode, ops: Vec<MachOperand>) -> InstId {
        let id = f.push_inst(MachInst::new(op, ops));
        f.append_inst(b, id);
        id
    }

    /// Single Movz def dominating the use -> Some(value).
    #[test]
    fn single_def_const_resolves() {
        let mut f = new_func();
        let e = f.entry;
        let x = v32(0);
        let y = v32(1);
        emit(&mut f, e, AArch64Opcode::Movz, vec![vr(x), im(41)]);
        let use_i = emit(&mut f, e, AArch64Opcode::AddRR, vec![vr(y), vr(x), vr(x)]);
        assert_eq!(unique_reaching_const(&f, use_i, x), Some(41));
    }

    /// Nonzero-shift Movz is deliberately not an optimizer constant fact.
    #[test]
    fn shifted_movz_is_rejected() {
        let mut f = new_func();
        let e = f.entry;
        let x = v64(0);
        let y = v64(1);
        emit(&mut f, e, AArch64Opcode::Movz, vec![vr(x), im(7), im(16)]);
        let use_i = emit(&mut f, e, AArch64Opcode::AddRR, vec![vr(y), vr(x), vr(x)]);
        assert_eq!(unique_reaching_const(&f, use_i, x), None);
    }

    #[test]
    fn explicit_shift_zero_movz_resolves() {
        let mut f = new_func();
        let e = f.entry;
        let x = v64(0);
        let y = v64(1);
        emit(&mut f, e, AArch64Opcode::Movz, vec![vr(x), im(7), im(0)]);
        let use_i = emit(&mut f, e, AArch64Opcode::AddRR, vec![vr(y), vr(x), vr(x)]);
        assert_eq!(unique_reaching_const(&f, use_i, x), Some(7));
    }

    #[test]
    fn shifted_movn_is_rejected() {
        let mut f = new_func();
        let e = f.entry;
        let x = v64(0);
        let y = v64(1);
        emit(&mut f, e, AArch64Opcode::Movn, vec![vr(x), im(7), im(16)]);
        let use_i = emit(&mut f, e, AArch64Opcode::AddRR, vec![vr(y), vr(x), vr(x)]);
        assert_eq!(unique_reaching_const(&f, use_i, x), None);
    }

    #[test]
    fn out_of_range_or_extra_move_wide_operands_are_rejected() {
        let x = v64(0);
        let f = VReg::new(1, RegClass::Fpr64);
        let malformed = [
            MachInst::new(AArch64Opcode::Movz, vec![vr(x), im(0x1_0000)]),
            MachInst::new(AArch64Opcode::Movz, vec![vr(x), im(7), im(0), im(0)]),
            MachInst::new(AArch64Opcode::Movk, vec![vr(x), im(7), im(8)]),
            MachInst::new(AArch64Opcode::Movz, vec![vr(f), im(7)]),
        ];
        assert_eq!(movz_value(&malformed[0]), None);
        assert_eq!(movz_value(&malformed[1]), None);
        assert_eq!(apply_movk(&malformed[2], x, 0), None);
        assert_eq!(movz_value(&malformed[3]), None);
    }

    /// The full Movz+Movk chain (puzzle's 500001 = 41249 | 7<<16).
    #[test]
    fn movz_movk_chain_resolves() {
        let mut f = new_func();
        let e = f.entry;
        let x = v64(0);
        let y = v64(1);
        emit(&mut f, e, AArch64Opcode::Movz, vec![vr(x), im(41249)]);
        emit(&mut f, e, AArch64Opcode::Movk, vec![vr(x), im(7), im(16)]);
        let use_i = emit(&mut f, e, AArch64Opcode::CmpRR, vec![vr(y), vr(x)]);
        assert_eq!(unique_reaching_const(&f, use_i, x), Some(500_001));
    }

    /// Two defs on merging paths both reach the use -> None.
    #[test]
    fn two_reaching_defs_bail() {
        let mut f = new_func();
        let e = f.entry;
        let (b1, b2, b3) = (f.create_block(), f.create_block(), f.create_block());
        f.block_order = vec![e, b1, b2, b3];
        f.add_edge(e, b1);
        f.add_edge(e, b2);
        f.add_edge(b1, b3);
        f.add_edge(b2, b3);
        let x = v32(0);
        let y = v32(1);
        emit(&mut f, e, AArch64Opcode::CmpRI, vec![vr(y), im(0)]);
        emit(&mut f, e, AArch64Opcode::BCond, vec![im(0), bl(b1)]);
        emit(&mut f, e, AArch64Opcode::B, vec![bl(b2)]);
        emit(&mut f, b1, AArch64Opcode::Movz, vec![vr(x), im(1)]);
        emit(&mut f, b1, AArch64Opcode::B, vec![bl(b3)]);
        emit(&mut f, b2, AArch64Opcode::Movz, vec![vr(x), im(2)]);
        emit(&mut f, b2, AArch64Opcode::B, vec![bl(b3)]);
        let use_i = emit(&mut f, b3, AArch64Opcode::AddRR, vec![vr(y), vr(x), vr(x)]);
        assert_eq!(unique_reaching_const(&f, use_i, x), None);
    }

    /// A redefinition INSIDE a loop body reaches the header around the back
    /// edge alongside the preheader def -> None.
    #[test]
    fn loop_redefinition_bails() {
        let mut f = new_func();
        let e = f.entry;
        let (h, l, x_) = (f.create_block(), f.create_block(), f.create_block());
        f.block_order = vec![e, h, l, x_];
        f.add_edge(e, h);
        f.add_edge(h, l);
        f.add_edge(h, x_);
        f.add_edge(l, h);
        let s = v32(0);
        let y = v32(1);
        emit(&mut f, e, AArch64Opcode::Movz, vec![vr(s), im(1)]);
        emit(&mut f, e, AArch64Opcode::B, vec![bl(h)]);
        // header: use s, then branch
        let use_i = emit(&mut f, h, AArch64Opcode::AddRR, vec![vr(y), vr(y), vr(s)]);
        emit(&mut f, h, AArch64Opcode::CmpRI, vec![vr(y), im(9)]);
        emit(&mut f, h, AArch64Opcode::BCond, vec![im(0), bl(x_)]);
        emit(&mut f, h, AArch64Opcode::B, vec![bl(l)]);
        // latch REDEFINES s (still a Movz #1 — but two defs reach the header).
        emit(&mut f, l, AArch64Opcode::Movz, vec![vr(s), im(1)]);
        emit(&mut f, l, AArch64Opcode::B, vec![bl(h)]);
        emit(&mut f, x_, AArch64Opcode::Ret, vec![]);
        assert_eq!(unique_reaching_const(&f, use_i, s), None);
    }

    /// A def in the same block AFTER the use does not count; the preheader def
    /// still resolves (in-block position precision).
    #[test]
    fn later_def_in_block_ignored() {
        let mut f = new_func();
        let e = f.entry;
        let x = v32(0);
        let y = v32(1);
        emit(&mut f, e, AArch64Opcode::Movz, vec![vr(x), im(5)]);
        let use_i = emit(&mut f, e, AArch64Opcode::AddRR, vec![vr(y), vr(x), vr(x)]);
        emit(&mut f, e, AArch64Opcode::Movz, vec![vr(x), im(99)]);
        assert_eq!(unique_reaching_const(&f, use_i, x), Some(5));
    }

    /// The unique reaching def is NOT a constant materialization -> None.
    #[test]
    fn non_const_reaching_def_bails() {
        let mut f = new_func();
        let e = f.entry;
        let x = v32(0);
        let y = v32(1);
        let z = v32(2);
        emit(&mut f, e, AArch64Opcode::AddRR, vec![vr(x), vr(z), vr(z)]);
        let use_i = emit(&mut f, e, AArch64Opcode::AddRR, vec![vr(y), vr(x), vr(x)]);
        assert_eq!(unique_reaching_const(&f, use_i, x), None);
    }

    /// No def at all (argument-like) -> the Uninit entry marker poisons -> None.
    #[test]
    fn undefined_vreg_bails() {
        let mut f = new_func();
        let e = f.entry;
        let x = v32(0);
        let y = v32(1);
        let use_i = emit(&mut f, e, AArch64Opcode::AddRR, vec![vr(y), vr(x), vr(x)]);
        assert_eq!(unique_reaching_const(&f, use_i, x), None);
    }

    /// A STORE with the queried vreg at operand 0 is a USE, not a def (the
    /// audited role table, not "op0 is def") — it must neither kill the real
    /// def nor register as one.
    #[test]
    fn store_operand_is_not_a_def() {
        let mut f = new_func();
        let e = f.entry;
        let x = v32(0);
        let y = v32(1);
        let p = v64(2);
        emit(&mut f, e, AArch64Opcode::Movz, vec![vr(x), im(1)]);
        emit(&mut f, e, AArch64Opcode::StrRI, vec![vr(x), vr(p), im(0)]);
        let use_i = emit(&mut f, e, AArch64Opcode::AddRR, vec![vr(y), vr(x), vr(x)]);
        assert_eq!(unique_reaching_const(&f, use_i, x), Some(1));
    }

    /// A post-index NEON pair load WRITES BACK its base (operand 2) — that
    /// def-use must kill a prior constant def of the base (the LDP/writeback
    /// P0 class).
    #[test]
    fn writeback_base_is_a_def() {
        let mut f = new_func();
        let e = f.entry;
        let p = v64(0);
        let y = v64(1);
        let (q0, q1) = (
            VReg::new(2, RegClass::Fpr128),
            VReg::new(3, RegClass::Fpr128),
        );
        emit(&mut f, e, AArch64Opcode::Movz, vec![vr(p), im(64)]);
        emit(
            &mut f,
            e,
            AArch64Opcode::NeonLdpQPost,
            vec![vr(q0), vr(q1), vr(p), im(32)],
        );
        let use_i = emit(&mut f, e, AArch64Opcode::AddRR, vec![vr(y), vr(p), vr(p)]);
        // p was advanced by the writeback: the Movz value must NOT be reported.
        assert_eq!(unique_reaching_const(&f, use_i, p), None);
    }

    /// Gpr32 destination truncates: Movk above bit 31 is malformed for a W
    /// register and bails rather than folding a wrong value.
    #[test]
    fn w_form_high_shift_bails() {
        let mut f = new_func();
        let e = f.entry;
        let x = v32(0);
        let y = v32(1);
        emit(&mut f, e, AArch64Opcode::Movz, vec![vr(x), im(1)]);
        emit(&mut f, e, AArch64Opcode::Movk, vec![vr(x), im(1), im(32)]);
        let use_i = emit(&mut f, e, AArch64Opcode::AddRR, vec![vr(y), vr(x), vr(x)]);
        assert_eq!(unique_reaching_const(&f, use_i, x), None);
    }

    /// The all-ids product solution is use-site independent: after one build, a
    /// second use in a different successor block must get the same answer as
    /// the original scan path without rebuilding the solution.
    #[test]
    fn all_ids_context_matches_scan_across_use_blocks() {
        let mut f = new_func();
        let e = f.entry;
        let (left, right) = (f.create_block(), f.create_block());
        f.block_order = vec![e, left, right];
        f.add_edge(e, left);
        f.add_edge(e, right);

        let x = v32(0);
        let y = v32(1);
        emit(&mut f, e, AArch64Opcode::Movz, vec![vr(x), im(41)]);
        let left_use = emit(
            &mut f,
            left,
            AArch64Opcode::AddRR,
            vec![vr(y), vr(x), vr(x)],
        );
        let right_use = emit(
            &mut f,
            right,
            AArch64Opcode::AddRR,
            vec![vr(y), vr(x), vr(x)],
        );

        let ctx = ReachingCtx::new(&f);
        assert!(ctx.all_ids.get().is_none());
        assert_eq!(
            unique_reaching_const_with(&f, &ctx, left_use, x),
            unique_reaching_const(&f, left_use, x)
        );
        let solution = ctx
            .all_ids
            .get()
            .expect("cross-block query builds solution") as *const _;
        assert_eq!(
            unique_reaching_const_with(&f, &ctx, right_use, x),
            unique_reaching_const(&f, right_use, x)
        );
        assert_eq!(
            ctx.all_ids.get().expect("solution remains initialized") as *const _,
            solution
        );
    }

    /// The product solution must preserve ambiguity, not turn a multi-def set
    /// into an arbitrary constant on a later query.
    #[test]
    fn all_ids_context_keeps_loop_redefinition_fail_closed() {
        let mut f = new_func();
        let e = f.entry;
        let (header, latch, exit) = (f.create_block(), f.create_block(), f.create_block());
        f.block_order = vec![e, header, latch, exit];
        f.add_edge(e, header);
        f.add_edge(header, latch);
        f.add_edge(header, exit);
        f.add_edge(latch, header);

        let x = v32(0);
        let y = v32(1);
        emit(&mut f, e, AArch64Opcode::Movz, vec![vr(x), im(1)]);
        let first_use = emit(
            &mut f,
            header,
            AArch64Opcode::AddRR,
            vec![vr(y), vr(y), vr(x)],
        );
        let second_use = emit(
            &mut f,
            header,
            AArch64Opcode::AddRR,
            vec![vr(y), vr(y), vr(x)],
        );
        emit(&mut f, latch, AArch64Opcode::Movz, vec![vr(x), im(1)]);

        let ctx = ReachingCtx::new(&f);
        assert_eq!(unique_reaching_const_with(&f, &ctx, first_use, x), None);
        let solution = ctx
            .all_ids
            .get()
            .expect("cross-block query builds solution") as *const _;
        assert_eq!(unique_reaching_const_with(&f, &ctx, second_use, x), None);
        assert_eq!(
            ctx.all_ids.get().expect("solution remains initialized") as *const _,
            solution
        );
    }

    /// A product solution is shared by context, while each use still needs its
    /// own predecessor-specific projection. Exercise three distinct answers in
    /// sequence so an accidental per-use answer cache cannot pass vacuously.
    #[test]
    fn all_ids_fixpoint_matches_scan_for_distinct_use_blocks() {
        let mut f = new_func();
        let e = f.entry;
        let (left_def, right_def, left_use, right_use, join) = (
            f.create_block(),
            f.create_block(),
            f.create_block(),
            f.create_block(),
            f.create_block(),
        );
        f.block_order = vec![e, left_def, right_def, left_use, right_use, join];
        f.add_edge(e, left_def);
        f.add_edge(e, right_def);
        f.add_edge(left_def, left_use);
        f.add_edge(right_def, right_use);
        f.add_edge(left_use, join);
        f.add_edge(right_use, join);

        let x = v32(0);
        let y = v32(1);
        emit(&mut f, left_def, AArch64Opcode::Movz, vec![vr(x), im(11)]);
        emit(&mut f, right_def, AArch64Opcode::Movz, vec![vr(x), im(29)]);
        let left_i = emit(
            &mut f,
            left_use,
            AArch64Opcode::AddRR,
            vec![vr(y), vr(x), vr(x)],
        );
        let right_i = emit(
            &mut f,
            right_use,
            AArch64Opcode::AddRR,
            vec![vr(y), vr(x), vr(x)],
        );
        let join_i = emit(
            &mut f,
            join,
            AArch64Opcode::AddRR,
            vec![vr(y), vr(x), vr(x)],
        );

        let ctx = ReachingCtx::new(&f);
        for (use_i, expected) in [(left_i, Some(11)), (right_i, Some(29)), (join_i, None)] {
            assert_eq!(unique_reaching_const(&f, use_i, x), expected);
            assert_eq!(unique_reaching_const_with(&f, &ctx, use_i, x), expected);
        }
        assert!(ctx.all_ids.get().is_some());
    }

    /// The transfer function reads `preds`, so its scheduling dependencies
    /// must be the inverse of `preds` too. During CFG rewrites the redundant
    /// `preds`/`succs` views can temporarily disagree. Scheduling from `succs`
    /// used to leave `relay` stale when it ran before `producer`, causing the
    /// use to look uninitialized even though the declared predecessor chain
    /// has one unique definition.
    ///
    /// Exercise both adversarial orders: the result must not depend on which
    /// block happens to be visited first.
    #[test]
    fn fixpoint_scheduling_follows_declared_predecessor_dependencies() {
        let mut f = new_func();
        let entry = f.entry;
        let producer = f.create_block();
        let relay = f.create_block();
        let use_block = f.create_block();
        f.block_order = vec![entry, producer, relay, use_block];

        // Successors make every block executable. Then model the transient
        // one-sided edge producer -> relay only in relay.preds: this is the
        // exact metadata asymmetry whose dependency was previously missed.
        f.add_edge(entry, producer);
        f.add_edge(entry, relay);
        f.add_edge(relay, use_block);
        f.block_mut(relay).preds = vec![producer];

        let x = v32(0);
        let def = emit(&mut f, producer, AArch64Opcode::Movz, vec![vr(x), im(37)]);
        let reachable = reachable_blocks(&f);
        let expected = HashSet::from([DefSite::Inst(def)]);

        for initial in [
            vec![entry, relay, use_block, producer],
            vec![use_block, relay, producer, entry],
        ] {
            let out = compute_out_from_worklist(&f, None, &reachable, x.id, initial);
            assert_eq!(out.get(&relay), Some(&expected));
            assert_eq!(assemble_in(&f, &reachable, &out, use_block), expected);
        }
    }

    /// A successor-only edge is an executable path that predecessor-based
    /// transfer cannot see. Here entry can bypass `producer`, so reporting its
    /// constant at `use_block` would be a miscompile. Both public query paths
    /// must decline before constructing cross-block dataflow.
    #[test]
    fn asymmetric_reachable_cfg_fails_closed_with_context_parity() {
        let mut f = new_func();
        let entry = f.entry;
        let producer = f.create_block();
        let relay = f.create_block();
        let use_block = f.create_block();
        f.block_order = vec![entry, producer, relay, use_block];
        f.add_edge(entry, producer);
        f.add_edge(producer, relay);
        f.add_edge(entry, relay);
        f.add_edge(relay, use_block);

        // Leave entry -> relay in the successor view but remove its mirror.
        // The real successor path entry -> relay -> use_block bypasses the def.
        f.block_mut(relay).preds.retain(|&p| p != entry);

        let x = v32(0);
        let y = v32(1);
        let local = v32(2);
        let local_y = v32(3);
        emit(&mut f, producer, AArch64Opcode::Movz, vec![vr(x), im(37)]);
        emit(&mut f, relay, AArch64Opcode::Movz, vec![vr(local), im(9)]);
        let local_use = emit(
            &mut f,
            relay,
            AArch64Opcode::AddRR,
            vec![vr(local_y), vr(local), vr(local)],
        );
        let use_i = emit(
            &mut f,
            use_block,
            AArch64Opcode::AddRR,
            vec![vr(y), vr(x), vr(x)],
        );

        let ctx = ReachingCtx::new(&f);
        assert!(!ctx.cfg_symmetric);
        assert_eq!(unique_reaching_const(&f, use_i, x), None);
        assert_eq!(unique_reaching_const_with(&f, &ctx, use_i, x), None);
        assert!(ctx.all_ids.get().is_none());
        assert_eq!(unique_reaching_const(&f, local_use, local), Some(9));
        assert_eq!(
            unique_reaching_const_with(&f, &ctx, local_use, local),
            Some(9)
        );
    }
}

/// True when `preds` and `succs` are exact inverses over the executable CFG.
///
/// Edges wholly outside successor-reachability cannot execute and therefore do
/// not invalidate live analysis. Any one-sided edge between reachable blocks
/// does: using only `preds` could miss a succ-only bypass path, while using only
/// `succs` could miss a declared dataflow predecessor.
fn reachable_cfg_is_symmetric(func: &MachFunction, reachable: &HashSet<BlockId>) -> bool {
    let mut from_succs: HashSet<(BlockId, BlockId)> = HashSet::new();
    let mut from_preds: HashSet<(BlockId, BlockId)> = HashSet::new();
    for &b in reachable {
        from_succs.extend(
            func.block(b)
                .succs
                .iter()
                .filter(|s| reachable.contains(s))
                .map(|&s| (b, s)),
        );
        from_preds.extend(
            func.block(b)
                .preds
                .iter()
                .filter(|p| reachable.contains(p))
                .map(|&p| (p, b)),
        );
    }
    from_succs == from_preds
}

/// GEN + the OUT fixpoint for one vreg id, retained as the independent one-shot
/// path against which the all-ids product solution is checked.
fn compute_out(
    func: &MachFunction,
    ctx: Option<&ReachingCtx>,
    reachable: &HashSet<BlockId>,
    id: u32,
) -> HashMap<BlockId, HashSet<DefSite>> {
    // HashSet iteration is deliberately not part of the solver's observable
    // behaviour. A stable seed order makes diagnostics and regressions
    // reproducible; correctness is independent of it (tested above).
    let mut initial_work: Vec<BlockId> = reachable.iter().copied().collect();
    initial_work.sort_unstable();
    compute_out_from_worklist(func, ctx, reachable, id, initial_work)
}

/// Compute one reaching-definitions fixpoint from an explicit seed order.
///
/// The separate entry point makes order independence directly testable. Every
/// reachable block must occur in `initial_work`; duplicates are harmless.
fn compute_out_from_worklist(
    func: &MachFunction,
    ctx: Option<&ReachingCtx>,
    reachable: &HashSet<BlockId>,
    id: u32,
    initial_work: impl IntoIterator<Item = BlockId>,
) -> HashMap<BlockId, HashSet<DefSite>> {
    let mut gens: HashMap<BlockId, InstId> = HashMap::new();
    for &b in reachable {
        let last = match ctx {
            Some(ctx) => ctx
                .def_positions(b, id)
                .and_then(|p| p.last())
                .map(|&pos| func.block(b).insts[pos]),
            None => func
                .block(b)
                .insts
                .iter()
                .rev()
                .copied()
                .find(|&i| defines_id(func, i, id)),
        };
        if let Some(d) = last {
            gens.insert(b, d);
        }
    }

    // OUT[b] is consumed by exactly those blocks that name b in `preds`.
    // Derive that inverse relation from the same metadata the transfer reads.
    // Requeuing `b.succs` instead is unsound when the two redundant CFG views
    // temporarily disagree: a consumer can retain a pre-fixpoint OUT value.
    let mut dependents: HashMap<BlockId, Vec<BlockId>> = HashMap::new();
    for &consumer in reachable {
        for &predecessor in &func.block(consumer).preds {
            if reachable.contains(&predecessor) {
                dependents.entry(predecessor).or_default().push(consumer);
            }
        }
    }
    for consumers in dependents.values_mut() {
        consumers.sort_unstable();
        consumers.dedup();
    }

    let mut out: HashMap<BlockId, HashSet<DefSite>> = HashMap::new();
    // Worklist to a fixpoint. Sets only grow, so termination is guaranteed
    // (each block's OUT is bounded by the def count + 1).
    let mut work: VecDeque<BlockId> = VecDeque::new();
    let mut queued: HashSet<BlockId> = HashSet::new();
    for b in initial_work {
        if reachable.contains(&b) && queued.insert(b) {
            work.push_back(b);
        }
    }
    debug_assert_eq!(queued.len(), reachable.len());

    while let Some(b) = work.pop_front() {
        queued.remove(&b);
        let mut inb: HashSet<DefSite> = HashSet::new();
        if b == func.entry {
            inb.insert(DefSite::Uninit);
        }
        for &p in &func.block(b).preds {
            if !reachable.contains(&p) {
                continue; // edge can never be traversed
            }
            if let Some(po) = out.get(&p) {
                inb.extend(po.iter().copied());
            }
        }
        let outb: HashSet<DefSite> = match gens.get(&b) {
            Some(&d) => HashSet::from([DefSite::Inst(d)]),
            None => inb,
        };
        let changed = match out.get(&b) {
            Some(prev) => *prev != outb,
            None => true,
        };
        if changed {
            out.insert(b, outb);
            if let Some(consumers) = dependents.get(&b) {
                for &consumer in consumers {
                    if queued.insert(consumer) {
                        work.push_back(consumer);
                    }
                }
            }
        }
    }

    out
}

/// `IN[use_block]` assembled from a completed one-id OUT fixpoint.
fn assemble_in(
    func: &MachFunction,
    reachable: &HashSet<BlockId>,
    out: &HashMap<BlockId, HashSet<DefSite>>,
    use_block: BlockId,
) -> HashSet<DefSite> {
    let mut inb: HashSet<DefSite> = HashSet::new();
    if use_block == func.entry {
        inb.insert(DefSite::Uninit);
    }
    for &p in &func.block(use_block).preds {
        if !reachable.contains(&p) {
            continue;
        }
        if let Some(po) = out.get(&p) {
            inb.extend(po.iter().copied());
        }
    }
    inb
}
