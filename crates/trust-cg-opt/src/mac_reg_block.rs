// trust-cg-opt - fail-closed aarch64 scalar matmul 1D register-blocking (T=12 or 8) fast-path
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! # Matmul 1D register-blocking (`mac-reg-block`)
//!
//! Recognizes the classic 3-deep bounds-checked scalar matmul nest
//!
//! ```text
//! for i in 0..N {                              // i-loop
//!   for k in 0..N {                            // k-loop
//!     let aik = a[i*N + k];                    // one read-only a load
//!     for j in 0..N {                          // j-loop (the mac-row-unroll shape)
//!       c[i*N + j] = c[i*N + j] + aik * b[k*N + j];
//!     }
//!   }
//! }
//! ```
//!
//! where `a`, `b`, `c` are three DISTINCT stack-local arrays (`AddPCRel(sp,
//! StackSlot)` bases with pairwise-distinct slot ids), `a`/`b` are read-only in
//! the nest and `c`'s ONLY store is `c[i*N+j]`, `N` is a compile-time constant
//! that is an exact multiple of the tile `T` (12, else 8: see [`tile_for`]),
//! and the common array length `L`
//! (from the surviving `idx <u L` bounds checks) satisfies `L >= N*N` so every
//! tiled index is provably in-bounds WITHOUT a per-access check.
//!
//! ## What it does (register-blocking with loop interchange; store-sinking)
//!
//! It splices, in FRONT of the untouched checked nest (kept as the fallback,
//! reached on a runtime guard, so `mac-row-unroll` still fires on it), a
//! CHECK-FREE register-blocked fast path that interchanges the `k` and `j`
//! loops and keeps a tile of `T` `c` accumulators in registers across the
//! whole `k`-loop:
//!
//! ```text
//! for i in 0..N {
//!   for jt in (0..N step T) {                  // exact tiles, T = 12 or 8
//!     let mut acc[0..T] = c[i*N + jt .. i*N + jt + T];   // T loads
//!     for k in 0..N {
//!       let aik = a[i*N + k];
//!       for m in 0..T { acc[m] += aik * b[k*N + jt + m]; }
//!     }
//!     c[i*N + jt .. i*N + jt + T] = acc[0..T];           // T stores, after k
//!   }
//! }
//! ```
//!
//! Per `(i, jt, k)` the fast path does `1` `a` load, `T` `b` loads and `T`
//! `madd`s and NO `c` traffic; `c` is loaded once per tile and stored once per
//! tile (after the whole `k`-loop). The tile/row pointers advance by immediate
//! `AddRI` (`+= T*scale` per tile, `+= N*scale` per `i`) and address `c` with
//! immediate-offset `LdrRI`/`StrRI [p, #m*scale]`.
//!
//! ## The k-loop body: pointer-writeback shape
//!
//! Inside the `k`-loop the two per-`k` pointer bumps are folded INTO the loads
//! that are their last readers (see `pair_writeback_ok` for the encodability
//! preconditions; anything that fails them falls back to the plain
//! `LdrRI` + two `AddRI` shape, which is what this pass emitted originally):
//!
//! ```text
//!   ldr  aik, [pa], #scale              // a load + `pa += scale`
//!   ldp  b6,b7, [pb, #(T-2)*scale]      // b lanes, DESCENDING
//!   madd ... ; madd ...
//!   ...
//!   ldp  b0,b1, [pb], #N*scale          // last b pair + `pb += N*scale`
//!   madd ... ; madd ...
//! ```
//!
//! This is a pure addressing-mode rewrite: identical loads of identical
//! addresses, identical `madd`s, and each pointer still advances exactly once
//! per `k` by exactly the same amount — only the instruction that performs the
//! advance changes. It costs `2*T + 4` instructions per `k` instead of
//! `2*T + 6`, i.e. `1 + 1/T` loop-overhead instructions per multiply-accumulate
//! instead of `1 + 3/T` (measured on `p4_matmul`, `T = 8`, Cortex-X925: 42.1ms
//! -> 39.4ms, 1.112x -> 1.041x of LLVM `-O3`).
//!
//! The DESCENDING lane order is load-bearing, not cosmetic: it puts the
//! writeback on the LAST `ldp`, so the other `T/2 - 1` pairs read the
//! pre-update `pb` and stay off the base-update recurrence. The ascending
//! order (writeback first, remaining pairs at negative offsets off the new
//! base) encodes equally well and computes the same values, but chains every
//! subsequent load behind the base write and measured ~2.5% slower.
//!
//! ## Why the rewrite preserves the nest (informal argument)
//!
//! This is the argument the recognizer's guards discharge by construction; it
//! is not a machine-checked proof. The executed evidence is the native
//! on/off/C-reference differential
//! `trust-cg-codegen/tests/e2e_aarch64_mac_reg_block_differential.rs`.
//!
//! 1. **Same values, k-order preserved.** For each fixed `(i, j=jt+m)` the fast
//!    path computes `acc = c[i*N+j] + sum_{k=0}^{N-1} a[i*N+k]*b[k*N+j]`,
//!    accumulating over `k=0,1,...,N-1` in exactly the original order, with the
//!    identical wrapping `madd`. `c` is loaded once (its zeroed/initial value)
//!    and stored once with the final sum — bit-identical to the original RMW
//!    chain because integer `+` is associative and the per-`k` order is kept.
//! 2. **Store-sinking is legal (distinct locals).** `a`, `b`, `c` are three
//!    distinct stack slots (verified from their `AddPCRel` bases), `a`/`b` are
//!    never stored in the nest, and `c`'s only store is `c[i*N+j]`. Deferring
//!    the `c[i*N+jt+m]` stores across the `k`-loop therefore changes no `a`/`b`
//!    load (they never read `c`) and no other `c` cell (distinct `(i,j)` are
//!    distinct addresses); nothing outside the nest observes `c` until the nest
//!    completes. The interchange is thus observationally identical.
//! 3. **No OOB (check-free).** With `i,k in 0..N`, `jt in {0,T,..,N-T}`,
//!    `m in 0..T` and `L >= N*N`, every index `i*N+k`, `k*N+jt+m`, `i*N+jt+m`
//!    is `<= (N-1)*N + (N-1) = N*N-1 < L`. All three facts are compile-time
//!    constants at recognition, so the fast path needs no per-access bounds
//!    check; the loop-bound guards `i<N`, `jt<N`, `k<N` are the ordinary loop
//!    structure. EVERY bounds check in the nest, the k-loop's `a[i*N+k]`
//!    check included, must compare a recognized index against a length
//!    `>= N*N`, and each backing stack slot must hold `N*N` 8-byte elements
//!    (`review_bar`). Each recognized index is defined in a non-header block
//!    of its own loop, before the check on every path and in the same loop,
//!    so the compared value is `x*N + y` of the current iteration's counters
//!    (both `< N`, since the header test passed): no check the fast path
//!    skips can fail, and no unchecked access leaves its slot.
//! 4. **Additive + guarded fallback.** The checked nest is left byte-for-byte
//!    intact; only new blocks are spliced before it and the i-loop preheader
//!    terminator is redirected (at a final COMMIT) to a guard that dispatches to
//!    the fast path (guard true for the recognized constant `N`) or the
//!    untouched fallback nest. Recognition is closed-world and fail-closed on
//!    every unproven precondition. The emitted opcode set is `Madd`, `AddRI`,
//!    `MovR`, `Movz`, `CmpRI`, `BCond`, `B`, `LdrRI`/`StrRI` with `#m*scale` —
//!    all already emitted by the scalar nest — plus, in the k-loop's
//!    pointer-writeback shape, `LdrPostIndex`, `LdpRI` and `LdpPostIndex`. Those
//!    three are pre-existing backend opcodes with encoder support and correct
//!    def/def-use operand roles (`effects::fill_operand_roles`); `LdpRI` is in
//!    any case what `mem-pair-formation` already folded this loop's `LdrRI`
//!    pairs into. No division, no new emittable opcode in the backend.
//! 5. **Nothing else observable (publication review bar, `review_bar`).**
//!    Every transferred and multiplied value is a 64-bit GPR (data width, not
//!    just stride). Every conditional branch in the nest is a counted-loop
//!    header test or one of the passing bounds checks above, and each header
//!    leaves exactly to its parent loop, so the scalar nest has no early exit
//!    or conditional store the fast path would skip (mandatory control flow).
//!    A header runs once more than its body, with the counter at `N`, so it
//!    may hold only copies, the counter compare and its branches; every
//!    recognized index, address, load, multiply-add and the store sits in a
//!    non-header block of its own loop, so each runs exactly once per
//!    iteration the fast path replays. Every single-definition value the
//!    nest reads is defined on every path before the read. Each loop counter
//!    is reset to 0 once per parent iteration, and is read only inside its
//!    own loop and never after its latch step. No vreg the nest writes is
//!    live into the nest exit, so skipping the scalar nest bypasses no
//!    live-out; NZCV at the exit is `cmp N, N` on both paths. The nest
//!    touches no physical register, stack-slot or special operand.
//!
//! Default-ON at O2/O3 (never O0/O1). Compile-time kill switch:
//! `TCG_NO_MAC_REG_BLOCK`. Per-pass bisect:
//! `TRUST_CG_DISABLE_PASSES=mac_reg_block`.

use crate::fast_hash::{FxHashMap as HashMap, FxHashSet as HashSet};
use crate::loop_contract::LoopLocality;
use crate::mach_util::{branch_targets, copied_const, copy_like, strip_copies};

use trust_cg_ir::{
    AArch64Opcode, BlockId, InstId, MachFunction, MachInst, MachOperand, RegClass, StackSlotId,
    VReg,
};

use crate::dom::DomTree;
use crate::loops::LoopAnalysis;
use crate::pass_manager::{AnalysisCache, MachinePass};

mod review_bar;
#[cfg(test)]
mod tests;

use review_bar::NestReject;

/// AArch64 condition code for unsigned lower (`LO`) — the native forward
/// `iv < N` continue test (accepted alongside `LT`).
const CC_LO: i64 = 3;
/// AArch64 condition code for signed less-than (`LT`).
const CC_LT: i64 = 11;
/// AArch64 condition code for unsigned higher-or-same (`HS`/`CS`) — the fast
/// path's loop-exit guards bail on `idx >= bound`.
const CC_HS: i64 = 2;
/// AArch64 condition code for not-equal (`NE`) — the fallback dispatch guard.
const CC_NE: i64 = 1;

/// Register-block tile widths, widest first: the number of `c` accumulators
/// held in registers across the `k`-loop.
///
/// Twelve lanes keep 18 values live in the k-loop (12 accumulators, `aik`,
/// two `b` lanes, the `a` and `b` pointers and `k`), inside the allocator's
/// 25 allocatable GPRs with room for the outer loop's values. In the
/// writeback shape the k-loop is `T/2` pair loads, `T` multiply-adds, the
/// `a` load and three loop instructions: 22 per 12 multiply-adds against 16
/// per 8. On p4_matmul (N = 24, Apple M4 Max, min of 7 runs) that is 566M
/// instead of 610M instructions retired and 116.3M instead of 119.8M cycles
/// (LLVM -O3: 524.6M, 115.7M). A 16-accumulator tile pair measured slower
/// on p4_matmul: it pushed the outer induction values into frame spills
/// (docs/archive/compile-time-attribution-2026-07-25.md, 2026-08-13).
const TILES: [i64; 2] = [12, 8];

/// The narrowest tile: every admitted `N` is at least this.
const MIN_TILE: i64 = 8;

/// The tile width for `N`: the widest of [`TILES`] that divides `N` exactly
/// (the fast path has no remainder tile), or `None`.
fn tile_for(n: i64) -> Option<i64> {
    TILES.into_iter().find(|&tile| n >= tile && n % tile == 0)
}

/// Compile-time kill switch: set `TCG_NO_MAC_REG_BLOCK` (any value) to disable
/// the pass (run() is a no-op). Default ON at O2/O3.
fn mrb_enabled() -> bool {
    crate::env_lock::var_os("TCG_NO_MAC_REG_BLOCK").is_none()
}

/// Cached `TRUST_CG_DUMP_MRB` dump gate — a pure diagnostic that selects only
/// whether `eprintln!`s fire, read from inside per-block/per-loop walks.
fn dumping() -> bool {
    use std::sync::OnceLock;
    static ENABLED: OnceLock<bool> = OnceLock::new();
    *ENABLED.get_or_init(|| std::env::var("TRUST_CG_DUMP_MRB").is_ok())
}

/// Whether any live block contains the opcode every recognized MAC nest needs.
///
/// This is an exact no-fire prefilter: every accepted shape traces its address
/// calculations and accumulated value through `Madd`, so without one the pass
/// cannot change the function.  Looking only at `block_order` matches the
/// recognizer's live-CFG scope; a dead-but-listed `Madd` may conservatively miss
/// the shortcut, but can never cause a false decline.
fn has_live_madd(func: &MachFunction) -> bool {
    func.block_order
        .iter()
        .flat_map(|&block| func.block(block).insts.iter())
        .any(|&inst| func.inst(inst).opcode == AArch64Opcode::Madd)
}

// ---------------------------------------------------------------------------
// Pass
// ---------------------------------------------------------------------------

/// The `mac-reg-block` machine pass.
#[derive(Default)]
pub struct MacRegBlock {
    fired: usize,
}

impl MacRegBlock {
    pub fn new() -> Self {
        Self { fired: 0 }
    }
    /// Nests register-blocked in the last `run`.
    pub fn fired(&self) -> usize {
        self.fired
    }
}

impl MachinePass for MacRegBlock {
    fn name(&self) -> &str {
        "mac-reg-block"
    }

    fn run(&mut self, func: &mut MachFunction) -> bool {
        if !mrb_enabled() {
            return false;
        }
        if !has_live_madd(func) {
            self.fired = 0;
            return false;
        }
        let dom = DomTree::compute(func);
        let loops = LoopAnalysis::compute(func, &dom);
        self.run_core(func, &dom, &loops)
    }

    fn run_with_analyses(&mut self, func: &mut MachFunction, analyses: &mut AnalysisCache) -> bool {
        if !mrb_enabled() {
            return false;
        }
        if !has_live_madd(func) {
            self.fired = 0;
            return false;
        }
        let loops = analyses.loop_analysis(func).clone();
        let changed = {
            let dom = analyses.domtree(func);
            self.run_core(func, dom, &loops)
        };
        if changed {
            analyses.invalidate();
        }
        changed
    }
}

impl MacRegBlock {
    fn run_core(&mut self, func: &mut MachFunction, dom: &DomTree, loops: &LoopAnalysis) -> bool {
        self.fired = 0;
        // Recognize first (read-only); at most one nest is transformed per run
        // (applying only ADDS blocks; ids are never renumbered). We take the
        // first recognized nest deterministically (BTreeMap header order).
        let mut plan = None;
        // One whole-arena def map for the sweep; the scan is read-only (it
        // breaks on the first recognition, and the plan is applied after).
        let def_map = crate::effects::build_reaching_def_map(func);
        for lp in loops.all_loops() {
            // Only consider a loop that is the innermost (j) loop.
            let is_innermost = loops
                .all_loops()
                .all(|other| other.header == lp.header || !lp.body.contains(&other.header));
            if !is_innermost {
                continue;
            }
            if let Ok(rec) = Recognized::recognize(func, dom, &def_map, loops, lp.header) {
                plan = Some(rec);
                break;
            }
        }
        let Some(rec) = plan else {
            return false;
        };
        if apply(func, &rec) {
            self.fired += 1;
            if dumping() {
                eprintln!(
                    "[mac-reg-block] fn={} register-blocked (T={})",
                    func.name, rec.tile
                );
            }
            true
        } else {
            false
        }
    }
}

// ---------------------------------------------------------------------------
// Recognition
// ---------------------------------------------------------------------------

struct Recognized {
    /// The i-loop preheader (redirect site) and its terminator.
    preheader: BlockId,
    preheader_term: InstId,
    /// The i-loop header (fallback entry).
    i_header: BlockId,
    /// The block control leaves the i-loop to (the non-body successor).
    exit_target: BlockId,
    /// Compile-time bound `N` (`>= tile`, `N % tile == 0`, `<= u32::MAX`).
    n_const: i64,
    /// Tile width (accumulators per tile), from [`tile_for`].
    tile: i64,
    /// The loop-invariant register holding `N` (reused as a `madd` multiplier
    /// and the guard bound).
    n_reg: VReg,
    /// Element scale (`8` for i64), `> 0`.
    scale_const: i64,
    /// `a`/`b`/`c` base pointers (distinct stack-slot `AddPCRel` bases).
    a_base: VReg,
    b_base: VReg,
    c_base: VReg,
    /// The loop-state contract (`crate::loop_contract`) passed for
    /// no register but proven pass-through carriers, handing off only at the nest exit. The plan
    /// cannot be built without it.
    _locality: LoopLocality,
}

impl Recognized {
    /// Recognize the nest whose innermost (`j`) loop is headed by `j_header`.
    ///
    /// Every structural mismatch is [`NestReject::Shape`]; each publication
    /// review-bar condition (data width, array bounds, mandatory control
    /// flow, bypassed live-outs) and each closed-world/aliasing condition has
    /// its own named [`NestReject`] so the unit tests pin WHICH guard refused.
    /// Where an earlier guard refuses every input a later one would (the
    /// bounds-check premise behind [`NestReject::HeaderWork`]), the unit tests
    /// also call the later check directly.
    #[allow(clippy::too_many_lines)]
    fn recognize(
        func: &MachFunction,
        dom: &DomTree,
        def: &HashMap<u32, InstId>,
        loops: &LoopAnalysis,
        j_header: BlockId,
    ) -> Result<Self, NestReject> {
        let dump = dumping();
        macro_rules! bail {
            ($($t:tt)*) => {{
                if dump {
                    eprintln!("[mac-reg-block] bail@{}: {}", func.name, format!($($t)*));
                }
                return Err(NestReject::Shape);
            }};
        }
        macro_rules! reject {
            ($reason:expr) => {{
                let reason: NestReject = $reason;
                if dump {
                    eprintln!("[mac-reg-block] reject@{}: {}", func.name, reason);
                }
                return Err(reason);
            }};
        }

        let Some(j_loop) = loops.get_loop(j_header) else {
            bail!("no loop headed by {:?}", j_header);
        };
        let j_body = &j_loop.body;
        let Some(j_latch) = single_latch(func, j_header, j_body) else {
            bail!("j-loop has no single latch");
        };
        let Some(j_pre) = j_loop.preheader else {
            bail!("j-loop has no unique preheader");
        };
        // `def` is supplied by the caller, built ONCE per recognition sweep.
        // It was rebuilt inside every per-loop attempt — the same defect
        // measured at ~99% of eight sibling passes this session.

        // ---- (1) inner MAC recognition (the `c[i*N+j] += aik*b[k*N+j]` shape).
        let Some(inner) = recognize_inner_mac(func, dom, j_header, j_latch, j_body, j_pre, def)
        else {
            bail!("inner MAC j-loop not recognized");
        };

        // ---- (1b) the j-loop itself must be a clean `0..N` unit-stride counted
        // loop over the recognized j iv (my fast path replays j = 0..N-1).
        let Some(j_counter) =
            verify_counted_0_n(func, def, j_body, j_header, inner.iv, inner.n_const, dump)
        else {
            bail!("j-loop is not a clean 0..N counted loop");
        };

        // ---- (2) k-loop = parent of the j-loop. Verify k is a clean `0..N`
        // counted loop over the recognized k, the read-only `a[i*N+k]` load, and
        // that the j-loop is its ONLY child loop.
        let Some(k_header) = j_loop.parent else {
            bail!("j-loop has no parent (k) loop");
        };
        let Some(k_loop) = loops.get_loop(k_header) else {
            bail!("no loop headed by {:?}", k_header);
        };
        if only_child(loops, k_header, j_header).is_none() {
            bail!("k-loop does not have the j-loop as its unique child");
        }
        let Some(k_counter) = verify_counted_0_n(
            func,
            def,
            &k_loop.body,
            k_header,
            inner.k_reg,
            inner.n_const,
            dump,
        ) else {
            bail!("k-loop is not a clean 0..N counted loop over k");
        };
        // The read-only `a` load: `aik = LdrRI[Madd(Madd(i,N,k), scale, a_base), #0]`.
        let Some(a_load) = recognize_a_load(func, def, &k_loop.body, &inner) else {
            bail!("read-only a[i*N+k] load not recognized");
        };
        let a_base = a_load.base;

        // ---- (3) i-loop = parent of the k-loop. Verify i is a clean `0..N`
        // counted loop over the recognized i and that the k-loop is its ONLY
        // child loop.
        let Some(i_header) = k_loop.parent else {
            bail!("k-loop has no parent (i) loop");
        };
        let Some(i_loop) = loops.get_loop(i_header) else {
            bail!("no loop headed by {:?}", i_header);
        };
        if only_child(loops, i_header, k_header).is_none() {
            bail!("i-loop does not have the k-loop as its unique child");
        }
        let Some(i_counter) = verify_counted_0_n(
            func,
            def,
            &i_loop.body,
            i_header,
            inner.i_reg,
            inner.n_const,
            dump,
        ) else {
            bail!("i-loop is not a clean 0..N counted loop over i");
        };
        let Some(preheader) = i_loop.preheader else {
            bail!("i-loop has no unique preheader");
        };
        let Some(&preheader_term) = func
            .block(preheader)
            .insts
            .iter()
            .rev()
            .find(|&&id| branch_targets(func.inst(id)).contains(&i_header))
        else {
            bail!("no preheader->i-header branch");
        };
        // IDEMPOTENCE: `apply` keeps the whole scalar nest as the FALLBACK of
        // the register-blocked nest it builds, behind a guard block that is
        // exactly `CmpRI n_reg, #N ; BCond NE -> i_header ; B entry`, and that
        // guard becomes the scalar nest's new preheader. Without this bail the
        // scalar nest was recognized again on the next fixpoint iteration and
        // every iteration nested one more blocked copy (masked on the corpus
        // only because mac-row-unroll had already unrolled the remainder j-loop
        // to four stores, which the row recognizer refuses).
        if preheader_is_reg_block_guard(func, preheader, i_header, inner.n_reg, inner.n_const) {
            bail!("scalar fallback nest of an already register-blocked nest");
        }
        // The unique non-body successor of the i-header is the nest exit.
        let exits: Vec<BlockId> = func
            .block(i_header)
            .succs
            .iter()
            .copied()
            .filter(|s| !i_loop.body.contains(s))
            .collect();
        if exits.len() != 1 {
            bail!("i-header has {} non-body successors (want 1)", exits.len());
        }
        let exit_target = exits[0];

        // ---- (4) distinct-locals + read-only a/b + single c-store + closed
        // world, all over the WHOLE i-loop body.
        let (Some(ss_a), Some(ss_b), Some(ss_c)) = (
            base_stack_slot(func, def, a_base),
            base_stack_slot(func, def, inner.b_base),
            base_stack_slot(func, def, inner.c_base),
        ) else {
            reject!(NestReject::ArrayBaseNotStackSlot);
        };
        if ss_a == ss_b || ss_a == ss_c || ss_b == ss_c {
            if dump {
                eprintln!(
                    "[mac-reg-block] a/b/c slots ({:?} {:?} {:?}) are not distinct",
                    ss_a, ss_b, ss_c
                );
            }
            reject!(NestReject::AliasedArrays);
        }
        if !verify_closed_world(
            func,
            def,
            &i_loop.body,
            a_base,
            inner.b_base,
            inner.c_base,
            dump,
        ) {
            reject!(NestReject::OpenWorld);
        }

        // ---- (5) tile / bound arithmetic (all compile-time constants).
        let n = inner.n_const;
        let scale = inner.scale_const;
        let Some(tile) = tile_for(n) else {
            reject!(NestReject::NotTileMultiple);
        };
        // L >= N*N  (so every tiled index <= N*N-1 < L is in-bounds).
        let Some(nn) = n.checked_mul(n) else {
            bail!("N*N overflows");
        };
        if inner.l_const < nn {
            if dump {
                eprintln!(
                    "[mac-reg-block] array length {} < N*N {} (cannot prove in-bounds)",
                    inner.l_const, nn
                );
            }
            reject!(NestReject::BoundsCheckMayFail);
        }
        // Encodable immediates: per-k b advance `N*scale`, per-lane offset
        // `(tile-1)*scale`, per-tile/per-row advance `tile*scale`/`N*scale`.
        // WRONG-CODE GUARD (2026-08-17): `apply` emits the whole kernel with
        // `RegClass::Gpr64` lanes and 64-bit `LdrRI`/`LdpRI` loads, so it is
        // correct ONLY for an 8-byte element. Recognition previously admitted
        // any positive scale, so an i32 matmul (scale == 4) was rewritten into
        // 64-bit loads at 4-byte lane strides: every lane pulled TWO adjacent
        // i32s packed into one X register and fed them to a 64-bit `madd`, and
        // the top lane read 4 bytes PAST the array. That miscompiled silently
        // and NON-DETERMINISTICALLY (repeated runs of one binary disagreed,
        // because the out-of-bounds read picks up whatever is adjacent);
        // measured against LLVM at O2/O3 on square i32 N in {8,24,64}.
        //
        // Fail closed on every element width this kernel does not model. Any
        // future non-8 support must widen `apply` (lane class, load opcode and
        // element packing) FIRST — this gate is what makes that a deliberate
        // change rather than a silent one. The STRIDE is only half of the
        // width contract: `review_bar::check_data_width` pins the transferred
        // and multiplied VALUES to 64-bit lanes too.
        if !kernel_supports_scale(scale) {
            reject!(NestReject::ElementScale);
        }
        let (Some(n_scale), Some(lane_span)) =
            (n.checked_mul(scale), (tile - 1).checked_mul(scale))
        else {
            bail!("scale {} / N {} immediates overflow", scale, n);
        };
        if n_scale > 4095 || lane_span > 4095 {
            bail!(
                "scale {} / N {} out of AddRI/ldst-immediate range",
                scale,
                n
            );
        }

        // ---- (6) the reused invariants must dominate the i-loop preheader.
        let i_loop_insts = collect_insts(func, &i_loop.body);
        for (name, v) in [
            ("N", inner.n_reg),
            ("scale", inner.scale_reg),
            ("a_base", a_base),
            ("b_base", inner.b_base),
            ("c_base", inner.c_base),
        ] {
            if v.class != RegClass::Gpr64 {
                bail!("{} not Gpr64", name);
            }
            if !is_loop_invariant(func, def, dom, &i_loop_insts, preheader, v) {
                bail!("{} not invariant across the i-loop", name);
            }
        }

        // ---- (7) the publication review bar (L10-P4): data width, all array
        // bounds, mandatory control flow and bypassed loop live-outs, each a
        // named fail-closed refusal. See `review_bar`.
        let facts = review_bar::NestFacts {
            i_body: &i_loop.body,
            k_body: &k_loop.body,
            j_body,
            headers: [i_header, k_header, j_header],
            counters: [i_counter, k_counter, j_counter],
            exit_target,
            indices: [a_load.index, inner.cidx, inner.bidx, inner.cidx2],
            lane_values: [
                a_load.value,
                inner.aik,
                inner.bval,
                inner.cval,
                inner.store_val,
            ],
            k_level_values: [a_load.index, a_load.addr, a_load.value],
            j_level_values: [
                inner.cidx,
                inner.caddr,
                inner.cval,
                inner.bidx,
                inner.baddr,
                inner.bval,
                inner.cidx2,
                inner.store_addr,
                inner.store_val,
            ],
            store: inner.store,
            slots: [ss_a, ss_b, ss_c],
            scale_reg: inner.scale_reg,
            n,
            scale,
        };
        let locality = match review_bar::check(func, dom, def, &facts) {
            Ok(locality) => locality,
            Err(reason) => reject!(reason),
        };

        if dump {
            eprintln!(
                "[mac-reg-block] RECOGNIZED@{} i_hdr={:?} N={} L={} scale={} a={:?} b={:?} c={:?} \
                 slots=({},{},{}) exit={:?}",
                func.name,
                i_header,
                n,
                inner.l_const,
                scale,
                a_base,
                inner.b_base,
                inner.c_base,
                ss_a.0,
                ss_b.0,
                ss_c.0,
                exit_target
            );
        }
        Ok(Recognized {
            _locality: locality,
            preheader,
            preheader_term,
            i_header,
            exit_target,
            n_const: n,
            tile,
            n_reg: inner.n_reg,
            scale_const: scale,
            a_base,
            b_base: inner.b_base,
            c_base: inner.c_base,
        })
    }
}

/// The inner `c[i*N+j] += aik*b[k*N+j]` MAC recognition (mirrors mac-row-unroll,
/// but tolerant of the address form being either `LdrRI [Madd(idx,scale,base)]`
/// or already-elided; here we require the pristine `LdrRI`/`StrRI` + `Madd`
/// address form, which is exactly what the pipeline hands this slot).
struct InnerMac {
    iv: VReg,
    n_reg: VReg,
    n_const: i64,
    l_const: i64,
    i_reg: VReg,
    k_reg: VReg,
    c_base: VReg,
    b_base: VReg,
    scale_reg: VReg,
    scale_const: i64,
    aik: VReg,
    /// `c` load index `Madd(i, N, j)`, address and loaded value.
    cidx: VReg,
    caddr: VReg,
    cval: VReg,
    /// `b` load index `Madd(k, N, j)`, address and loaded value.
    bidx: VReg,
    baddr: VReg,
    bval: VReg,
    /// `c` store index `Madd(i, N, j)`, address and stored value.
    cidx2: VReg,
    store_addr: VReg,
    store_val: VReg,
    /// The single `c` store.
    store: InstId,
}

/// The recognized read-only `aik = a[i*N+k]` load in the k-loop.
struct ALoad {
    /// `a` base register (a stack-slot address).
    base: VReg,
    /// Index `Madd(i, N, k)`.
    index: VReg,
    /// Address `Madd(index, scale, base)`.
    addr: VReg,
    /// The loaded value (the `LdrRI` destination).
    value: VReg,
}

#[allow(clippy::too_many_lines)]
fn recognize_inner_mac(
    func: &MachFunction,
    dom: &DomTree,
    header: BlockId,
    latch: BlockId,
    body: &HashSet<BlockId>,
    preheader: BlockId,
    def: &HashMap<u32, InstId>,
) -> Option<InnerMac> {
    if header == latch || body.len() < 2 {
        return None;
    }
    // Closed-world whitelist + exactly one StrRI, two LdrRI in the j-loop.
    let mut loop_insts = HashSet::default();
    let mut stores: Vec<InstId> = Vec::new();
    let mut loads = 0usize;
    for &b in body {
        for &id in &func.block(b).insts {
            let op = func.inst(id).opcode;
            if !allowed_inner_op(op) {
                return None;
            }
            match op {
                AArch64Opcode::StrRI => stores.push(id),
                AArch64Opcode::LdrRI => loads += 1,
                _ => {}
            }
            loop_insts.insert(id);
        }
    }
    if stores.len() != 1 || loads != 2 {
        return None;
    }
    let store_id = stores[0];

    // header preds == {preheader, latch}
    let hpreds = &func.block(header).preds;
    if hpreds.len() != 2 || !hpreds.contains(&latch) || !hpreds.contains(&preheader) {
        return None;
    }

    let iv = find_unit_induction(func, def, latch)?;
    if iv.class != RegClass::Gpr64 {
        return None;
    }

    // Work backward from the single store: StrRI [val, addr, #0].
    let store = func.inst(store_id);
    if store.operands.len() != 3 || store.operands[2].as_imm() != Some(0) {
        return None;
    }
    let store_val = store.operands[0].as_vreg()?;
    let store_addr = store.operands[1].as_vreg()?;
    let (cidx2, scale_r_s, cbase_s) = madd_addr(func, def, store_addr)?;
    let (i_r2, n_r2, jc_a) = madd_index(func, def, cidx2)?;
    if !same_as(func, def, jc_a, iv) {
        return None;
    }

    // store value: mac = Madd(aik, bval, cval).
    let mac = func.inst(*def.get(&store_val.id)?);
    let (aik, bval, cval) = madd_parts_val(mac)?;

    // bval = LdrRI [_, baddr, #0]; baddr = Madd(bidx, scale, b_base);
    // bidx = Madd(k, N, j).
    let baddr = ldr_addr(func, def, bval)?;
    let (bidx, scale_r_b, bbase) = madd_addr(func, def, baddr)?;
    let (k_reg, n_r_b, jc_b) = madd_index(func, def, bidx)?;
    if !same_as(func, def, jc_b, iv) {
        return None;
    }

    // cval = LdrRI [_, caddr, #0]; caddr = Madd(cidx, scale, c_base);
    // cidx = Madd(i, N, j).
    let caddr = ldr_addr(func, def, cval)?;
    let (cidx, scale_r_c, cbase_c) = madd_addr(func, def, caddr)?;
    let (i_reg, n_r_c, jc_c) = madd_index(func, def, cidx)?;
    if !same_as(func, def, jc_c, iv) {
        return None;
    }

    // Cross-consistency.
    if !same_as(func, def, i_r2, i_reg) || cbase_s != cbase_c {
        return None;
    }
    if scale_r_s != scale_r_c || scale_r_b != scale_r_c {
        return None;
    }
    let scale_reg = scale_r_c;
    let scale_const = copied_const(func, def, scale_reg)?;
    if n_r2 != n_r_c || n_r_b != n_r_c {
        return None;
    }
    let n_reg = n_r_c;
    let n_const = copied_const(func, def, n_reg)?;
    if !(MIN_TILE..=i64::from(u32::MAX)).contains(&n_const) {
        return None;
    }
    // header uses the same native forward `iv < N` test with the same constant.
    let hdr_n = recognize_native_const_bound(func, def, body, header, iv)?;
    if hdr_n != n_const {
        return None;
    }
    // the three bounds checks against ONE array length L.
    let l1 = find_bounds_check(func, def, body, cidx)?;
    let l2 = find_bounds_check(func, def, body, bidx)?;
    let l3 = find_bounds_check(func, def, body, cidx2)?;
    if l1 != l2 || l2 != l3 {
        return None;
    }
    let l_const = l1;

    // aik / i / k / bases must be loop-invariant in the j-loop.
    let _ = dom;
    Some(InnerMac {
        iv,
        n_reg,
        n_const,
        l_const,
        i_reg,
        k_reg,
        c_base: cbase_c,
        b_base: bbase,
        scale_reg,
        scale_const,
        aik,
        cidx,
        caddr,
        cval,
        bidx,
        baddr,
        bval,
        cidx2,
        store_addr,
        store_val,
        store: store_id,
    })
}

/// Recognize the k-loop's read-only `aik = a[i*N+k]` load:
/// `LdrRI [aik, Madd(Madd(i,N,k), scale, a_base), #0]`, with the loaded reg
/// being exactly the `aik` the inner mac multiplies.
fn recognize_a_load(
    func: &MachFunction,
    def: &HashMap<u32, InstId>,
    k_body: &HashSet<BlockId>,
    inner: &InnerMac,
) -> Option<ALoad> {
    let value = strip_copies(func, def, inner.aik);
    let aik_def = *def.get(&value.id)?;
    // aik must be produced by a LdrRI whose def-block is in the k-loop body.
    let ai = func.inst(aik_def);
    if ai.opcode != AArch64Opcode::LdrRI
        || ai.operands.len() != 3
        || ai.operands[2].as_imm() != Some(0)
    {
        return None;
    }
    let blk = block_of_inst(func, aik_def)?;
    if !k_body.contains(&blk) {
        return None;
    }
    let addr = ai.operands[1].as_vreg()?;
    let (aidx, scale_r, a_base) = madd_addr(func, def, addr)?;
    if scale_r != inner.scale_reg {
        return None;
    }
    // aidx = Madd(i, N, k)
    let (i_r, n_r, k_r) = madd_index(func, def, aidx)?;
    if n_r != inner.n_reg
        || !same_as(func, def, i_r, inner.i_reg)
        || !same_as(func, def, k_r, inner.k_reg)
    {
        return None;
    }
    Some(ALoad {
        base: a_base,
        index: aidx,
        addr,
        value,
    })
}

/// Fail-closed closed-world check over the WHOLE i-loop body: only whitelisted
/// opcodes; the ONLY store is a single `StrRI` whose base traces to `c_base`;
/// no store addresses `a_base` or `b_base`.
fn verify_closed_world(
    func: &MachFunction,
    def: &HashMap<u32, InstId>,
    i_body: &HashSet<BlockId>,
    a_base: VReg,
    b_base: VReg,
    c_base: VReg,
    dump: bool,
) -> bool {
    macro_rules! bail {
        ($($t:tt)*) => {{ if dump { eprintln!("[mac-reg-block] bail@closed-world: {}", format!($($t)*)); } return false; }};
    }
    let mut stores = 0usize;
    let mut loads = 0usize;
    for &b in i_body {
        for &id in &func.block(b).insts {
            let inst = func.inst(id);
            if !allowed_nest_op(inst.opcode) {
                bail!("disallowed nest op {:?}", inst.opcode);
            }
            // The fast path defines only fresh vregs and replays no physical
            // register, stack-slot or special-register traffic; a nest that
            // writes or reads any such operand (a `Copy` into an ABI lane, a
            // frame address) has effects the rewrite would drop.
            if let Some(op) = inst.operands.iter().find(|op| {
                !matches!(
                    op,
                    MachOperand::VReg(_) | MachOperand::Imm(_) | MachOperand::Block(_)
                )
            }) {
                bail!("non-virtual operand {:?} in {:?}", op, inst.opcode);
            }
            match inst.opcode {
                AArch64Opcode::StrRI => {
                    stores += 1;
                    // Store base must trace (through Madd(idx,scale,base)) to c_base.
                    let Some(base) = store_base(func, def, inst) else {
                        bail!("store base not a Madd(idx,scale,base)");
                    };
                    if base != c_base {
                        bail!("store addresses non-c base {:?}", base);
                    }
                }
                AArch64Opcode::LdrRI => loads += 1,
                _ => {}
            }
        }
    }
    // Exactly the a load, the c load, the b load, and the single c store.
    if stores != 1 {
        bail!("expected exactly 1 store in the nest, found {}", stores);
    }
    if loads != 3 {
        bail!("expected exactly 3 loads in the nest, found {}", loads);
    }
    let _ = (a_base, b_base);
    true
}

/// The base register of a `StrRI`'s address, resolved through
/// `addr = Madd(idx, scale, base)`.
fn store_base(func: &MachFunction, def: &HashMap<u32, InstId>, store: &MachInst) -> Option<VReg> {
    if store.operands.len() != 3 {
        return None;
    }
    let addr = store.operands[1].as_vreg()?;
    let (_, _, base) = madd_addr(func, def, addr)?;
    Some(base)
}

/// The distinct stack slot a base register points at:
/// `base = AddPCRel(sp, StackSlot(id))`. Through copies.
///
/// Only the exact three-operand stack-address form
/// `AddPCRel [dst, sp, StackSlot(id)]` names the START of slot `id`; any
/// other operand list (an extra offset, a frame index, a symbol) is refused,
/// so the slot size the review bar checks is the extent the base can reach.
/// The base must also have exactly one definition, so the slot is the one
/// every use sees.
fn base_stack_slot(
    func: &MachFunction,
    def: &HashMap<u32, InstId>,
    base: VReg,
) -> Option<StackSlotId> {
    let v = strip_copies(func, def, base);
    if crate::effects::live_def_count(func, v.id) != 1 {
        return None;
    }
    let d = *def.get(&v.id)?;
    let inst = func.inst(d);
    if inst.opcode != AArch64Opcode::AddPCRel || inst.operands.len() != 3 {
        return None;
    }
    match (&inst.operands[0], &inst.operands[2]) {
        (MachOperand::VReg(dst), MachOperand::StackSlot(slot)) if *dst == v => Some(*slot),
        _ => None,
    }
}

/// Return `Some(child)` iff `child_header` is the UNIQUE loop whose parent is
/// `parent_header` (i.e. the parent nests exactly one immediate child loop).
/// Whether `preheader` is the guard block [`apply`] emits in front of the
/// scalar fallback nest: `CmpRI n_reg, #n ; BCond NE -> i_header ; B <other>`.
fn preheader_is_reg_block_guard(
    func: &MachFunction,
    preheader: BlockId,
    i_header: BlockId,
    n_reg: VReg,
    n_const: i64,
) -> bool {
    let insts = &func.block(preheader).insts;
    let (mut cmp, mut bne, mut b_other) = (false, false, false);
    for &id in insts {
        let inst = func.inst(id);
        match inst.opcode {
            AArch64Opcode::CmpRI
                if inst.operands.len() == 2
                    && inst.operands[0].as_vreg() == Some(n_reg)
                    && inst.operands[1].as_imm() == Some(n_const) =>
            {
                cmp = true;
            }
            AArch64Opcode::BCond
                if inst.operands.len() == 2
                    && inst.operands[0].as_imm() == Some(CC_NE)
                    && branch_targets(inst).first() == Some(&i_header) =>
            {
                bne = true;
            }
            AArch64Opcode::B if branch_targets(inst).first().is_some_and(|&t| t != i_header) => {
                b_other = true;
            }
            _ => {}
        }
    }
    cmp && bne && b_other
}

fn only_child(
    loops: &LoopAnalysis,
    parent_header: BlockId,
    child_header: BlockId,
) -> Option<BlockId> {
    let mut found = None;
    for lp in loops.all_loops() {
        if lp.parent == Some(parent_header) {
            if found.is_some() {
                return None; // more than one child
            }
            found = Some(lp.header);
        }
    }
    match found {
        Some(h) if h == child_header => Some(h),
        _ => None,
    }
}

/// The single latch of a loop (unique body block with a back-edge to `header`).
fn single_latch(func: &MachFunction, header: BlockId, body: &HashSet<BlockId>) -> Option<BlockId> {
    let mut latch = None;
    for &b in body {
        if func.block(b).succs.contains(&header) {
            if latch.is_some() {
                return None;
            }
            latch = Some(b);
        }
    }
    latch
}

// ---------------------------------------------------------------------------
// Transformation (register-blocked fast path spliced in front; guarded fallback)
// ---------------------------------------------------------------------------

#[allow(clippy::too_many_lines)]
/// Element widths the emitted kernel actually models.
///
/// [`apply`] builds every lane with `RegClass::Gpr64` and 64-bit loads, so the
/// rewrite is value-preserving ONLY for an 8-byte element. This predicate is
/// the single place that fact is enforced; widening it REQUIRES widening
/// `apply` (lane class, load opcode, element packing) in the same change.
fn kernel_supports_scale(scale: i64) -> bool {
    scale == 8
}

/// Can the k-loop body use the pointer-writeback shape (post-indexed `Ldr` for
/// `a`, `Ldp`/`LdpPostIndex` for the `b` tile) instead of plain `LdrRI`s plus
/// two explicit `AddRI` pointer bumps?
///
/// Requires, ALL checked here so the pass stays fail-closed onto the plain
/// shape rather than emitting an unencodable instruction:
///
/// * `scale == 8` — the pass allocates `Gpr64` lanes and `Ldp` of a 64-bit
///   register pair transfers 8 bytes per lane, so an element scale other than
///   8 would silently transfer the wrong width.
/// * `tiles` even — lanes are consumed two at a time.
/// * every pair offset in the LDP signed-imm7 range. That immediate is scaled
///   by 8 for a 64-bit pair, giving `[-64*8, 63*8] = [-512, 504]`, and the
///   offsets used are `m*scale` for even `m` in `2..tiles` plus the writeback
///   amount `N*scale`. Both are non-negative here, so the upper bound is the
///   only binding one; the lower bound is asserted anyway for clarity.
fn pair_writeback_ok(scale: i64, n_scale: i64, tiles: i64) -> bool {
    const LDP64_MIN: i64 = -512;
    const LDP64_MAX: i64 = 504;
    if scale != 8 || tiles % 2 != 0 || tiles < 2 {
        return false;
    }
    let max_lane_off = (tiles - 2) * scale;
    (LDP64_MIN..=LDP64_MAX).contains(&max_lane_off) && (LDP64_MIN..=LDP64_MAX).contains(&n_scale)
}

fn apply(func: &mut MachFunction, rec: &Recognized) -> bool {
    let n = rec.n_const;
    let scale = rec.scale_const;
    let n_scale = n * scale; // per-k b advance / per-i row advance
    let tiles = rec.tile; // lanes
    let tile_scale = tiles * scale; // per-tile advance

    // Fresh blocks.
    let guard = func.create_block();
    let entry = func.create_block();
    let ihdr = func.create_block();
    let jtpre = func.create_block();
    let jthdr = func.create_block();
    let tload = func.create_block();
    let khdr = func.create_block();
    let kbody = func.create_block();
    let tstore = func.create_block();
    let ilatch = func.create_block();
    insert_new_blocks_before(
        func,
        rec.i_header,
        &[
            guard, entry, ihdr, jtpre, jthdr, tload, khdr, kbody, tstore, ilatch,
        ],
    );

    // Edges (preheader redirect deferred to COMMIT).
    func.add_edge(guard, entry);
    func.add_edge(guard, rec.i_header); // fallback
    func.add_edge(entry, ihdr);
    func.add_edge(ihdr, jtpre);
    func.add_edge(ihdr, rec.exit_target);
    func.add_edge(jtpre, jthdr);
    func.add_edge(jthdr, tload);
    func.add_edge(jthdr, ilatch);
    func.add_edge(tload, khdr);
    func.add_edge(khdr, kbody);
    func.add_edge(khdr, tstore);
    func.add_edge(kbody, khdr);
    func.add_edge(tstore, jthdr);
    func.add_edge(ilatch, ihdr);

    // --- guard: dispatch to the fast path when the runtime N matches the
    // recognized constant (always true for the recognized const-N input; keeps
    // the untouched fallback nest reachable so mac-row-unroll still fires).
    emit(
        func,
        guard,
        AArch64Opcode::CmpRI,
        vec![vreg(rec.n_reg), imm(n)],
    );
    emit(
        func,
        guard,
        AArch64Opcode::BCond,
        vec![imm(CC_NE), block(rec.i_header)],
    );
    emit(func, guard, AArch64Opcode::B, vec![block(entry)]);

    // --- entry: i-loop running IVs. i counter, running c-row and a-row
    // pointers (pc_row = c_base + i*N*scale, pa_row = a_base + i*N*scale).
    let i_iv = alloc(func, RegClass::Gpr64);
    materialize_into(func, entry, i_iv, 0);
    let pc_row = alloc(func, RegClass::Gpr64);
    emit(
        func,
        entry,
        AArch64Opcode::MovR,
        vec![vreg(pc_row), vreg(rec.c_base)],
    );
    let pa_row = alloc(func, RegClass::Gpr64);
    emit(
        func,
        entry,
        AArch64Opcode::MovR,
        vec![vreg(pa_row), vreg(rec.a_base)],
    );
    emit(func, entry, AArch64Opcode::B, vec![block(ihdr)]);

    // --- ihdr: guard i < N -> body (jtpre) else exit.
    emit(func, ihdr, AArch64Opcode::CmpRI, vec![vreg(i_iv), imm(n)]);
    emit(
        func,
        ihdr,
        AArch64Opcode::BCond,
        vec![imm(CC_HS), block(rec.exit_target)],
    );
    emit(func, ihdr, AArch64Opcode::B, vec![block(jtpre)]);

    // --- jtpre: jt-loop running IVs. jt counter, pc_tile (= pc_row + jt*scale),
    // pb_tile (= b_base + jt*scale). At jt=0 they equal pc_row and b_base.
    let jt_iv = alloc(func, RegClass::Gpr64);
    materialize_into(func, jtpre, jt_iv, 0);
    let pc_tile = alloc(func, RegClass::Gpr64);
    emit(
        func,
        jtpre,
        AArch64Opcode::MovR,
        vec![vreg(pc_tile), vreg(pc_row)],
    );
    let pb_tile = alloc(func, RegClass::Gpr64);
    emit(
        func,
        jtpre,
        AArch64Opcode::MovR,
        vec![vreg(pb_tile), vreg(rec.b_base)],
    );
    emit(func, jtpre, AArch64Opcode::B, vec![block(jthdr)]);

    // --- jthdr: guard jt < N -> tile (tload) else i-latch.
    emit(func, jthdr, AArch64Opcode::CmpRI, vec![vreg(jt_iv), imm(n)]);
    emit(
        func,
        jthdr,
        AArch64Opcode::BCond,
        vec![imm(CC_HS), block(ilatch)],
    );
    emit(func, jthdr, AArch64Opcode::B, vec![block(tload)]);

    // --- tload: load T accumulators from c tile, set k-loop running pointers.
    let mut acc: Vec<VReg> = Vec::with_capacity(tiles as usize);
    for m in 0..tiles {
        let cm = alloc(func, RegClass::Gpr64);
        emit(
            func,
            tload,
            AArch64Opcode::LdrRI,
            vec![vreg(cm), vreg(pc_tile), imm(m * scale)],
        );
        acc.push(cm);
    }
    let pa = alloc(func, RegClass::Gpr64);
    emit(
        func,
        tload,
        AArch64Opcode::MovR,
        vec![vreg(pa), vreg(pa_row)],
    );
    let pb = alloc(func, RegClass::Gpr64);
    emit(
        func,
        tload,
        AArch64Opcode::MovR,
        vec![vreg(pb), vreg(pb_tile)],
    );
    let k_iv = alloc(func, RegClass::Gpr64);
    materialize_into(func, tload, k_iv, 0);
    emit(func, tload, AArch64Opcode::B, vec![block(khdr)]);

    // --- khdr: guard k < N -> body else store the tile.
    emit(func, khdr, AArch64Opcode::CmpRI, vec![vreg(k_iv), imm(n)]);
    emit(
        func,
        khdr,
        AArch64Opcode::BCond,
        vec![imm(CC_HS), block(tstore)],
    );
    emit(func, khdr, AArch64Opcode::B, vec![block(kbody)]);

    // --- kbody: aik = a[pa]; for m: acc[m] += aik * b[pb + m*scale]; advance
    // pa += scale, pb += N*scale, k += 1; back to khdr.
    //
    // Two shapes, selected by `writeback_pairs` (see `pair_writeback_ok`):
    //
    // * WRITEBACK shape (the fast one, taken whenever the offsets encode):
    //   `aik` is loaded with a post-indexed `LdrPostIndex [pa], #scale` and the
    //   `b` tile is read as `T/2` `Ldp`s issued in DESCENDING lane order,
    //   the LAST of which (`m == 0`) is an `LdpPostIndex [pb], #N*scale`. The
    //   two separate `AddRI` pointer bumps disappear into those two loads, so
    //   the k-loop shrinks from `2*T + 6` to `2*T + 4` instructions.
    //   Descending order is deliberate: it keeps the three non-writeback `Ldp`s
    //   OFF the base-update recurrence (they read the pre-bump `pb`), which
    //   measured ~2.5% faster on p4_matmul than the ascending order that hangs
    //   each subsequent load off the just-written base.
    // * PLAIN shape (unchanged fallback): `LdrRI`/`LdrRI` + two `AddRI` bumps.
    //   Kept for any recognized nest whose `scale`/`N` push a pair offset out
    //   of the LDP signed-imm7 range, so the pass never fails to apply.
    //
    // Both shapes compute exactly the same values in exactly the same k-order;
    // the writeback shape only folds the two pointer increments the plain shape
    // performs explicitly at the END of the body into the loads that are the
    // last readers of each pointer in the body.
    let writeback_pairs = pair_writeback_ok(scale, n_scale, tiles);
    let aik = alloc(func, RegClass::Gpr64);
    if writeback_pairs {
        emit(
            func,
            kbody,
            AArch64Opcode::LdrPostIndex,
            vec![vreg(aik), vreg(pa), imm(scale)],
        );
    } else {
        emit(
            func,
            kbody,
            AArch64Opcode::LdrRI,
            vec![vreg(aik), vreg(pa), imm(0)],
        );
    }
    let mac = |func: &mut MachFunction, m: i64, bm: VReg| {
        let cm_new = alloc(func, RegClass::Gpr64);
        emit(
            func,
            kbody,
            AArch64Opcode::Madd,
            vec![vreg(cm_new), vreg(aik), vreg(bm), vreg(acc[m as usize])],
        );
        // carry the accumulator in-place (MovR into the same acc reg).
        emit(
            func,
            kbody,
            AArch64Opcode::MovR,
            vec![vreg(acc[m as usize]), vreg(cm_new)],
        );
    };
    if writeback_pairs {
        // Descending pairs; the m == 0 pair carries the `pb += N*scale`
        // writeback and is therefore emitted last.
        let mut m = tiles - 2;
        while m >= 0 {
            let b0 = alloc(func, RegClass::Gpr64);
            let b1 = alloc(func, RegClass::Gpr64);
            let (op, off) = if m == 0 {
                (AArch64Opcode::LdpPostIndex, n_scale)
            } else {
                (AArch64Opcode::LdpRI, m * scale)
            };
            emit(
                func,
                kbody,
                op,
                vec![vreg(b0), vreg(b1), vreg(pb), imm(off)],
            );
            mac(func, m, b0);
            mac(func, m + 1, b1);
            m -= 2;
        }
    } else {
        for m in 0..tiles {
            let bm = alloc(func, RegClass::Gpr64);
            emit(
                func,
                kbody,
                AArch64Opcode::LdrRI,
                vec![vreg(bm), vreg(pb), imm(m * scale)],
            );
            mac(func, m, bm);
        }
        emit(
            func,
            kbody,
            AArch64Opcode::AddRI,
            vec![vreg(pa), vreg(pa), imm(scale)],
        );
        emit(
            func,
            kbody,
            AArch64Opcode::AddRI,
            vec![vreg(pb), vreg(pb), imm(n_scale)],
        );
    }
    let k_next = alloc(func, RegClass::Gpr64);
    emit(
        func,
        kbody,
        AArch64Opcode::AddRI,
        vec![vreg(k_next), vreg(k_iv), imm(1)],
    );
    emit(
        func,
        kbody,
        AArch64Opcode::MovR,
        vec![vreg(k_iv), vreg(k_next)],
    );
    emit(func, kbody, AArch64Opcode::B, vec![block(khdr)]);

    // --- tstore: store the T accumulators back to the c tile; advance the
    // jt-loop IVs (jt += T, pc_tile += T*scale, pb_tile += T*scale).
    for m in 0..tiles {
        emit(
            func,
            tstore,
            AArch64Opcode::StrRI,
            vec![vreg(acc[m as usize]), vreg(pc_tile), imm(m * scale)],
        );
    }
    let jt_next = alloc(func, RegClass::Gpr64);
    emit(
        func,
        tstore,
        AArch64Opcode::AddRI,
        vec![vreg(jt_next), vreg(jt_iv), imm(tiles)],
    );
    emit(
        func,
        tstore,
        AArch64Opcode::MovR,
        vec![vreg(jt_iv), vreg(jt_next)],
    );
    emit(
        func,
        tstore,
        AArch64Opcode::AddRI,
        vec![vreg(pc_tile), vreg(pc_tile), imm(tile_scale)],
    );
    emit(
        func,
        tstore,
        AArch64Opcode::AddRI,
        vec![vreg(pb_tile), vreg(pb_tile), imm(tile_scale)],
    );
    emit(func, tstore, AArch64Opcode::B, vec![block(jthdr)]);

    // --- ilatch: advance the i-loop IVs (i += 1, pc_row += N*scale, pa_row +=
    // N*scale); back to ihdr.
    let i_next = alloc(func, RegClass::Gpr64);
    emit(
        func,
        ilatch,
        AArch64Opcode::AddRI,
        vec![vreg(i_next), vreg(i_iv), imm(1)],
    );
    emit(
        func,
        ilatch,
        AArch64Opcode::MovR,
        vec![vreg(i_iv), vreg(i_next)],
    );
    emit(
        func,
        ilatch,
        AArch64Opcode::AddRI,
        vec![vreg(pc_row), vreg(pc_row), imm(n_scale)],
    );
    emit(
        func,
        ilatch,
        AArch64Opcode::AddRI,
        vec![vreg(pa_row), vreg(pa_row), imm(n_scale)],
    );
    emit(func, ilatch, AArch64Opcode::B, vec![block(ihdr)]);

    // --- COMMIT: redirect the i-loop preheader terminator to the guard.
    if !rewrite_block_target(func.inst_mut(rec.preheader_term), rec.i_header, guard) {
        return false;
    }
    remove_cfg_edge(func, rec.preheader, rec.i_header);
    func.add_edge(rec.preheader, guard);
    true
}

// ---------------------------------------------------------------------------
// Small local IR helpers (independent copies, as in the sibling passes)
// ---------------------------------------------------------------------------

fn vreg(v: VReg) -> MachOperand {
    MachOperand::VReg(v)
}
fn imm(v: i64) -> MachOperand {
    MachOperand::Imm(v)
}
fn block(b: BlockId) -> MachOperand {
    MachOperand::Block(b)
}

fn madd_parts_val(inst: &MachInst) -> Option<(VReg, VReg, VReg)> {
    if inst.opcode == AArch64Opcode::Madd && inst.operands.len() == 4 {
        Some((
            inst.operands[1].as_vreg()?,
            inst.operands[2].as_vreg()?,
            inst.operands[3].as_vreg()?,
        ))
    } else {
        None
    }
}

fn madd_addr(
    func: &MachFunction,
    def: &HashMap<u32, InstId>,
    addr: VReg,
) -> Option<(VReg, VReg, VReg)> {
    let &d = def.get(&addr.id)?;
    madd_parts_val(func.inst(d))
}

fn madd_index(
    func: &MachFunction,
    def: &HashMap<u32, InstId>,
    idx: VReg,
) -> Option<(VReg, VReg, VReg)> {
    let &d = def.get(&idx.id)?;
    madd_parts_val(func.inst(d))
}

fn ldr_addr(func: &MachFunction, def: &HashMap<u32, InstId>, v: VReg) -> Option<VReg> {
    let &d = def.get(&v.id)?;
    let inst = func.inst(d);
    if inst.opcode == AArch64Opcode::LdrRI
        && inst.operands.len() == 3
        && inst.operands[2].as_imm() == Some(0)
    {
        inst.operands[1].as_vreg()
    } else {
        None
    }
}

fn find_unit_induction(
    func: &MachFunction,
    def: &HashMap<u32, InstId>,
    latch: BlockId,
) -> Option<VReg> {
    for &id in &func.block(latch).insts {
        if let Some((d, s)) = copy_like(func.inst(id)) {
            if d.class != RegClass::Gpr64 {
                continue;
            }
            if let Some(&sdef) = def.get(&s.id) {
                let si = func.inst(sdef);
                if is_add1(si) && si.operands[1].as_vreg() == Some(d) {
                    return Some(d);
                }
            }
        }
    }
    for &id in &func.block(latch).insts {
        let inst = func.inst(id);
        if is_add1(inst) {
            let d = inst.operands[0].as_vreg()?;
            if d.class == RegClass::Gpr64 && inst.operands[1].as_vreg() == Some(d) {
                return Some(d);
            }
        }
    }
    None
}

fn is_add1(inst: &MachInst) -> bool {
    inst.opcode == AArch64Opcode::AddRI
        && inst.operands.len() == 3
        && inst.operands[2].as_imm() == Some(1)
}

/// `(index, constant length)` of a proof-only bounds carrier
/// `TrapBoundsCheckExact [base, index, Imm(len)]`, which traps iff
/// `!(index <u len)`. The base operand is identity metadata for proof
/// binding and does not take part in the runtime check. A carrier whose
/// length is a register (the dynamic-length form) is not a compile-time
/// length and yields `None`.
fn bounds_carrier(inst: &MachInst) -> Option<(VReg, i64)> {
    if inst.opcode != AArch64Opcode::TrapBoundsCheckExact || inst.operands.len() != 3 {
        return None;
    }
    inst.operands[0].as_vreg()?;
    Some((inst.operands[1].as_vreg()?, inst.operands[2].as_imm()?))
}

/// The constant length a bounds check of `idx` in `body` compares against.
///
/// Two check forms are recognized. A trust-ir `icmp ult` + `condbr` to a
/// failure block lowers to the expanded `CmpRI/CmpRR idx, L ; BCond LO/LT ->
/// body ; B -> outside` diamond. The rustc bridge emits a MIR
/// `Assert(BoundsCheck)` in this form, its failure block calling
/// `panic_bounds_check(index, len, &Location)` and then `unreachable`. The
/// proof-only carrier `TrapBoundsCheckExact [idx, idx, #L]` inside a
/// straight-line block traps on failure and expands to `CMP; B.LO; BRK` only
/// after optimization. It is what a same-block `const` + `icmp ult` +
/// `assert` triple lowered to: the bridge's spelling of a constant-length
/// check before TrustIR v52, which the shared admission floor now refuses as
/// a kindless source `assert`, so the bridge no longer reaches this pass with
/// carriers. Either form names `L`. This only locates the length; the review
/// bar classifies EVERY check and carrier in the nest
/// (`review_bar::check_mandatory_control_flow`).
fn find_bounds_check(
    func: &MachFunction,
    def: &HashMap<u32, InstId>,
    body: &HashSet<BlockId>,
    idx: VReg,
) -> Option<i64> {
    let mut blocks: Vec<BlockId> = body.iter().copied().collect();
    blocks.sort_unstable();
    for &b in &blocks {
        for &id in &func.block(b).insts {
            if let Some((index, len)) = bounds_carrier(func.inst(id))
                && same_as(func, def, index, idx)
            {
                return Some(len);
            }
        }
    }
    for &b in body {
        let mut bound: Option<i64> = None;
        for &id in &func.block(b).insts {
            let inst = func.inst(id);
            match inst.opcode {
                AArch64Opcode::CmpRR if inst.operands.len() == 2 => {
                    if same_as(func, def, inst.operands[0].as_vreg()?, idx) {
                        bound = copied_const(func, def, inst.operands[1].as_vreg()?);
                    }
                }
                AArch64Opcode::CmpRI
                    if inst.operands.len() == 2
                        && same_as(func, def, inst.operands[0].as_vreg()?, idx) =>
                {
                    bound = inst.operands[1].as_imm();
                }
                _ => {}
            }
        }
        let Some(l) = bound else { continue };
        let mut lo_to_body = false;
        let mut has_exit = false;
        for &id in &func.block(b).insts {
            let inst = func.inst(id);
            if inst.opcode == AArch64Opcode::BCond && inst.operands.len() == 2 {
                let cc = inst.operands[0].as_imm()?;
                let tgt = *branch_targets(inst).first()?;
                if (cc == CC_LO || cc == CC_LT) && body.contains(&tgt) {
                    lo_to_body = true;
                }
            }
        }
        for &s in &func.block(b).succs {
            if !body.contains(&s) {
                has_exit = true;
            }
        }
        if lo_to_body && has_exit {
            return Some(l);
        }
    }
    None
}

fn recognize_native_const_bound(
    func: &MachFunction,
    def: &HashMap<u32, InstId>,
    body: &HashSet<BlockId>,
    header: BlockId,
    iv: VReg,
) -> Option<i64> {
    let mut cmp_bound: Option<i64> = None;
    for &id in &func.block(header).insts {
        let inst = func.inst(id);
        match inst.opcode {
            AArch64Opcode::CmpRR if inst.operands.len() == 2 => {
                if same_as(func, def, inst.operands[0].as_vreg()?, iv) {
                    cmp_bound = copied_const(func, def, inst.operands[1].as_vreg()?);
                }
            }
            AArch64Opcode::CmpRI
                if inst.operands.len() == 2
                    && same_as(func, def, inst.operands[0].as_vreg()?, iv) =>
            {
                cmp_bound = inst.operands[1].as_imm();
            }
            _ => {}
        }
    }
    let n = cmp_bound?;
    let mut has_forward = false;
    for &id in &func.block(header).insts {
        let inst = func.inst(id);
        if inst.opcode == AArch64Opcode::BCond && inst.operands.len() == 2 {
            let cc = inst.operands[0].as_imm()?;
            let tgt = *branch_targets(inst).first()?;
            if (cc == CC_LT || cc == CC_LO) && body.contains(&tgt) {
                has_forward = true;
            }
        }
    }
    if !has_forward {
        return None;
    }
    func.block(header)
        .succs
        .iter()
        .find(|s| !body.contains(s))?;
    Some(n)
}

/// Verify that `loop(header, body)` is a canonical `for iv in 0..N` counted
/// loop: a native forward `iv < N` header test, `iv` initialized to `0` from
/// outside the loop, and `iv` advanced by exactly `+1` per iteration, where the
/// loop's counter is the same loop-carried value as `index_iv` (the register
/// used in the nest's index `madd`s). Robust to the conventional-SSA `MovR`-phi
/// / body-copy / self-copy forms; fail-closed on anything else.
///
/// Returns the loop-carried counter, its latch step and its init, which the
/// review bar uses to refuse a read of the counter after that step or outside
/// the loop, and an init that does not run once per parent iteration.
fn verify_counted_0_n(
    func: &MachFunction,
    def: &HashMap<u32, InstId>,
    body: &HashSet<BlockId>,
    header: BlockId,
    index_iv: VReg,
    n_const: i64,
    dump: bool,
) -> Option<review_bar::CountedLoop> {
    macro_rules! nope {
        ($($t:tt)*) => {{ if dump { eprintln!("[mac-reg-block] counted-loop reject: {}", format!($($t)*)); } return None; }};
    }
    let Some(latch) = single_latch(func, header, body) else {
        nope!("no single latch");
    };
    // (1) header forward test `t < N` -> body.
    let Some((t, bound)) = find_header_iv_test(func, def, body, header) else {
        nope!("no native forward iv<const header test");
    };
    if bound != n_const {
        nope!("header bound {} != N {}", bound, n_const);
    }
    // (2) resolve the tested value and the index value to the loop-carried
    // counter; they must be the SAME induction.
    let Some(c_t) = resolve_to_carried(func, t, latch) else {
        nope!("header-tested value does not resolve to a loop-carried counter");
    };
    let Some(c_i) = resolve_to_carried(func, index_iv, latch) else {
        nope!("index iv does not resolve to a loop-carried counter");
    };
    if c_t != c_i {
        nope!("header counter {:?} != index counter {:?}", c_t, c_i);
    }
    let counter = c_t;
    // (3) the counter's defs: exactly one `+1` step in the latch and one
    // `init = 0` from outside the loop (self-copies of the counter ignored).
    // An init inside the body would reset the counter mid-loop, so the
    // non-latch def must lie OUTSIDE the loop body; the review bar also
    // requires it once per parent iteration (`check_counter_inits`).
    let mut init = None;
    let mut step = None;
    for d in find_all_defs(func, counter) {
        let blk = block_of_inst(func, d)?;
        let inst = func.inst(d);
        // Ignore a degenerate self-copy `counter = MovR(counter)`.
        if let Some((dst, src)) = copy_like(inst)
            && dst == counter
            && src == counter
        {
            continue;
        }
        if blk == latch {
            if step.is_some() {
                nope!("multiple latch defs of the counter");
            }
            if !latch_def_is_unit_step(func, def, inst, counter, latch) {
                nope!("latch def of the counter is not a +1 step");
            }
            step = Some(d);
        } else {
            if body.contains(&blk) {
                nope!("a non-latch def of the counter lies inside the loop body");
            }
            if init.is_some() {
                nope!("multiple out-of-loop defs of the counter");
            }
            let z = if let Some((dst, src)) = copy_like(inst) {
                dst == counter && copied_const(func, def, src) == Some(0)
            } else {
                is_movz_zero(inst)
            };
            if !z {
                nope!("out-of-loop init of the counter is not 0");
            }
            init = Some(d);
        }
    }
    let (Some(init), Some(step)) = (init, step) else {
        nope!(
            "counter missing init(0)={} step(+1)={}",
            init.is_some(),
            step.is_some()
        );
    };
    Some(review_bar::CountedLoop {
        counter,
        latch,
        step,
        init,
    })
}

/// The latch def of the counter must be a `+1` step: either the in-place
/// `counter = AddRI(x, 1)` or the copy form `counter = MovR(inc)` with
/// `inc = AddRI(x, 1)`, where `x` resolves to the same loop-carried counter.
fn latch_def_is_unit_step(
    func: &MachFunction,
    _def: &HashMap<u32, InstId>,
    inst: &MachInst,
    counter: VReg,
    latch: BlockId,
) -> bool {
    // in-place: counter = AddRI(x, 1)
    if is_add1(inst) {
        return inst.operands[1]
            .as_vreg()
            .and_then(|x| resolve_to_carried(func, x, latch))
            == Some(counter);
    }
    // copy: counter = MovR(inc), inc = AddRI(x, 1)
    if let Some((dst, inc)) = copy_like(inst) {
        if dst != counter {
            return false;
        }
        // find inc's (unique) AddRI(_, 1) def
        for d in find_all_defs(func, inc) {
            let ii = func.inst(d);
            if is_add1(ii) {
                return ii.operands[1]
                    .as_vreg()
                    .and_then(|x| resolve_to_carried(func, x, latch))
                    == Some(counter);
            }
        }
    }
    false
}

fn is_movz_zero(inst: &MachInst) -> bool {
    inst.opcode == AArch64Opcode::Movz
        && inst.operands.len() == 2
        && inst.operands[1].as_imm() == Some(0)
}

/// Resolve a value to its loop-carried counter: follow single non-self copy
/// defs until a value that has a def IN the latch (the loop-carried phi value).
/// Fail-closed (None) on any ambiguity (a non-copy def, more than one non-self
/// copy source, or no resolution within the bound).
fn resolve_to_carried(func: &MachFunction, v: VReg, latch: BlockId) -> Option<VReg> {
    let mut cur = v;
    for _ in 0..32 {
        let defs = find_all_defs(func, cur);
        if defs.is_empty() {
            return None;
        }
        // Loop-carried iff it has a def in the latch.
        if defs.iter().any(|&d| block_of_inst(func, d) == Some(latch)) {
            return Some(cur);
        }
        // Otherwise follow the unique non-self copy source.
        let mut srcs: HashSet<VReg> = HashSet::default();
        for &d in &defs {
            let ii = func.inst(d);
            match copy_like(ii) {
                Some((dst, src)) if dst == cur && src != cur => {
                    srcs.insert(src);
                }
                Some((dst, src)) if dst == cur && src == cur => {} // self-copy: ignore
                _ => return None, // a non-copy def: not a pure iv copy
            }
        }
        if srcs.len() != 1 {
            return None;
        }
        cur = *srcs.iter().next().unwrap();
    }
    None
}

/// Find the header's forward `iv < const` continue test: a `CmpRR/CmpRI(t, N)`
/// paired with a `BCond LT/LO -> body` in `header`. Returns `(t, N)`.
fn find_header_iv_test(
    func: &MachFunction,
    def: &HashMap<u32, InstId>,
    body: &HashSet<BlockId>,
    header: BlockId,
) -> Option<(VReg, i64)> {
    // Must have a forward LT/LO branch into the body and a non-body exit.
    let mut has_forward = false;
    for &id in &func.block(header).insts {
        let inst = func.inst(id);
        if inst.opcode == AArch64Opcode::BCond && inst.operands.len() == 2 {
            let cc = inst.operands[0].as_imm()?;
            let tgt = *branch_targets(inst).first()?;
            if (cc == CC_LT || cc == CC_LO) && body.contains(&tgt) {
                has_forward = true;
            }
        }
    }
    if !has_forward || func.block(header).succs.iter().all(|s| body.contains(s)) {
        return None;
    }
    let mut found: Option<(VReg, i64)> = None;
    for &id in &func.block(header).insts {
        let inst = func.inst(id);
        match inst.opcode {
            AArch64Opcode::CmpRR if inst.operands.len() == 2 => {
                let t = inst.operands[0].as_vreg()?;
                if let Some(b) = copied_const(func, def, inst.operands[1].as_vreg()?) {
                    found = Some((t, b));
                }
            }
            AArch64Opcode::CmpRI if inst.operands.len() == 2 => {
                let t = inst.operands[0].as_vreg()?;
                if let Some(b) = inst.operands[1].as_imm() {
                    found = Some((t, b));
                }
            }
            _ => {}
        }
    }
    found
}

/// All instruction defs of `v` (a value may be defined in several blocks under
/// the conventional-SSA `MovR`-phi form).
fn find_all_defs(func: &MachFunction, v: VReg) -> Vec<InstId> {
    let mut out = Vec::new();
    for &bid in &func.block_order {
        for &id in &func.block(bid).insts {
            if crate::effects::inst_defines_vreg(func.inst(id), v) {
                out.push(id);
            }
        }
    }
    out
}

fn is_loop_invariant(
    func: &MachFunction,
    def: &HashMap<u32, InstId>,
    dom: &DomTree,
    loop_insts: &HashSet<InstId>,
    preheader: BlockId,
    v: VReg,
) -> bool {
    for &id in loop_insts {
        if crate::effects::inst_defines_vreg(func.inst(id), v) {
            return false;
        }
    }
    let Some(&d) = def.get(&v.id) else {
        return !func.block_order.iter().any(|&bid| {
            func.block(bid)
                .insts
                .iter()
                .any(|&id| crate::effects::inst_defines_vreg(func.inst(id), v))
        });
    };
    let Some(db) = block_of_inst(func, d) else {
        return false;
    };
    dom.dominates(db, preheader)
}

/// Whitelist for the inner j-loop body (the mac-row-unroll shape, with its
/// bounds checks either expanded or as `TrapBoundsCheckExact` carriers).
fn allowed_inner_op(op: AArch64Opcode) -> bool {
    use AArch64Opcode::*;
    matches!(
        op,
        Madd | AddRI
            | MovR
            | Copy
            | CmpRR
            | CmpRI
            | BCond
            | B
            | LdrRI
            | StrRI
            | TrapBoundsCheckExact
    )
}

/// Whitelist for the WHOLE i-loop body (the inner shape plus the k/i loop
/// machinery, which is the same opcode set — index `Madd`s, iv `AddRI`s, phi
/// `MovR`s, guards or bounds carriers, and the three loads / one store).
/// Admitting `TrapBoundsCheckExact` here is safe only because the review bar
/// classifies every carrier in the nest as a check of a recognized current
/// index against a constant length of at least `N*N`
/// (`review_bar::check_bounds_carrier`); no other trap pseudo is admitted.
fn allowed_nest_op(op: AArch64Opcode) -> bool {
    use AArch64Opcode::*;
    matches!(
        op,
        Madd | AddRI
            | MovR
            | Copy
            | CmpRR
            | CmpRI
            | BCond
            | B
            | LdrRI
            | StrRI
            | TrapBoundsCheckExact
    )
}

fn same_as(func: &MachFunction, def: &HashMap<u32, InstId>, v: VReg, w: VReg) -> bool {
    strip_copies(func, def, v) == strip_copies(func, def, w)
}

fn block_of_inst(func: &MachFunction, target: InstId) -> Option<BlockId> {
    for (idx, blk) in func.blocks.iter().enumerate() {
        if blk.insts.contains(&target) {
            return Some(BlockId(idx as u32));
        }
    }
    None
}

fn collect_insts(func: &MachFunction, body: &HashSet<BlockId>) -> HashSet<InstId> {
    let mut set = HashSet::default();
    for &b in body {
        for &id in &func.block(b).insts {
            set.insert(id);
        }
    }
    set
}

fn rewrite_block_target(inst: &mut MachInst, old: BlockId, new: BlockId) -> bool {
    let mut changed = false;
    for op in inst.operands.iter_mut() {
        if let MachOperand::Block(b) = op
            && *b == old
        {
            *b = new;
            changed = true;
        }
    }
    changed
}

fn remove_cfg_edge(func: &mut MachFunction, from: BlockId, to: BlockId) {
    func.block_mut(from).succs.retain(|&b| b != to);
    func.block_mut(to).preds.retain(|&b| b != from);
}

fn insert_new_blocks_before(func: &mut MachFunction, before: BlockId, new_blocks: &[BlockId]) {
    let mut reordered = Vec::with_capacity(func.block_order.len() + new_blocks.len());
    for &b in &func.block_order {
        if b == before {
            reordered.extend(new_blocks.iter().copied());
        }
        if !new_blocks.contains(&b) {
            reordered.push(b);
        }
    }
    func.block_order = reordered;
}

fn emit(
    func: &mut MachFunction,
    b: BlockId,
    op: AArch64Opcode,
    operands: Vec<MachOperand>,
) -> InstId {
    let id = func.push_inst(MachInst::new(op, operands));
    func.append_inst(b, id);
    id
}

/// Materialize a `[0, u32::MAX]` constant into an EXISTING fresh `Gpr64` `d`
/// via `Movz` + `Movk` chunks, appended to `blk`.
fn materialize_into(func: &mut MachFunction, blk: BlockId, d: VReg, value: i64) {
    let bits = value as u64;
    emit(
        func,
        blk,
        AArch64Opcode::Movz,
        vec![vreg(d), imm((bits & 0xFFFF) as i64)],
    );
    for hw in 1..4u32 {
        let chunk = (bits >> (hw * 16)) & 0xFFFF;
        if chunk != 0 {
            emit(
                func,
                blk,
                AArch64Opcode::Movk,
                vec![vreg(d), imm(chunk as i64), imm((hw * 16) as i64)],
            );
        }
    }
}

fn alloc(func: &mut MachFunction, class: RegClass) -> VReg {
    let max_existing = func
        .insts
        .iter()
        .flat_map(|inst| inst.operands.iter())
        .filter_map(MachOperand::as_vreg)
        .map(|v| v.id)
        .max()
        .unwrap_or(0);
    let mut id = func.alloc_vreg();
    while id <= max_existing {
        id = func.alloc_vreg();
    }
    VReg::new(id, class)
}
