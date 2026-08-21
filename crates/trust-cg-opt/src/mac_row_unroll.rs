// trust-cg-opt - SOUND aarch64 scalar RMW-MAC row-loop partial-unroll (x4)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! # RMW-MAC row-loop partial-unroll (`mac-row-unroll`)
//!
//! Partially unrolls (x4) an innermost, counted, bounds-checked scalar
//! read-modify-write multiply-accumulate ("AXPY-row") loop of the shape
//!
//! ```text
//! let mut j = 0;
//! while j <u N { c[cb + j] = c[cb + j] + aik * b[bb + j]; j += 1; }
//! ```
//!
//! where `cb = i*N`, `bb = k*N`, `aik` are all loop-invariant in `j`, `N` is a
//! compile-time-constant loop bound, and the two index streams `cidx = i*N + j`
//! and `bidx = k*N + j` are both bounds-checked against the SAME compile-time
//! array length `L` (`index <u L` guards each access). This is the innermost
//! `j`-loop of the `p4_matmul` kernel `c[i*N+j] += a[i*N+k]*b[k*N+j]`, which
//! LLVM 4x-unrolls with running pointers; the bridge does not, paying (per MAC)
//! three address `madd`s, three un-eliminated bounds branches, and a full
//! `c[cidx]` reload/restore.
//!
//! ## What it does (partial-unroll-with-pre-guard; mirrors `strided_store_unroll`)
//!
//! The pass is PURELY ADDITIVE: it splices a guarded, 4x-unrolled MAIN loop in
//! FRONT of the scalar loop and NEVER edits the scalar loop's instructions. The
//! scalar loop is left byte-for-byte intact as the exact `trip mod 4` remainder
//! handler AND the fallback when any guard fails. Fresh blocks (spliced before
//! the scalar header; the preheader redirect deferred to a final COMMIT):
//!
//! * `g0` (setup, once): materialize the loop constants `N-3` and `L-3`, and
//!   INITIALIZE the four running induction variables from the entry `j`
//!   (address-SR + row-base LICM): the c/b indices `cidx_iv = i*N+j`,
//!   `bidx_iv = k*N+j`, and the running byte pointers `pc = c_base + cidx_iv*s`,
//!   `pb = b_base + bidx_iv*s` (`s` = the scalar element scale).
//! * `hdr` (main header; re-entered each block-of-4): guard `j <u N-3`
//!   (`B.HS -> scalar`). No per-block index/address recompute — the running IVs
//!   carry them, so the two per-block index `madd`s and the two per-block
//!   address derivations are gone from the loop body.
//! * `gc` guard `cidx_iv <u L-3` (`B.HS -> scalar`); `gb` guard
//!   `bidx_iv <u L-3` (`B.HS -> scalar`). The guards stay on the EXPLICIT index
//!   IVs (not the pointers), so bounds behavior is bit-identical and needs no
//!   address-non-wrap assumption. Together (checked EACH block-of-4) these
//!   subsume the scalar loop's three per-iteration bounds branches: they prove
//!   all four `j`s in the block are `< N` (a legitimate scalar iteration) and
//!   the largest `c`/`b` index (`cidx_iv+3`, `bidx_iv+3`) is `<= L-1`
//!   (in-bounds).
//! * `mb` (the 4x body + back-edge): four verbatim lanes, EACH preserving the
//!   exact scalar per-lane memory order — `ldr c[cidx_iv+m]; ldr b[bidx_iv+m];
//!   madd aik*b + c; str c[cidx_iv+m]` — at byte addresses `pc + m*s`,
//!   `pb + m*s` via the immediate-offset addressing mode (`LdrRI/StrRI
//!   [p, #m*s]`, no per-lane address `AddRI`). Then advance the running
//!   pointers by `UNROLL*s`, the running indices and the shared iv by `UNROLL`,
//!   all IN-PLACE, and branch back to `hdr`.
//! * COMMIT: redirect the preheader terminator `scalar -> g0`.
//!
//! ## Why this is SOUND (bit-identical, guard-subsumed, wrap-free, no division)
//!
//! 1. **Compute = 4 scalar iterations, bit-for-bit, under ANY aliasing.** Each
//!    lane emits the EXACT scalar per-lane memory order at the SAME byte
//!    addresses the scalar `madd`s form: lane `m` accesses element `cidx+m`
//!    (`= i*N + (j+m)`) and `bidx+m` (`= k*N + (j+m)`) — precisely the elements
//!    the untouched scalar loop touches at iteration `j+m`. No load/store is
//!    reordered within or across lanes, so even if `b` and `c` alias, every load
//!    reads the value it would in the scalar sequence and every store writes the
//!    same value in the same order. The accumulate `Madd(aik, b, c)` is the
//!    identical op (`aik*b + c` over Z/2^64) the scalar loop uses.
//! 2. **Bounds behavior preserved (guard subsumption, re-checked per block).**
//!    A block of four runs only when `j <u N-3` (all four `j`s `< N`) AND
//!    `cidx <u L-3` AND `bidx <u L-3` (so `cidx+3, bidx+3 <= L-1`). These are
//!    re-evaluated at `hdr` on EVERY block-of-4 (the loop is
//!    `hdr->gc->gb->mb->hdr`), so no later iteration can drift out of range —
//!    the `cidx/bidx` guards are NOT hoisted to a once-only entry. On any guard
//!    failure control falls to the untouched scalar remainder, which reproduces
//!    the exact per-access trap/abort at the original logical index. Guard
//!    arithmetic is wrap-free: unsigned `idx <u (const)` never computes `idx+3`;
//!    `N-3`, `L-3` are compile-time constants materialized once; `N,L in
//!    [4, u32::MAX]`.
//!
//! **(2b) The MAC really is unconditional (recognition step 8).** Points 1 and
//! 2 say what the recognized chain DOES; they do not say that it RUNS. Since
//! the main block is straight-line, recognition additionally requires the
//! store's block to DOMINATE THE LATCH (with the two loads and the accumulate
//! `Madd` dominating that store), and requires the ONLY loop-exiting blocks to
//! be the header and the three recognized bounds-check blocks — exactly the
//! transfers the spliced guards subsume. Without this, a predicated MAC
//! (`if p { c[..] += aik*b[..] }`) or an early `break` is unrolled into four
//! unconditional MACs. Both BAIL.
//!
//! 3. **Additive:** the scalar loop's instructions are untouched; only new
//!    blocks are spliced before it and the preheader terminator is redirected at
//!    COMMIT (deferred so a mid-build bail cannot corrupt the CFG). The shared-iv
//!    advance-in-place hands off to the remainder exactly like
//!    `strided_store_unroll`.
//!
//! Every emitted opcode (`Madd`, `AddRI`, `LdrRI`/`StrRI` with `#0`/`#m*s`,
//! `CmpRR`, `BCond`, `B`, `Movz`/`Movk`) is ALREADY emitted by the scalar MAC
//! loop itself — no new emittable opcode, NO udiv/division, NO multiply beyond
//! the `madd` the scalar already carries. This adds no opcode-level proof-DB
//! entry; pass-level equivalence still relies on the guards/alias argument above
//! and the differential and regression tests.
//!
//! Default-ON at O2/O3 (never O0/O1). Compile-time kill switch:
//! `TCG_NO_MAC_ROW_UNROLL` (run() becomes a no-op). Per-pass bisect:
//! `TRUST_CG_DISABLE_PASSES=mac_row_unroll`.

use std::collections::{HashMap, HashSet};

use trust_cg_ir::{
    AArch64Opcode, BlockId, InstId, MachFunction, MachInst, MachOperand, RegClass, VReg,
};

use crate::dom::DomTree;
use crate::loops::LoopAnalysis;
use crate::pass_manager::{AnalysisCache, MachinePass};

#[cfg(test)]
mod tests;

/// AArch64 condition code for unsigned lower (`LO`) — the native forward
/// `iv < N` continue test (accepted alongside `LT`).
const CC_LO: i64 = 3;
/// AArch64 condition code for signed less-than (`LT`) — accepted alongside `LO`
/// as a native forward `iv < N` continue test.
const CC_LT: i64 = 11;
/// AArch64 condition code for unsigned higher-or-same (`HS`/`CS`) — the main
/// header's three guards bail on `idx >= bound`.
const CC_HS: i64 = 2;

/// Unroll factor. Four lanes per main-loop block.
const UNROLL: i64 = 4;

/// Compile-time kill switch: set `TCG_NO_MAC_ROW_UNROLL` (any value) to disable
/// the pass (run() is a no-op). Default ON at O2/O3.
fn mru_enabled() -> bool {
    std::env::var_os("TCG_NO_MAC_ROW_UNROLL").is_none()
}

// ---------------------------------------------------------------------------
// Pass
// ---------------------------------------------------------------------------

/// The `mac-row-unroll` machine pass.
#[derive(Default)]
pub struct MacRowUnroll {
    fired: usize,
}

impl MacRowUnroll {
    pub fn new() -> Self {
        Self { fired: 0 }
    }
    /// Loops partially unrolled in the last `run`.
    pub fn fired(&self) -> usize {
        self.fired
    }
}

impl MachinePass for MacRowUnroll {
    fn name(&self) -> &str {
        "mac-row-unroll"
    }

    fn run(&mut self, func: &mut MachFunction) -> bool {
        if !mru_enabled() {
            return false;
        }
        let dom = DomTree::compute(func);
        let loops = LoopAnalysis::compute(func, &dom);
        self.run_core(func, &dom, &loops)
    }

    fn run_with_analyses(&mut self, func: &mut MachFunction, analyses: &mut AnalysisCache) -> bool {
        if !mru_enabled() {
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

impl MacRowUnroll {
    fn run_core(&mut self, func: &mut MachFunction, dom: &DomTree, loops: &LoopAnalysis) -> bool {
        self.fired = 0;
        // Recognize first (read-only); applying a plan only ADDS blocks (never
        // renumbers ids or edits other loops), so recognized data for other
        // loops stays valid.
        let mut plans = Vec::new();
        let def_map = build_def_map(func);
        for lp in loops.all_loops() {
            // innermost only: no other loop's header lies inside this body.
            let is_innermost = loops
                .all_loops()
                .all(|other| other.header == lp.header || !lp.body.contains(&other.header));
            if !is_innermost {
                continue;
            }
            let Some(preheader) = lp.preheader else {
                // No unique preheader (e.g. an already-spliced main loop's
                // scalar remainder now has several guard predecessors) -> skip.
                // This is exactly what makes the pass idempotent.
                continue;
            };
            if let Some(rec) = Recognized::recognize(
                func, dom, &def_map, lp.header, lp.latch, &lp.body, preheader,
            ) {
                plans.push(rec);
            }
        }
        let mut changed = false;
        for rec in plans {
            if apply(func, &rec) {
                self.fired += 1;
                changed = true;
            }
        }
        if changed && std::env::var("TRUST_CG_DUMP_MRU").is_ok() {
            eprintln!("[mac-row-unroll] fn={} unrolled={}", func.name, self.fired);
        }
        changed
    }
}

// ---------------------------------------------------------------------------
// Recognition
// ---------------------------------------------------------------------------

struct Recognized {
    /// The scalar loop header (the redirect target on any guard failure and the
    /// `trip mod 4` remainder entry).
    header: BlockId,
    preheader: BlockId,
    preheader_term: InstId,
    /// The `Gpr64` induction `j`, unit-strided (`j += 1`).
    iv: VReg,
    /// The loop-invariant `Gpr64` register holding the compile-time bound `N`
    /// (reused verbatim in the replicated index `madd`s).
    n_reg: VReg,
    /// The compile-time value of `N` (from the header test), `4 <= N <= u32::MAX`.
    n_const: i64,
    /// The compile-time array length `L` (from the three bounds checks),
    /// `4 <= L <= u32::MAX`.
    l_const: i64,
    /// Loop-invariant `i` register (the `cidx = i*N+j` multiplier).
    i_reg: VReg,
    /// Loop-invariant `k` register (the `bidx = k*N+j` multiplier).
    k_reg: VReg,
    /// Loop-invariant `c` base pointer (the RMW array).
    c_base: VReg,
    /// Loop-invariant `b` base pointer (the read-only array).
    b_base: VReg,
    /// Loop-invariant `Gpr64` register holding the element scale (`8` for i64);
    /// reused verbatim as the address-`madd` multiplier.
    scale_reg: VReg,
    /// The element scale as a constant (`> 0`, `4*scale <= 4095`).
    scale_const: i64,
    /// Loop-invariant `aik` accumulate multiplier.
    aik: VReg,
}

impl Recognized {
    #[allow(clippy::too_many_lines)]
    fn recognize(
        func: &MachFunction,
        dom: &DomTree,
        def: &HashMap<u32, InstId>,
        header: BlockId,
        latch: BlockId,
        body: &HashSet<BlockId>,
        preheader: BlockId,
    ) -> Option<Self> {
        let dump = std::env::var("TRUST_CG_DUMP_MRU").is_ok();
        macro_rules! bail {
            ($($t:tt)*) => {{
                if dump {
                    eprintln!("[mac-row-unroll] bail@{}: {}", func.name, format!($($t)*));
                }
                return None;
            }};
        }
        if header == latch || body.len() < 2 {
            bail!("degenerate loop");
        }
        // `def` is supplied by the caller, built ONCE per recognition sweep.
        // Measured as ~99% of this pass's entire cost when it was rebuilt inside
        // every per-loop attempt.

        // (1) Closed-world opcode whitelist over the ENTIRE body. Anything
        // unmodeled (calls, atomics, division, multiply, other loads/stores,
        // wide arithmetic) is absent -> BAIL. Require EXACTLY one StrRI and two
        // LdrRI (the RMW `c` store, the `c` reload, and the `b` read).
        let mut loop_insts = HashSet::new();
        let mut stores: Vec<InstId> = Vec::new();
        let mut loads = 0usize;
        for &b in body {
            for &id in &func.block(b).insts {
                let op = func.inst(id).opcode;
                if !allowed_loop_op(op) {
                    bail!("disallowed body op {:?}", op);
                }
                match op {
                    AArch64Opcode::StrRI => stores.push(id),
                    AArch64Opcode::LdrRI => loads += 1,
                    _ => {}
                }
                loop_insts.insert(id);
            }
        }
        if stores.len() != 1 {
            bail!("expected exactly one StrRI, found {}", stores.len());
        }
        if loads != 2 {
            bail!("expected exactly two LdrRI, found {}", loads);
        }
        let store_id = stores[0];

        // (2) Header preds == exactly {preheader, latch}; single latch. The
        // caller already established a unique `preheader`; confirm the shape.
        let hpreds = &func.block(header).preds;
        if hpreds.len() != 2 || !hpreds.contains(&latch) || !hpreds.contains(&preheader) {
            bail!("header preds != {{latch, preheader}}: {:?}", hpreds);
        }
        let Some(&preheader_term) = func
            .block(preheader)
            .insts
            .iter()
            .rev()
            .find(|&&id| branch_targets(func.inst(id)).contains(&header))
        else {
            bail!("no preheader->header branch");
        };

        // (3) The unit induction `j` (from the latch): `j = MovR(next)` with
        // `next = AddRI(j, 1)`, or the in-place `j = AddRI(j, 1)`.
        let Some(iv) = find_unit_induction(func, &def, latch) else {
            bail!("no `j = j + 1` unit writeback in latch");
        };
        if iv.class != RegClass::Gpr64 {
            bail!("iv class not Gpr64 ({:?})", iv.class);
        }

        // (4) Work backwards from the single store. StrRI [value, addr, #0].
        let store = func.inst(store_id);
        if store.operands.len() != 3 || imm_of(&store.operands[2]) != Some(0) {
            bail!("store is not StrRI [val, addr, #0]");
        }
        let store_val = vreg_of(&store.operands[0])?;
        let store_addr = vreg_of(&store.operands[1])?;

        // store addr: caddr2 = Madd(cidx2, scale, c_base).
        let (cidx2, scale_r_s, cbase_s) = madd_addr(func, &def, store_addr)?;
        // cidx2 = Madd(i, N, j').
        let (i_r2, n_r2, jc_a) = madd_index(func, &def, cidx2)?;
        if !same_as(func, &def, jc_a, iv) {
            bail!("store index is not i*N + j");
        }

        // store value: mac = Madd(aik, bval, cval).
        let mac = func.inst(*def.get(&store_val.id)?);
        let (aik, bval, cval) = madd_parts_val(mac)?;

        // bval = LdrRI [_, baddr, #0]; baddr = Madd(bidx, scale, b_base);
        // bidx = Madd(k, N, j').
        let baddr = ldr_addr(func, &def, bval)?;
        let (bidx, scale_r_b, bbase) = madd_addr(func, &def, baddr)?;
        let (k_reg, n_r_b, jc_b) = madd_index(func, &def, bidx)?;
        if !same_as(func, &def, jc_b, iv) {
            bail!("b index is not k*N + j");
        }

        // cval = LdrRI [_, caddr, #0]; caddr = Madd(cidx, scale, c_base);
        // cidx = Madd(i, N, j').
        let caddr = ldr_addr(func, &def, cval)?;
        let (cidx, scale_r_c, cbase_c) = madd_addr(func, &def, caddr)?;
        let (i_reg, n_r_c, jc_c) = madd_index(func, &def, cidx)?;
        if !same_as(func, &def, jc_c, iv) {
            bail!("c index is not i*N + j");
        }

        // (5) Cross-consistency of the reused registers.
        if !same_as(func, &def, i_r2, i_reg) {
            bail!("store/load i mismatch");
        }
        if cbase_s != cbase_c {
            bail!("c_base mismatch between load and store addr");
        }
        let c_base = cbase_c;
        // scale must be one loop-invariant const register, identical for all 3
        // address madds.
        if scale_r_s != scale_r_c || scale_r_b != scale_r_c {
            bail!("scale register differs across address madds");
        }
        let scale_reg = scale_r_c;
        let Some(scale_const) = const_value(func, &def, scale_reg) else {
            bail!("scale is not a compile-time constant");
        };
        // Bound the scale so that BOTH the per-lane immediate offset
        // (`(UNROLL-1)*scale`) AND the per-block running-pointer advance
        // (`UNROLL*scale`) are encodable AddRI/load-store immediates.
        if scale_const <= 0 || scale_const.saturating_mul(UNROLL) > 4095 {
            bail!("scale {} out of AddRI-immediate range", scale_const);
        }
        // N must be one loop-invariant const register, identical for all 3 index
        // madds.
        if n_r2 != n_r_c || n_r_b != n_r_c {
            bail!("N register differs across index madds");
        }
        let n_reg = n_r_c;
        let Some(n_const) = const_value(func, &def, n_reg) else {
            bail!("N is not a compile-time constant");
        };
        if !(UNROLL..=i64::from(u32::MAX)).contains(&n_const) {
            bail!("N {} out of [4, u32::MAX]", n_const);
        }

        // (6) Loop-invariance of every reused operand register.
        for (name, v) in [
            ("i", i_reg),
            ("k", k_reg),
            ("c_base", c_base),
            ("b_base", bbase),
            ("aik", aik),
            ("N", n_reg),
            ("scale", scale_reg),
        ] {
            if v.class != RegClass::Gpr64 {
                bail!("{} not Gpr64 ({:?})", name, v.class);
            }
            if !is_loop_invariant(func, &def, dom, &loop_insts, preheader, v) {
                bail!("{} ({:?}) not loop-invariant", name, v);
            }
        }
        // The reused `n_reg` is compared in the index madds; confirm the header
        // uses the SAME native forward `iv < N` test with the SAME constant.
        let Some(hdr_n) = recognize_native_const_bound(func, &def, body, header, iv) else {
            bail!("no NATIVE forward iv<const-N continue test in header");
        };
        if hdr_n != n_const {
            bail!("header bound {} != index N {}", hdr_n, n_const);
        }

        // (7) The three bounds checks over cidx, bidx, cidx2 against ONE array
        // length L. Each is a `Cmp idx, L ; B.LO body ; B exit` guarding the
        // access; require all three present and identical.
        let l1 = find_bounds_check(func, &def, body, cidx)?;
        let l2 = find_bounds_check(func, &def, body, bidx)?;
        let l3 = find_bounds_check(func, &def, body, cidx2)?;
        if l1 != l2 || l2 != l3 {
            bail!("bounds L mismatch: {} {} {}", l1, l2, l3);
        }
        let l_const = l1;
        if !(UNROLL..=i64::from(u32::MAX)).contains(&l_const) {
            bail!("array length {} out of [4, u32::MAX]", l_const);
        }

        // (8) UNCONDITIONAL EXECUTION. The main block replaces FOUR scalar
        // iterations with STRAIGHT-LINE code, so the whole soundness argument
        // ("compute = 4 scalar iterations, bit-for-bit") silently assumes that
        // each scalar iteration (a) always performs the recognized MAC and
        // (b) never leaves the loop other than through a control transfer the
        // spliced guards already prove cannot be taken. Nothing above checks
        // either: steps (1)-(7) only constrain WHAT the recognized chain does
        // when it runs, never THAT it runs. Two shapes slip through and are
        // miscompiled:
        //
        //   * a PREDICATED MAC — `while j <u N { if p { c[..] += aik*b[..] } ;
        //     j += 1 }` — the store block does not dominate the latch, and the
        //     unrolled block performs all four MACs unconditionally, dropping
        //     `p`;
        //   * an EARLY EXIT — `while j <u N { if p { break } ; c[..] += .. }` —
        //     the unrolled block runs four iterations without ever evaluating
        //     `p`.
        //
        // Close both fail-closed:
        //   (a) the store's block DOMINATES the latch, so every iteration that
        //       completes performed the RMW store; and the three chain values
        //       feeding it (the two loads and the accumulate `Madd`) dominate
        //       that store, so the value stored is the recognized one on every
        //       path reaching it;
        //   (b) the ONLY loop-exiting blocks are the header (whose `j <u N`
        //       test the `j <u N-3` guard subsumes) and blocks that ARE one of
        //       the three recognized `idx <u L` bounds checks (whose fail edges
        //       the `cidx <u L-3` / `bidx <u L-3` guards prove untaken for all
        //       four lanes). An exiting block is admitted only if it has
        //       EXACTLY two successors — one in the body, one out — so it
        //       cannot smuggle a second, unmodeled exit alongside the check.
        //       Any other block with a successor outside the body BAILS.
        let Some(store_blk) = block_of_inst(func, store_id) else {
            bail!("store has no owning block");
        };
        if !dom.dominates(store_blk, latch) {
            bail!(
                "store block {:?} does not dominate latch {:?} (predicated MAC)",
                store_blk,
                latch
            );
        }
        for (name, v) in [("c load", cval), ("b load", bval), ("mac", store_val)] {
            let blk = def.get(&v.id).and_then(|&d| block_of_inst(func, d));
            if !blk.is_some_and(|b| dom.dominates(b, store_blk)) {
                bail!("{} ({:?}) does not dominate the store block", name, v);
            }
        }
        for &b in body {
            let succs = &func.block(b).succs;
            if !succs.iter().any(|s| !body.contains(s)) {
                continue; // not an exiting block
            }
            if succs.len() != 2 || succs.iter().filter(|s| body.contains(s)).count() != 1 {
                bail!("exiting block {:?} has an unmodeled successor set", b);
            }
            if b == header {
                continue; // the recognized `j <u N` continue test
            }
            let is_bc = [cidx, bidx, cidx2]
                .iter()
                .any(|&idx| bounds_check_in(func, def, body, b, idx) == Some(l_const));
            if !is_bc {
                bail!("unmodeled loop-exiting block {:?} (early exit)", b);
            }
        }

        if dump {
            eprintln!(
                "[mac-row-unroll] RECOGNIZED@{} iv={:?} N={} L={} i={:?} k={:?} c={:?} b={:?} \
                 scale={} aik={:?}",
                func.name, iv, n_const, l_const, i_reg, k_reg, c_base, bbase, scale_const, aik
            );
        }
        Some(Recognized {
            header,
            preheader,
            preheader_term,
            iv,
            n_reg,
            n_const,
            l_const,
            i_reg,
            k_reg,
            c_base,
            b_base: bbase,
            scale_reg,
            scale_const,
            aik,
        })
    }
}

/// A `Madd [dst, xn, xm, xa]` -> `(xn, xm, xa)` (value = `xa + xn*xm`).
fn madd_parts_val(inst: &MachInst) -> Option<(VReg, VReg, VReg)> {
    if inst.opcode == AArch64Opcode::Madd && inst.operands.len() == 4 {
        Some((
            vreg_of(&inst.operands[1])?,
            vreg_of(&inst.operands[2])?,
            vreg_of(&inst.operands[3])?,
        ))
    } else {
        None
    }
}

/// Resolve an address register produced by `addr = Madd(index, scale, base)`
/// (byte address = base + index*scale). Returns `(index, scale, base)`.
fn madd_addr(
    func: &MachFunction,
    def: &HashMap<u32, InstId>,
    addr: VReg,
) -> Option<(VReg, VReg, VReg)> {
    let &d = def.get(&addr.id)?;
    madd_parts_val(func.inst(d))
}

/// Resolve an index register produced by `idx = Madd(mul, n, j)`
/// (element index = mul*n + j). Returns `(mul, n, j)`.
fn madd_index(
    func: &MachFunction,
    def: &HashMap<u32, InstId>,
    idx: VReg,
) -> Option<(VReg, VReg, VReg)> {
    let &d = def.get(&idx.id)?;
    madd_parts_val(func.inst(d))
}

/// Resolve a loaded value `v = LdrRI [v, addr, #0]` to its `addr` register
/// (require the `#0` immediate offset — the scalar form).
fn ldr_addr(func: &MachFunction, def: &HashMap<u32, InstId>, v: VReg) -> Option<VReg> {
    let &d = def.get(&v.id)?;
    let inst = func.inst(d);
    if inst.opcode == AArch64Opcode::LdrRI
        && inst.operands.len() == 3
        && imm_of(&inst.operands[2]) == Some(0)
    {
        vreg_of(&inst.operands[1])
    } else {
        None
    }
}

/// Find the unit induction in the latch: `j = MovR/Copy(next)` with
/// `next = AddRI(j, 1)`, or the in-place `j = AddRI(j, 1)`.
fn find_unit_induction(
    func: &MachFunction,
    def: &HashMap<u32, InstId>,
    latch: BlockId,
) -> Option<VReg> {
    // Phi-copy form.
    for &id in &func.block(latch).insts {
        if let Some((d, s)) = copy_like(func.inst(id)) {
            if d.class != RegClass::Gpr64 {
                continue;
            }
            if let Some(&sdef) = def.get(&s.id) {
                let si = func.inst(sdef);
                if is_add1(si) && vreg_of(&si.operands[1]) == Some(d) {
                    return Some(d);
                }
            }
        }
    }
    // In-place form.
    for &id in &func.block(latch).insts {
        let inst = func.inst(id);
        if is_add1(inst) {
            let d = vreg_of(&inst.operands[0])?;
            if d.class == RegClass::Gpr64 && vreg_of(&inst.operands[1]) == Some(d) {
                return Some(d);
            }
        }
    }
    None
}

/// `AddRI [d, s, #1]`.
fn is_add1(inst: &MachInst) -> bool {
    inst.opcode == AArch64Opcode::AddRI
        && inst.operands.len() == 3
        && imm_of(&inst.operands[2]) == Some(1)
}

/// Find `Cmp idx, L ; B.LO/LT body ; B exit` in the body that bounds-checks
/// `idx` against a compile-time constant `L`, returning `L`. Requires the taken
/// (in-bounds) target to be in the loop body and the fall-through (fail) target
/// to leave the body (the abort/trap edge).
fn find_bounds_check(
    func: &MachFunction,
    def: &HashMap<u32, InstId>,
    body: &HashSet<BlockId>,
    idx: VReg,
) -> Option<i64> {
    body.iter()
        .find_map(|&b| bounds_check_in(func, def, body, b, idx))
}

/// Is block `b` a `Cmp idx, L ; B.LO/LT body ; B exit` bounds check on `idx`?
/// Returns the compile-time `L`. Split out of `find_bounds_check` so the
/// unconditional-execution gate can ask the same question of a SPECIFIC block
/// (order-independent — `body` is a `HashSet`).
fn bounds_check_in(
    func: &MachFunction,
    def: &HashMap<u32, InstId>,
    body: &HashSet<BlockId>,
    b: BlockId,
    idx: VReg,
) -> Option<i64> {
    // The compare on `idx`.
    let mut bound: Option<i64> = None;
    for &id in &func.block(b).insts {
        let inst = func.inst(id);
        match inst.opcode {
            AArch64Opcode::CmpRR if inst.operands.len() == 2 => {
                if same_as(func, def, vreg_of(&inst.operands[0])?, idx) {
                    bound = const_value(func, def, vreg_of(&inst.operands[1])?);
                }
            }
            AArch64Opcode::CmpRI
                if inst.operands.len() == 2
                    && same_as(func, def, vreg_of(&inst.operands[0])?, idx) =>
            {
                bound = imm_of(&inst.operands[1]);
            }
            _ => {}
        }
    }
    let l = bound?;
    // The block's conditional exit must be a forward in-bounds branch.
    let mut lo_to_body = false;
    let mut has_exit = false;
    for &id in &func.block(b).insts {
        let inst = func.inst(id);
        if inst.opcode == AArch64Opcode::BCond && inst.operands.len() == 2 {
            let cc = imm_of(&inst.operands[0])?;
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
    None
}

/// Recognize the NATIVE forward `iv < N` continue test with a COMPILE-TIME
/// CONSTANT bound in the `header`. Returns `N`. (Same discipline as
/// `strided_store_unroll`'s bound recognizer.)
fn recognize_native_const_bound(
    func: &MachFunction,
    def: &HashMap<u32, InstId>,
    body: &HashSet<BlockId>,
    header: BlockId,
    iv: VReg,
) -> Option<i64> {
    // The single `iv < bound` compare in the header (through copies).
    let mut cmp_bound: Option<i64> = None;
    for &id in &func.block(header).insts {
        let inst = func.inst(id);
        match inst.opcode {
            AArch64Opcode::CmpRR if inst.operands.len() == 2 => {
                if same_as(func, def, vreg_of(&inst.operands[0])?, iv) {
                    // Same guard, same reason as
                    // `strided_store_unroll::recognize_native_const_bound`:
                    // this recognizer is a copy of that one and had the same
                    // hole. A bound the loop reassigns resolves to its LATCH
                    // value. Not driven to a witness here — the pass fires on
                    // the shape but stays correct — so this is defensive.
                    let rhs = vreg_of(&inst.operands[1])?;
                    if crate::effects::live_def_count(func, rhs.id) == 1 {
                        cmp_bound = const_value(func, def, rhs);
                    }
                }
            }
            AArch64Opcode::CmpRI
                if inst.operands.len() == 2
                    && same_as(func, def, vreg_of(&inst.operands[0])?, iv) =>
            {
                cmp_bound = imm_of(&inst.operands[1]);
            }
            _ => {}
        }
    }
    let n = cmp_bound?;
    // A forward BCond LT/LO whose taken-target is a body block.
    let mut has_forward = false;
    for &id in &func.block(header).insts {
        let inst = func.inst(id);
        if inst.opcode == AArch64Opcode::BCond && inst.operands.len() == 2 {
            let cc = imm_of(&inst.operands[0])?;
            let tgt = *branch_targets(inst).first()?;
            if (cc == CC_LT || cc == CC_LO) && body.contains(&tgt) {
                has_forward = true;
            }
        }
    }
    if !has_forward {
        return None;
    }
    // The header must have a non-body successor (the real exit).
    func.block(header)
        .succs
        .iter()
        .find(|s| !body.contains(s))?;
    Some(n)
}

/// A register is loop-invariant iff it is NOT defined anywhere in the loop body
/// and its (unique last) def dominates the preheader. Fail-safe: anything else
/// returns `false`.
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

/// Opcodes permitted anywhere in the loop body. Loads/stores are limited to the
/// immediate-offset `LdrRI`/`StrRI` (register-offset, wide, atomic, and every
/// unmodeled effect BAIL — closed-world).
fn allowed_loop_op(op: AArch64Opcode) -> bool {
    use AArch64Opcode::*;
    matches!(
        op,
        Madd | AddRI | MovR | Copy | CmpRR | CmpRI | BCond | B | LdrRI | StrRI
    )
}

// ---------------------------------------------------------------------------
// Transformation (partial-unroll-in-front; additive, never edits the scalar loop)
// ---------------------------------------------------------------------------

fn apply(func: &mut MachFunction, rec: &Recognized) -> bool {
    let j = rec.iv;
    let scalar = rec.header;

    // Fresh blocks: g0 (materialize constants + initialize running indices), hdr
    // (`j` guard), gc (cidx guard), gb (bidx guard), mb (the 4x body + back-edge).
    // The main loop is `hdr -> gc -> gb -> mb -> hdr`; each guard bails to the
    // scalar remainder.
    let g0 = func.create_block();
    let hdr = func.create_block();
    let gc = func.create_block();
    let gb = func.create_block();
    let mb = func.create_block();
    insert_new_blocks_before(func, scalar, &[g0, hdr, gc, gb, mb]);

    // Internal edges (the preheader redirect is deferred to COMMIT so a failure
    // cannot break the CFG).
    func.add_edge(g0, hdr);
    func.add_edge(hdr, scalar);
    func.add_edge(hdr, gc);
    func.add_edge(gc, scalar);
    func.add_edge(gc, gb);
    func.add_edge(gb, scalar);
    func.add_edge(gb, mb);
    func.add_edge(mb, hdr);

    // --- g0: materialize the loop constants `N-3` and `L-3`, and INITIALIZE
    // the four running induction variables ONCE (address-SR + row-base LICM):
    //   cidx_iv = i*N + j   (the c index; carried, guarded, `+= UNROLL` / block)
    //   bidx_iv = k*N + j   (the b index; carried, guarded, `+= UNROLL` / block)
    //   pc      = c_base + cidx_iv*scale  (the running c byte pointer; `+=
    //             UNROLL*scale` / block)
    //   pb      = b_base + bidx_iv*scale  (the running b byte pointer)
    // These are computed from the CURRENT `j` at entry (the same values
    // iteration 1's chain would compute), so the transform is exact for any
    // entry `j` (the main loop is entered only from the preheader). Hoisting
    // the index/address recompute out of the per-block header and carrying it
    // additively removes the two per-block index `madd`s and the two per-block
    // address derivations from the loop body; the guards stay on the explicit
    // index IVs (NOT on the pointers), so bounds behavior is bit-identical and
    // needs no address-non-wrap assumption.
    let njm = materialize_in(func, g0, rec.n_const - (UNROLL - 1));
    let ljm = materialize_in(func, g0, rec.l_const - (UNROLL - 1));
    let cidx_iv = alloc(func, RegClass::Gpr64);
    emit(
        func,
        g0,
        AArch64Opcode::Madd,
        vec![vreg(cidx_iv), vreg(rec.i_reg), vreg(rec.n_reg), vreg(j)],
    );
    let bidx_iv = alloc(func, RegClass::Gpr64);
    emit(
        func,
        g0,
        AArch64Opcode::Madd,
        vec![vreg(bidx_iv), vreg(rec.k_reg), vreg(rec.n_reg), vreg(j)],
    );
    let pc = alloc(func, RegClass::Gpr64);
    emit(
        func,
        g0,
        AArch64Opcode::Madd,
        vec![
            vreg(pc),
            vreg(cidx_iv),
            vreg(rec.scale_reg),
            vreg(rec.c_base),
        ],
    );
    let pb = alloc(func, RegClass::Gpr64);
    emit(
        func,
        g0,
        AArch64Opcode::Madd,
        vec![
            vreg(pb),
            vreg(bidx_iv),
            vreg(rec.scale_reg),
            vreg(rec.b_base),
        ],
    );
    emit(func, g0, AArch64Opcode::B, vec![block(hdr)]);

    // --- hdr: guard `j <u N-3` (all four lanes are legitimate scalar
    // iterations). No per-block index/address recompute — the running IVs
    // carry them.
    emit(func, hdr, AArch64Opcode::CmpRR, vec![vreg(j), vreg(njm)]);
    emit(
        func,
        hdr,
        AArch64Opcode::BCond,
        vec![imm(CC_HS), block(scalar)],
    );
    emit(func, hdr, AArch64Opcode::B, vec![block(gc)]);

    // --- gc: guard `cidx_iv <u L-3` (the running c index).
    emit(
        func,
        gc,
        AArch64Opcode::CmpRR,
        vec![vreg(cidx_iv), vreg(ljm)],
    );
    emit(
        func,
        gc,
        AArch64Opcode::BCond,
        vec![imm(CC_HS), block(scalar)],
    );
    emit(func, gc, AArch64Opcode::B, vec![block(gb)]);

    // --- gb: guard `bidx_iv <u L-3` (the running b index).
    emit(
        func,
        gb,
        AArch64Opcode::CmpRR,
        vec![vreg(bidx_iv), vreg(ljm)],
    );
    emit(
        func,
        gb,
        AArch64Opcode::BCond,
        vec![imm(CC_HS), block(scalar)],
    );
    emit(func, gb, AArch64Opcode::B, vec![block(mb)]);

    // --- mb: four verbatim lanes at byte addresses pc/pb + m*scale, each
    // preserving the scalar per-lane memory order (ldr c ; ldr b ;
    // madd aik*b + c ; str c). Uses the immediate-offset addressing mode
    // directly (`LdrRI/StrRI [base, #m*scale]`); recognition keeps both these
    // offsets and the `4*scale` pointer step within the pass's immediate-offset
    // / late-legalization envelope. Then advance the four running IVs and the
    // shared iv IN-PLACE and branch back to hdr.
    for m in 0..UNROLL {
        let off = m * rec.scale_const;
        let cval = alloc(func, RegClass::Gpr64);
        emit(
            func,
            mb,
            AArch64Opcode::LdrRI,
            vec![vreg(cval), vreg(pc), imm(off)],
        );
        let bval = alloc(func, RegClass::Gpr64);
        emit(
            func,
            mb,
            AArch64Opcode::LdrRI,
            vec![vreg(bval), vreg(pb), imm(off)],
        );
        let macv = alloc(func, RegClass::Gpr64);
        emit(
            func,
            mb,
            AArch64Opcode::Madd,
            vec![vreg(macv), vreg(rec.aik), vreg(bval), vreg(cval)],
        );
        emit(
            func,
            mb,
            AArch64Opcode::StrRI,
            vec![vreg(macv), vreg(pc), imm(off)],
        );
    }
    // Advance the running byte pointers by UNROLL*scale, the running indices
    // and the shared iv by UNROLL — all IN-PLACE (every read above is
    // complete) — then branch back to the main header. `UNROLL*scale <= 4095`
    // (guarded at recognition) so the pointer advance is an AddRI immediate.
    let ptr_step = UNROLL * rec.scale_const;
    emit(
        func,
        mb,
        AArch64Opcode::AddRI,
        vec![vreg(pc), vreg(pc), imm(ptr_step)],
    );
    emit(
        func,
        mb,
        AArch64Opcode::AddRI,
        vec![vreg(pb), vreg(pb), imm(ptr_step)],
    );
    emit(
        func,
        mb,
        AArch64Opcode::AddRI,
        vec![vreg(cidx_iv), vreg(cidx_iv), imm(UNROLL)],
    );
    emit(
        func,
        mb,
        AArch64Opcode::AddRI,
        vec![vreg(bidx_iv), vreg(bidx_iv), imm(UNROLL)],
    );
    emit(
        func,
        mb,
        AArch64Opcode::AddRI,
        vec![vreg(j), vreg(j), imm(UNROLL)],
    );
    emit(func, mb, AArch64Opcode::B, vec![block(hdr)]);

    // --- COMMIT: splice the main loop in front of the scalar loop. Point of no
    // return; runs only after all emission succeeded.
    if !rewrite_block_target(func.inst_mut(rec.preheader_term), scalar, g0) {
        return false;
    }
    remove_cfg_edge(func, rec.preheader, scalar);
    func.add_edge(rec.preheader, g0);
    true
}

/// Materialize a `[0, u32::MAX]` constant into a fresh `Gpr64` via `Movz` +
/// `Movk` chunks, APPENDED to `blk`. Returns the register.
fn materialize_in(func: &mut MachFunction, blk: BlockId, value: i64) -> VReg {
    let d = alloc(func, RegClass::Gpr64);
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
    d
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
fn vreg_of(op: &MachOperand) -> Option<VReg> {
    match op {
        MachOperand::VReg(v) => Some(*v),
        _ => None,
    }
}
fn imm_of(op: &MachOperand) -> Option<i64> {
    match op {
        MachOperand::Imm(v) => Some(*v),
        _ => None,
    }
}

/// `MovR(d, s)` / `Copy(d, s)` / `AddRI(d, s, 0)` copy idioms -> `(d, s)`.
fn copy_like(inst: &MachInst) -> Option<(VReg, VReg)> {
    match inst.opcode {
        AArch64Opcode::MovR | AArch64Opcode::Copy if inst.operands.len() == 2 => {
            Some((vreg_of(&inst.operands[0])?, vreg_of(&inst.operands[1])?))
        }
        AArch64Opcode::AddRI
            if inst.operands.len() == 3 && imm_of(&inst.operands[2]) == Some(0) =>
        {
            Some((vreg_of(&inst.operands[0])?, vreg_of(&inst.operands[1])?))
        }
        _ => None,
    }
}

/// `v` equals `w` up through `MovR`/`Copy` chains.
fn same_as(func: &MachFunction, def: &HashMap<u32, InstId>, v: VReg, w: VReg) -> bool {
    strip_copies(func, def, v) == strip_copies(func, def, w)
}

/// Follow `MovR`/`Copy` chains to the underlying value.
fn strip_copies(func: &MachFunction, def: &HashMap<u32, InstId>, mut v: VReg) -> VReg {
    for _ in 0..16 {
        // A vreg with several live defs has no single reaching definition: the
        // def map is LAST-WINS over the emitted layout, so it names whichever
        // def comes last rather than the one that reaches this use. Every
        // loop-carried variable is multi-def by construction — the frontend
        // lowers a block parameter to one copy per predecessor, giving a
        // preheader copy and a latch copy into the same vreg — so walking one
        // resolves the INDUCTION VARIABLE to its latch source `iv + 1`. Then
        // `same_as(iv + 1, iv)` is TRUE and an index of `j + 1` passes as an
        // index of `j`, which is a wrong-address store.
        if crate::effects::live_def_count(func, v.id) != 1 {
            return v;
        }
        let Some(&d) = def.get(&v.id) else {
            return v;
        };
        match copy_like(func.inst(d)) {
            Some((dst, src)) if dst == v => v = src,
            _ => return v,
        }
    }
    v
}

/// 16-bit `Movz` constant, or a `Movz(lo16)`+`Movk(hi..)` chain, through copies.
fn const_value(func: &MachFunction, def: &HashMap<u32, InstId>, val: VReg) -> Option<i64> {
    let v = strip_copies(func, def, val);
    let id = *def.get(&v.id)?;
    let inst = func.inst(id);
    match inst.opcode {
        AArch64Opcode::Movz => move_wide_seed(inst, v),
        AArch64Opcode::Movk => {
            let blk = block_of_inst(func, id)?;
            let insts = &func.block(blk).insts;
            let pos = insts.iter().position(|&i| i == id)?;
            let mut acc: Option<i64> = None;
            for &pid in &insts[..=pos] {
                let pi = func.inst(pid);
                if !crate::effects::inst_defines_vreg(pi, v) {
                    continue;
                }
                match pi.opcode {
                    AArch64Opcode::Movz => acc = move_wide_seed(pi, v),
                    AArch64Opcode::Movk => {
                        let (halfword, shift) = move_wide_patch(pi, v)?;
                        let old = acc?;
                        let mask = 0xFFFF_i64 << shift;
                        acc = Some((old & !mask) | (halfword << shift));
                    }
                    _ => acc = None,
                }
            }
            acc
        }
        _ => None,
    }
}

fn move_wide_seed(inst: &MachInst, dst: VReg) -> Option<i64> {
    if !matches!(dst.class, RegClass::Gpr32 | RegClass::Gpr64) {
        return None;
    }
    if inst.opcode != AArch64Opcode::Movz
        || !(2..=3).contains(&inst.operands.len())
        || inst.operands.first().and_then(vreg_of) != Some(dst)
        || (inst.operands.len() == 3 && imm_of(&inst.operands[2]) != Some(0))
    {
        return None;
    }
    imm_of(&inst.operands[1]).filter(|imm| (0..=0xFFFF).contains(imm))
}

fn move_wide_patch(inst: &MachInst, dst: VReg) -> Option<(i64, u32)> {
    if !matches!(dst.class, RegClass::Gpr32 | RegClass::Gpr64) {
        return None;
    }
    if inst.opcode != AArch64Opcode::Movk
        || !(2..=3).contains(&inst.operands.len())
        || inst.operands.first().and_then(vreg_of) != Some(dst)
    {
        return None;
    }
    let halfword = imm_of(&inst.operands[1]).filter(|imm| (0..=0xFFFF).contains(imm))?;
    let shift = match inst.operands.get(2) {
        None => 0,
        Some(operand) => imm_of(operand)?,
    };
    let max_shift = if dst.class == RegClass::Gpr32 { 16 } else { 48 };
    if !matches!(shift, 0 | 16 | 32 | 48) || shift > max_shift {
        return None;
    }
    Some((halfword, shift as u32))
}

pub(crate) static MACROW_NANOS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
pub(crate) static MACROW_CALLS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

fn build_def_map(func: &MachFunction) -> HashMap<u32, InstId> {
    if crate::neon_array::boi_timing_enabled() {
        let t = std::time::Instant::now();
        let r = build_def_map_inner(func);
        MACROW_NANOS.fetch_add(
            t.elapsed().as_nanos() as u64,
            std::sync::atomic::Ordering::Relaxed,
        );
        MACROW_CALLS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        return r;
    }
    build_def_map_inner(func)
}

fn build_def_map_inner(func: &MachFunction) -> HashMap<u32, InstId> {
    crate::effects::build_reaching_def_map(func)
}

fn block_of_inst(func: &MachFunction, target: InstId) -> Option<BlockId> {
    for (idx, blk) in func.blocks.iter().enumerate() {
        if blk.insts.contains(&target) {
            return Some(BlockId(idx as u32));
        }
    }
    None
}

fn branch_targets(inst: &MachInst) -> Vec<BlockId> {
    inst.operands
        .iter()
        .filter_map(|o| match o {
            MachOperand::Block(b) => Some(*b),
            _ => None,
        })
        .collect()
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

fn alloc(func: &mut MachFunction, class: RegClass) -> VReg {
    let max_existing = func
        .insts
        .iter()
        .flat_map(|inst| inst.operands.iter())
        .filter_map(vreg_of)
        .map(|v| v.id)
        .max()
        .unwrap_or(0);
    let mut id = func.alloc_vreg();
    while id <= max_existing {
        id = func.alloc_vreg();
    }
    VReg::new(id, class)
}
