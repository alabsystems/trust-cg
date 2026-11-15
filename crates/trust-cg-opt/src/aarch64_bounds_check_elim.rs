// trust-cg-opt - AArch64 dominated-unsigned-guard bounds-check elimination
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! AArch64 machine-level elimination of a still-live `TrapBoundsCheckExact`
//! proof carrier that a *dominating loop-header unsigned guard* already proves
//! can never trap — the AArch64 port of the x86 carrier arm
//! ([`crate::x86_bounds_check_elim`]).
//!
//! # The shape this eliminates
//!
//! Bounds checks travel the whole pass pipeline as opaque, single-instruction
//! `TrapBoundsCheckExact [base, index, Imm(K)]` proof carriers; they are only
//! expanded into a real `cmp; b.lo; brk` diamond AFTER every trust-cg-opt pass
//! has run (`trust-cg-codegen`'s `expand_trap_bounds_check_exact`). For a
//! counted loop over a slice's own length (`for i in 0..N { .. a[i] .. }`) the
//! selector emits, per iteration:
//!
//! ```text
//!   header (guard):   cmp iv, N ; b.lo body ; b exit
//!   body   (carrier): ... ; TrapBoundsCheckExact [_, iv', Imm(N)] ; ...
//! ```
//!
//! where `iv'` is a value-preserving copy of the loop induction variable `iv`
//! and the header bound `N` equals (or is tighter than) the carrier bound `K`.
//! The guard's taken edge (`b.lo body`) establishes `iv <u N` on the ONLY path
//! into `body`, so the carrier's trap is provably dead. LLVM elides this; this
//! pass makes trust-cg match it by DELETING the carrier (a single instruction
//! removal — the carrier never encodes, so no CFG surgery, no trap block, and
//! no block renumbering is involved).
//!
//! # Why this is memory-safe (sound by construction, fail-safe by default)
//!
//! This pass is SAFETY-CRITICAL: removing a bounds check that is actually
//! needed is a silent out-of-bounds access (memory unsafety), strictly worse
//! than a wrong value. A carrier at position `p` of block `C` testing
//! `index <u K` is deleted ONLY when ALL of the following hold; ANY unproven
//! condition KEEPS the carrier (there is no wildcard/optimistic arm):
//!
//! 1. **Index canonicalization.** `index` follows single-def, SAME-CLASS
//!    `Gpr64` value-preserving copy links (`MovR`/`Copy`/`MOVXrr`) to a root
//!    `r` (first multi-def vreg / param / non-copy def), depth-bounded.
//!    Truncating/extending moves (`MOVWrr`/`Uxtw`/`Uxtb`) are NOT followed.
//! 2. **Dominating unsigned guard.** Some strict dominator `D` of `C` ends in
//!    `Cmp(op0, K') ; BCond cc [; B]` where `canon(op0) == r`, `op0` is `Gpr64`,
//!    the compare immediately precedes the branch (so the branch reads exactly
//!    that compare's flags), and `cc` is an UNSIGNED bound (`LO`/`HS`/`LS`/`HI`).
//! 3. **Bound value + implication.** `K'` is the compare immediate, or the
//!    constant of a single-def 2-operand `Movz [rhs, Imm(K')]` (`Gpr64`; any
//!    shifted/`Movk`-completed constant is unresolved -> keep), with
//!    `0 <= K' <= i32::MAX`. `cc` picks the guarded successor `T` and its
//!    strictness (`LO`: taken, strict; `HS`: fall-through, strict; `LS`: taken,
//!    non-strict; `HI`: fall-through, non-strict), and the bound must imply the
//!    carrier's: `K' <= K` (strict) or `K' < K` (non-strict).
//! 4. **Edge-dominance.** `T`'s ONLY predecessor is `D`, and `T` dominates `C`
//!    — so every path reaching the carrier traverses the guarded `D->T` edge.
//! 5. **No-redefinition of `r`.** `r` has NO def in the guarded region — the
//!    blocks forward-reachable from `T` avoiding `D`, intersected with the
//!    blocks backward-reachable from `C` avoiding `D` (with `C` sliced at `p`)
//!    — NOR in `D` at/after the guard anchor. Paths that leave through `D` (the
//!    loop latch re-entering the header) re-establish the predicate before
//!    re-reaching `T`, which is exactly why avoiding-`D` regions are the sound
//!    scan set.
//!
//! **Width discipline (soundness-critical):** `r`, `index`, `op0`, and the
//! bound register are ALL `Gpr64`; a 32-bit (`Gpr32`/`CMPWrr`) guard fact
//! constrains only the low 32 bits and must NOT prove a 64-bit bound — decline
//! otherwise. This is enforced by (a) only following full-width `Gpr64` copies,
//! (b) only matching `CmpRR`/`CmpRI` whose `op0` is `Gpr64` (the `sf` bit is
//! operand-class-derived), and (c) requiring the bound register `Gpr64`.
//!
//! # The NARROW-INDEX arm (mask / byte-range) — additive, guard-independent
//!
//! A SECOND, independent arm (`narrow_index_proven_below`) deletes a carrier
//! whose index `idx <u K` follows NOT from a dominating guard but from the
//! STRUCTURE of `idx`'s own single definition — the base64/crc32 table, RC4
//! S-box, and byte-histogram (`h[a[i] as usize]`) access patterns, which have a
//! constant array length but neither a constant index nor a dominating compare:
//!
//!   * `idx` canonicalizes (through the guard arm's `Gpr64` copy chain) to a
//!     root whose def is `Uxtb` (value in `[0,255]`; delete iff `K >= 256`) or
//!     `Uxth` (`[0,65535]`; `K >= 65536`) — a byte/half zero-extension is itself
//!     the value bound.
//!   * or the root's def is `AndRI [_, _, Imm(m)]` (or `Uxtw` of a `Gpr32`
//!     `AndRI`) with a non-negative constant mask `m < K`: `x & m <= m < K`.
//!
//! The root is SINGLE-def, so its value is globally fixed by that def and the
//! def dominates the carrier — the bound holds AT the carrier with NO
//! guarded-region scan. Unlike the guard arm this arm DELIBERATELY follows the
//! byte/half zero-extension (`Uxtb`/`Uxth`/`Uxtw`): the extended 64-bit value
//! EQUALS the narrow value, so there is no 32-vs-64-bit unsoundness. Every
//! unrecognized def shape / non-constant mask / `m >= K` keeps the carrier.
//!
//! # The REGISTER-BOUND trap-branch arm — explicit checks against a length
//!
//! A bounds check against a run-time length (`v[k]` on a `Vec` or slice) is
//! not a carrier: the selector emits it as an explicit two-way terminator
//!
//! ```text
//!   C:  ... ; Cmp(idx, len) ; BCond HS, fail ; B cont     (or LO cont ; B fail)
//!   fail: Brk                                   (a backend checked-trap guard)
//!   fail: <args> ; Bl panic_bounds_check ; Brk  (a source bounds check's raise)
//! ```
//!
//! and for `while k < v.len() { .. v[k] .. }` the loop header already tests the
//! same `k <u len`. This arm (`find_trap_branch_folds`) folds such a check to
//! `B cont` when a strict dominator `D` ends in a strict unsigned guard
//! `Cmp(idx', len') ; BCond` whose `<` edge enters `T`, `T`'s only predecessor
//! is `D`, `T` dominates `C`, `idx`/`idx'` share a copy root, `len`/`len'` share
//! a copy root or are two equal plain loads (same block, same base and offset,
//! nothing between them writes memory or the base), every copy link is a
//! snapshot inside the guarded window, and no root is redefined in the guarded
//! region (conditions 1, 2, 4 and 5 above, applied to both operands). Only a
//! DIVERGING failing successor (no successors, last instruction `Brk`:
//! `is_diverging_sink`) is folded — a bare trap or a panic raise alike, since
//! the guard proves the failing edge is never taken whatever it would run —
//! proof-annotated compares and branches are left to the proof path,
//! and a function with a volatile access keeps its checks: the volatile-trace
//! preservation check assumes every source edge takeable and would refuse the
//! compile. The fold unlinks the `BCond`, retargets the trailing `B` and drops
//! the edge into the failing block; the compare stays until DCE finds its flags
//! dead. A non-strict guard (`LS`/`HI`) proves only `idx <=u len` and never
//! folds. Per-arm bisect key: `TRUST_CG_DISABLE_PASSES=bcetrapbranch`.
//!
//! The same explicit check against a CONSTANT bound (`CmpRI idx, #K`, or a
//! single-def two-operand `Movz K` register) also folds when the NARROW-INDEX
//! arm's structural proof holds for `idx` (`narrow_index_proven_below`: a
//! byte/half zero-extension or a constant mask below `K`) — the `h[b as usize]`
//! byte-histogram shape whose check is no longer a carrier once its failing
//! edge raises `panic_bounds_check`. No guard is involved; the index's single
//! definition is the proof, exactly as for a carrier.
//!
//! And it folds when the CARRIER arm's guard rule (conditions 1-5 above,
//! `constant_guard_proves_below`) holds for `idx` against the check's constant
//! `K`: a strict dominator's unsigned guard on the same index root against a
//! constant `K'` with `K' <= K` (strict) or `K' < K` (non-strict). That is
//! `while i < N { .. a[i] .. }` over an array of `N` elements, the own-length
//! loop the carrier arm was written for: its check was a carrier until the
//! failing edge began to raise, and then nothing deleted it, so every AArch64
//! NEON pass that admits only a bounds-check-free (or carrier) body declined
//! the loop (`count_only`, `fill_only`, `bsum_only`, `isum_only` and
//! `p7_sieve` in the bridge's `opt_loop_state_run`). The proof obligations are
//! the carrier arm's, unchanged; only the shape of the check differs.
//!
//! # Why a standalone delete is accepted by every gate
//!
//! `TrapBoundsCheckExact` is a pseudo that never encodes; deleting it means its
//! `cmp/b.lo/brk` expansion never happens => strictly FEWER emitted opcodes =>
//! the per-compile emitted-opcode coverage gate (which fails closed only on an
//! emitted opcode with no proof query) cannot newly fail, so the gated compile
//! still promotes. `guard_ledger` reconcile() marks an absent-post-opt carrier
//! `eliminated` and conservation still balances. The `ProofOptimization` S4
//! kernel gate is untouched — this pass never fabricates proof evidence.
//!
//! Kill switch: `TCG_NO_AARCH64_BCE` (any value) disables the pass (run() is a
//! no-op). Default ON at O2/O3, mirroring x86's `TCG_NO_X86_BCE`. Per-pass
//! bisect key: `TRUST_CG_DISABLE_PASSES=aarch64bce` (drops the registration).

use crate::fast_hash::{FxHashMap as HashMap, FxHashSet as HashSet};
use std::collections::VecDeque;

use trust_cg_ir::{
    AArch64Opcode, BlockId, CondCode, InstId, MachFunction, MachInst, MachOperand, RegClass, VReg,
};

use crate::dom::DomTree;
use crate::effects::{for_each_inst_def, inst_defines_vreg, opcode_effect};
use crate::pass_manager::{AnalysisCache, MachinePass};

/// Kill switch: set `TCG_NO_AARCH64_BCE` (any value) to disable the pass.
/// Default ON at O2/O3 (mirrors x86's `TCG_NO_X86_BCE`).
fn bce_enabled() -> bool {
    std::env::var_os("TCG_NO_AARCH64_BCE").is_none()
}

/// Maximum index/guard copy-chain depth followed before failing safe.
const MAX_CHAIN_DEPTH: usize = 8;
/// Maximum dominator hops walked before failing safe.
const MAX_DOM_HOPS: usize = 64;
/// Inclusive upper bound on a resolvable carrier/guard immediate. Keeping
/// immediates in `[0, i32::MAX]` makes signed/unsigned/64-vs-32-bit comparison
/// of `K'` against `K` coincide, so the implication `K' <= K` is unambiguous.
const MAX_IMM: i64 = i32::MAX as i64;

/// AArch64 dominated-unsigned-guard bounds-check elimination pass.
pub struct AArch64BoundsCheckElimination {
    /// Number of carriers eliminated by the most recent [`run`] invocation
    /// (diagnostics / tests only).
    ///
    /// [`run`]: MachinePass::run
    pub last_run_eliminations: usize,
    /// Number of explicit register-bound checks the most recent [`run`] folded
    /// (diagnostics / tests only).
    ///
    /// [`run`]: MachinePass::run
    pub last_run_trap_branch_folds: usize,
    /// Whether the register-bound trap-branch arm runs (default on).
    trap_branch_folds: bool,
}

impl Default for AArch64BoundsCheckElimination {
    fn default() -> Self {
        Self::new()
    }
}

impl AArch64BoundsCheckElimination {
    /// Create the pass.
    pub fn new() -> Self {
        Self {
            last_run_eliminations: 0,
            last_run_trap_branch_folds: 0,
            trap_branch_folds: true,
        }
    }

    /// The pass without the register-bound trap-branch arm (carrier arms only).
    pub fn without_trap_branch_folds(mut self) -> Self {
        self.trap_branch_folds = false;
        self
    }

    /// Run the pass directly on a function (tests / standalone use).
    pub fn run_on_function(&mut self, func: &mut MachFunction) -> bool {
        self.run_on_function_enabled(func, bce_enabled())
    }

    /// Direct runner with an explicit enable decision. Keeping the decision as
    /// an argument lets the kill-switch unit test exercise the disabled path
    /// without mutating process-wide environment state while other tests run.
    fn run_on_function_enabled(&mut self, func: &mut MachFunction, enabled: bool) -> bool {
        self.last_run_eliminations = 0;
        self.last_run_trap_branch_folds = 0;
        if !enabled {
            return false;
        }
        let dom = DomTree::compute(func);
        self.run_core(func, &dom)
    }

    /// Core: recognize every provably-redundant carrier and every foldable
    /// explicit check against the ORIGINAL, unmutated function, then apply them.
    /// A carrier deletion removes only the carrier `InstId` from its block's
    /// instruction list; the `MachInst` stays inert in the arena (unreferenced,
    /// never encoded). A trap-branch fold changes one terminator and removes
    /// one CFG edge into a successor-less diverging block. Each recognized fact
    /// holds in the original program, and neither kind of edit removes an edge
    /// a later fact's guard relies on reaching its target through (a fold only
    /// removes edges into blocks with no successors, which guard nothing).
    fn run_core(&mut self, func: &mut MachFunction, dom: &DomTree) -> bool {
        let sites = find_carrier_eliminations(func, dom);
        let folds = if self.trap_branch_folds {
            find_trap_branch_folds(func, dom)
        } else {
            Vec::new()
        };
        if sites.is_empty() && folds.is_empty() {
            return false;
        }
        // Group carrier InstIds by block, then unlink them (retain != id).
        let mut by_block: HashMap<BlockId, HashSet<InstId>> = HashMap::default();
        for &(b, id) in &sites {
            by_block.entry(b).or_default().insert(id);
        }
        for (b, ids) in by_block {
            func.block_mut(b).insts.retain(|iid| !ids.contains(iid));
        }
        for &fold in &folds {
            apply_trap_branch_fold(func, fold);
        }
        self.last_run_eliminations = sites.len();
        self.last_run_trap_branch_folds = folds.len();
        true
    }
}

impl MachinePass for AArch64BoundsCheckElimination {
    fn name(&self) -> &str {
        "aarch64-bounds-check-elim"
    }

    fn run(&mut self, func: &mut MachFunction) -> bool {
        self.run_on_function_enabled(func, bce_enabled())
    }

    fn run_with_analyses(&mut self, func: &mut MachFunction, analyses: &mut AnalysisCache) -> bool {
        self.last_run_eliminations = 0;
        self.last_run_trap_branch_folds = 0;
        if !bce_enabled() {
            return false;
        }
        let changed = {
            let dom = analyses.domtree(func);
            self.run_core(func, dom)
        };
        // A carrier delete changes no CFG edge, but a trap-branch fold removes
        // one, so cached dominator/loop analyses must be recomputed.
        if changed {
            analyses.invalidate();
        }
        changed
    }
}

// ===========================================================================
// Recognizer
// ===========================================================================

/// Build the single-def index (vregs with EXACTLY one definition in the
/// function), keyed to the def's `(block, position-in-block)`. A hit means
/// "this vreg has a unique, globally-fixed value".
fn build_single_def_index(func: &MachFunction) -> HashMap<VReg, (BlockId, usize)> {
    let mut counts: HashMap<VReg, u32> = HashMap::default();
    let mut single: HashMap<VReg, (BlockId, usize)> = HashMap::default();
    for &b in &func.block_order {
        for (pos, &iid) in func.block(b).insts.iter().enumerate() {
            for_each_inst_def(func.inst(iid), |v| {
                *counts.entry(v).or_insert(0) += 1;
                single.insert(v, (b, pos));
            });
        }
    }
    single.retain(|v, _| counts.get(v) == Some(&1));
    single
}

/// The instruction at `(block, position)`, if it exists.
fn inst_at(func: &MachFunction, b: BlockId, pos: usize) -> Option<&MachInst> {
    let iid = func.block(b).insts.get(pos).copied()?;
    Some(func.inst(iid))
}

/// Follow single-def, SAME-CLASS `Gpr64` value-preserving copy links from `v`
/// to a canonical root vreg, recording each link's `(block, position)` def
/// site. The root is the first multi-def vreg, parameter, or non-copy def.
///
/// Width discipline: only `MovR`/`Copy`/`MOVXrr` (full-width `Gpr64`) copies
/// whose SOURCE is `Gpr64` are followed — `MOVWrr`/`Uxtw`/`Uxtb` truncate or
/// zero-extend, and the carrier's post-expansion compare is full-width, so a
/// truncating link would let a 32-bit fact "prove" a 64-bit bound. Returns
/// `None` (fail-safe) on a malformed copy or an over-deep chain.
fn chain_root(
    single_def: &HashMap<VReg, (BlockId, usize)>,
    func: &MachFunction,
    v: VReg,
) -> Option<(VReg, Vec<(BlockId, usize)>)> {
    let mut links: Vec<(BlockId, usize)> = Vec::new();
    let mut cur = v;
    for _ in 0..MAX_CHAIN_DEPTH {
        match single_def.get(&cur) {
            // Multi-def (or never-defined param) vreg: it is the root.
            None => return Some((cur, links)),
            Some(&(b, pos)) => {
                let inst = inst_at(func, b, pos)?;
                match inst.opcode {
                    AArch64Opcode::MovR | AArch64Opcode::Copy | AArch64Opcode::MOVXrr => {
                        match inst.operands.get(1) {
                            Some(MachOperand::VReg(s)) => {
                                // src AND dst must be Gpr64 (dst `cur` already
                                // is, being reached only through Gpr64 links or
                                // the Gpr64-checked entry).
                                if s.class != RegClass::Gpr64 || cur.class != RegClass::Gpr64 {
                                    return None;
                                }
                                links.push((b, pos));
                                cur = *s;
                            }
                            _ => return None,
                        }
                    }
                    // Non-copy (or truncating copy) def: the root.
                    _ => return Some((cur, links)),
                }
            }
        }
    }
    None // chain too deep — fail safe
}

/// The right-hand operand of a guard compare: another register, or an immediate.
#[derive(Clone, Copy)]
enum CmpRhs {
    Reg(VReg),
    Imm(i64),
}

/// A decoded dominating guard: `D`'s terminator decides `op0 <cc> rhs`, with the
/// `cc`-true edge going to `taken`. `cmp_pos` is the position of the bound
/// compare in `D` (the no-redefinition anchor).
struct GuardBranch {
    cmp_pos: usize,
    op0: VReg,
    rhs: CmpRhs,
    cc: CondCode,
    taken: BlockId,
    /// The successor the branch falls through to: `D`'s other successor.
    not_taken: BlockId,
}

/// Decode an AArch64 condition-code encoding (0..=15) to a [`CondCode`].
fn decode_cond(enc: i64) -> Option<CondCode> {
    if !(0..=15).contains(&enc) {
        return None;
    }
    // SAFETY-free: exhaustive match rather than transmute.
    Some(match enc as u8 {
        0b0000 => CondCode::EQ,
        0b0001 => CondCode::NE,
        0b0010 => CondCode::HS,
        0b0011 => CondCode::LO,
        0b0100 => CondCode::MI,
        0b0101 => CondCode::PL,
        0b0110 => CondCode::VS,
        0b0111 => CondCode::VC,
        0b1000 => CondCode::HI,
        0b1001 => CondCode::LS,
        0b1010 => CondCode::GE,
        0b1011 => CondCode::LT,
        0b1100 => CondCode::GT,
        0b1101 => CondCode::LE,
        0b1110 => CondCode::AL,
        _ => CondCode::NV,
    })
}

/// Parse `D`'s terminator as `Cmp(op0, rhs) ; BCond cc taken [; B other]`.
///
/// The `BCond` is the last instruction, or the second-to-last when an explicit
/// `B` fall-through follows it. The bound compare (`CmpRR`/`CmpRI`) must
/// IMMEDIATELY precede the `BCond` — so the branch reads exactly that compare's
/// NZCV, with no intervening flag-writer. Only `Gpr64` `op0` (the `sf` bit is
/// operand-class-derived) is accepted; a 32-bit compare fails the decode.
/// `D` must have exactly two distinct successors, `taken` and `not_taken`, and
/// a trailing `B` must target `not_taken`: a guard edge read off any other CFG
/// shape could name the wrong block as the bounded one.
/// Returns `None` (fail-safe) for anything else.
fn parse_guard_branch(func: &MachFunction, d: BlockId) -> Option<GuardBranch> {
    let insts = &func.block(d).insts;
    let n = insts.len();
    if n < 2 {
        return None;
    }
    // Locate the terminating BCond (bare, or with a trailing unconditional B).
    let last = func.inst(insts[n - 1]).opcode;
    let bcond_pos = if last == AArch64Opcode::BCond {
        n - 1
    } else if last == AArch64Opcode::B && func.inst(insts[n - 2]).opcode == AArch64Opcode::BCond {
        n - 2
    } else {
        return None;
    };
    if bcond_pos == 0 {
        return None;
    }
    let cmp_pos = bcond_pos - 1;

    let cmp = func.inst(insts[cmp_pos]);
    let (op0, rhs) = match cmp.opcode {
        AArch64Opcode::CmpRR => match cmp.operands.as_slice() {
            [MachOperand::VReg(a), MachOperand::VReg(b)] => (*a, CmpRhs::Reg(*b)),
            _ => return None,
        },
        AArch64Opcode::CmpRI => match cmp.operands.as_slice() {
            [MachOperand::VReg(a), MachOperand::Imm(imm)] => (*a, CmpRhs::Imm(*imm)),
            _ => return None,
        },
        // Deliberately NOT matching CMPWrr/CMPXrr/CMPWri/CMPXri: the width
        // discipline requires a proven-full-width guard, gated by op0==Gpr64.
        _ => return None,
    };
    if op0.class != RegClass::Gpr64 {
        return None;
    }

    let bcond = func.inst(insts[bcond_pos]);
    let (cc_enc, taken) = match bcond.operands.as_slice() {
        [MachOperand::Imm(enc), MachOperand::Block(t)] => (*enc, *t),
        _ => return None,
    };
    let cc = decode_cond(cc_enc)?;

    let not_taken = match func.block(d).succs.as_slice() {
        [a, b] if *a == taken && *b != taken => *b,
        [a, b] if *b == taken && *a != taken => *a,
        _ => return None,
    };
    if bcond_pos == n - 2 {
        match func.inst(insts[n - 1]).operands.as_slice() {
            [MachOperand::Block(f)] if *f == not_taken => {}
            _ => return None,
        }
    }

    Some(GuardBranch {
        cmp_pos,
        op0,
        rhs,
        cc,
        taken,
        not_taken,
    })
}

/// True iff `root` is defined anywhere in the avoiding-`D` guarded region
/// between the guarded edge target `t` and the carrier at `(c_blk, p)`, or
/// inside `D` at/after `d_from` (the guard compare or a guard-side copy link).
fn region_redefines_root(
    func: &MachFunction,
    t: BlockId,
    c_blk: BlockId,
    p: usize,
    d: BlockId,
    d_from: usize,
    root: VReg,
) -> bool {
    // Forward reachability from `t`, never entering `d`.
    let mut fwd: HashSet<BlockId> = HashSet::default();
    let mut work: VecDeque<BlockId> = VecDeque::new();
    fwd.insert(t);
    work.push_back(t);
    while let Some(b) = work.pop_front() {
        for &s in &func.block(b).succs {
            if s != d && fwd.insert(s) {
                work.push_back(s);
            }
        }
    }
    // Backward reachability from `c_blk`, never entering `d`.
    let mut bwd: HashSet<BlockId> = HashSet::default();
    work.clear();
    bwd.insert(c_blk);
    work.push_back(c_blk);
    while let Some(b) = work.pop_front() {
        for &pr in &func.block(b).preds {
            if pr != d && bwd.insert(pr) {
                work.push_back(pr);
            }
        }
    }
    // `C` is sliced at `p` only when control cannot come back to `C` without
    // passing `D`: on a cycle through `C` that avoids `D` (an inner loop inside
    // the guarded region), a def after `p` runs between the guard and a later
    // execution of the check.
    let c_reentered = func
        .block(c_blk)
        .succs
        .iter()
        .any(|&s| s != d && reaches_avoiding(func, s, c_blk, d));
    // Scan the intersection for defs of `root` (slice `c_blk` at `p`).
    for &b in fwd.intersection(&bwd) {
        for (i, &iid) in func.block(b).insts.iter().enumerate() {
            if b == c_blk && i >= p && !c_reentered {
                break;
            }
            if inst_defines_vreg(func.inst(iid), root) {
                return true;
            }
        }
    }
    // Defs of `root` inside `D` at/after the guard-side anchor.
    for &iid in func.block(d).insts.iter().skip(d_from) {
        if inst_defines_vreg(func.inst(iid), root) {
            return true;
        }
    }
    false
}

/// Whether `to` is reachable from `from` (inclusive) without entering `avoid`.
fn reaches_avoiding(func: &MachFunction, from: BlockId, to: BlockId, avoid: BlockId) -> bool {
    if from == avoid {
        return false;
    }
    let mut seen: HashSet<BlockId> = HashSet::default();
    let mut work: VecDeque<BlockId> = VecDeque::new();
    seen.insert(from);
    work.push_back(from);
    while let Some(b) = work.pop_front() {
        if b == to {
            return true;
        }
        for &s in &func.block(b).succs {
            if s != avoid && seen.insert(s) {
                work.push_back(s);
            }
        }
    }
    false
}

/// A constant `AndRI [dst, src, Imm(m)]` mask that is non-negative and strictly
/// below `k` — so `dst = src & m` has an unsigned value in `[0, m]`, hence `< k`.
/// A negative or `>= k` mask (or a non-immediate operand) is unproven. Only the
/// three-operand form carries a mask: the encoder also accepts a pre-decomposed
/// `AndRI [dst, src, N, immr, imms]`, whose operand 2 is the `N` bit (0 or 1),
/// and reading that as a mask would "prove" any bound `k >= 2`.
fn and_ri_mask_below(inst: &MachInst, k: i64) -> bool {
    matches!(
        inst.operands.as_slice(),
        [MachOperand::VReg(_), MachOperand::VReg(_), MachOperand::Imm(m)] if *m >= 0 && *m < k
    )
}

/// Follow single-def, SAME-CLASS `Gpr32` value-preserving copies from `v` to a
/// root whose definition STRUCTURALLY bounds its 32-bit value below `k`:
/// a constant mask (`AndRI`, `m < k`) or a byte/half zero-extension
/// (`Uxtb`->[0,255] with `k >= 256`; `Uxth`->[0,65535] with `k >= 65536`). Any
/// other def shape, a non-`Gpr32` copy source, or an over-deep chain is unproven
/// (fail-closed).
fn gpr32_value_proven_below(
    single_def: &HashMap<VReg, (BlockId, usize)>,
    func: &MachFunction,
    v: VReg,
    k: i64,
) -> bool {
    let mut cur = v;
    for _ in 0..MAX_CHAIN_DEPTH {
        let Some(&(b, pos)) = single_def.get(&cur) else {
            return false;
        };
        let Some(inst) = inst_at(func, b, pos) else {
            return false;
        };
        match inst.opcode {
            AArch64Opcode::MovR | AArch64Opcode::Copy => match inst.operands.get(1) {
                Some(MachOperand::VReg(s)) if s.class == RegClass::Gpr32 => cur = *s,
                _ => return false,
            },
            AArch64Opcode::AndRI => return and_ri_mask_below(inst, k),
            AArch64Opcode::Uxtb => return k >= 256,
            AArch64Opcode::Uxth => return k >= 65536,
            _ => return false,
        }
    }
    false
}

/// NARROW-INDEX soundness: is the carrier index `idx` PROVABLY `< k` (unsigned)
/// from its own single definition alone — independent of any dominating guard?
///
/// `idx` (Gpr64) is canonicalized through the SAME `Gpr64` value-preserving copy
/// chain as the guard arm (`chain_root`), then the root's single def must be one
/// of the value-bounding shapes:
///
///   * `Uxtb` — `[0, 255]`; in bounds iff `k >= 256`.
///   * `Uxth` — `[0, 65535]`; in bounds iff `k >= 65536`.
///   * `Uxtw src` — zero-extends the 32-bit `src`, so in bounds iff `src`'s
///     32-bit value is proven `< k` (a mask, or a nested byte/half extension).
///   * `AndRI [_, _, Imm(m)]` — `[0, m]`; in bounds iff `m < k`.
///
/// The root is SINGLE-def (its value is globally fixed by that def) and its def
/// dominates the carrier (single def dominates all uses in the pre-regalloc
/// machine IR), so the bound holds AT the carrier with no guarded-region scan
/// needed. Every other shape returns `false` (fail-closed — the carrier stays).
///
/// Width note: unlike the guard arm, this arm DELIBERATELY follows the byte/half
/// zero-extension (`Uxtb`/`Uxth`/`Uxtw`) that produces the 64-bit index from a
/// narrow computation — the zero-extension is itself the value bound, so there
/// is no 32-vs-64-bit unsoundness (the extended value is exactly the narrow one).
fn narrow_index_proven_below(
    single_def: &HashMap<VReg, (BlockId, usize)>,
    func: &MachFunction,
    idx: VReg,
    k: i64,
) -> bool {
    let Some((root, _links)) = chain_root(single_def, func, idx) else {
        return false;
    };
    if root.class != RegClass::Gpr64 {
        return false;
    }
    let Some(&(b, pos)) = single_def.get(&root) else {
        return false;
    };
    let Some(inst) = inst_at(func, b, pos) else {
        return false;
    };
    match inst.opcode {
        AArch64Opcode::Uxtb => k >= 256,
        AArch64Opcode::Uxth => k >= 65536,
        AArch64Opcode::Uxtw => match inst.operands.get(1) {
            Some(MachOperand::VReg(s)) if s.class == RegClass::Gpr32 => {
                gpr32_value_proven_below(single_def, func, *s, k)
            }
            _ => false,
        },
        AArch64Opcode::AndRI => and_ri_mask_below(inst, k),
        _ => false,
    }
}

/// Find every provably-redundant `TrapBoundsCheckExact` carrier. See the module
/// docs for the exact soundness conditions; any failure keeps the carrier.
/// Returns `(block, carrier InstId)` pairs.
fn find_carrier_eliminations(func: &MachFunction, dom: &DomTree) -> Vec<(BlockId, InstId)> {
    // Each `trace!` names the reason a candidate is kept; it emits nothing.
    macro_rules! trace {
        ($($a:tt)*) => {};
    }

    let single_def = build_single_def_index(func);
    let mut out: Vec<(BlockId, InstId)> = Vec::new();

    for &c_blk in &func.block_order {
        let insts = func.block(c_blk).insts.clone();
        'carrier: for (p, &iid) in insts.iter().enumerate() {
            let inst = func.inst(iid);
            if inst.opcode != AArch64Opcode::TrapBoundsCheckExact {
                continue;
            }
            // Proof-annotated / kernel-owned carrier: leave it to the proof path.
            if inst.proof.is_some() {
                continue;
            }
            // Carrier shape: `[_, VReg(idx), Imm(K)]` (read the index from
            // operand[1]; operand[0] is identity metadata that equals idx here).
            let (idx, k) = match inst.operands.as_slice() {
                [_, MachOperand::VReg(idx), MachOperand::Imm(k)] => (*idx, *k),
                _ => continue,
            };
            if !(0..=MAX_IMM).contains(&k) {
                continue;
            }
            if idx.class != RegClass::Gpr64 {
                trace!("{c_blk:?}[{p}] decline: idx {idx:?} not Gpr64");
                continue;
            }

            // NARROW-INDEX arm (mask / byte-range) — additive and INDEPENDENT of
            // the dominating-guard arm below. The carrier is dead when `idx`'s
            // own single definition STRUCTURALLY bounds its value below `k`:
            //   * a byte/half zero-extension (`Uxtb`->[0,255], `Uxth`->[0,65535])
            //     with a wide-enough array (`k >= 256` / `k >= 65536`), or
            //   * a constant mask (`AndRI`/`Uxtw`-of-`AndRI`) with `m < k`.
            // This is the base64/crc32 table, RC4 S-box, and byte-histogram
            // access-pattern class the guard arm cannot see (no dominating
            // compare). Fail-closed: any other def shape falls through.
            if narrow_index_proven_below(&single_def, func, idx, k) {
                trace!(
                    "{c_blk:?}[{p}] ELIMINATE: idx<u{k} proven by narrow-index (mask/byte-range)"
                );
                out.push((c_blk, iid));
                continue 'carrier;
            }

            // (1) Index canonicalization to a root, recording each copy link.
            let Some((root, idx_links)) = chain_root(&single_def, func, idx) else {
                continue;
            };
            if root.class != RegClass::Gpr64 {
                trace!("{c_blk:?}[{p}] decline: root {root:?} not Gpr64");
                continue;
            }
            // (2)-(5) A strict dominator's unsigned guard on the same root
            // whose constant bound implies `idx <u k` at the carrier.
            if constant_guard_proves_below(func, dom, &single_def, c_blk, p, root, &idx_links, k) {
                trace!("{c_blk:?}[{p}] ELIMINATE: idx<u{k} proven by a dominating guard");
                out.push((c_blk, iid));
                continue 'carrier;
            }
            trace!("{c_blk:?}[{p}] decline: no proving dominator guard (K={k})");
        }
    }
    out
}

/// The carrier arm's conditions 2-5: some strict dominator `D` of `c_blk`
/// ends in an unsigned guard on `root` whose CONSTANT bound `K'` (a `CmpRI`
/// immediate or a single-def two-operand `Movz`) implies `root <u k` on the
/// guarded edge (`K' <= k` strict, `K' < k` non-strict), that edge's target
/// `T` has `D` as its only predecessor and dominates `c_blk`, every index copy
/// link (`idx_links`, from `chain_root`) is a snapshot inside the guarded
/// window, and `root` is not redefined between the guard and position `p` of
/// `c_blk` ([`region_redefines_root`]). Any unproven condition is `false`.
///
/// Shared by the carrier arm (a `TrapBoundsCheckExact [_, idx, Imm(k)]` at
/// `p`) and the trap-branch arm's constant-bound rule (an explicit
/// `Cmp(idx, K) ; BCond` whose compare is at `p`): the proof is about the
/// index's value at `p`, not about what the failing path runs.
#[allow(clippy::too_many_arguments)]
fn constant_guard_proves_below(
    func: &MachFunction,
    dom: &DomTree,
    single_def: &HashMap<VReg, (BlockId, usize)>,
    c_blk: BlockId,
    p: usize,
    root: VReg,
    idx_links: &[(BlockId, usize)],
    k: i64,
) -> bool {
    // Each `trace!` names the reason a candidate is kept; it emits nothing.
    macro_rules! trace {
        ($($a:tt)*) => {};
    }
    if !(0..=MAX_IMM).contains(&k) || root.class != RegClass::Gpr64 {
        return false;
    }
    // An index copy captured at/after `p` in C is not a valid snapshot of the
    // guarded value.
    if idx_links.iter().any(|&(lb, li)| lb == c_blk && li >= p) {
        trace!("{c_blk:?}[{p}] decline: index copy after the check in C");
        return false;
    }
    let mut d = c_blk;
    for _hop in 0..MAX_DOM_HOPS {
        let Some(up) = dom.idom(d) else { break };
        if up == d {
            break; // reached entry
        }
        d = up;
        let Some(gb) = parse_guard_branch(func, d) else {
            continue;
        };
        // Guard's compared value must canonicalize to the carrier root.
        if gb.op0.class != RegClass::Gpr64 {
            continue;
        }
        let Some((g_root, g_links)) = chain_root(single_def, func, gb.op0) else {
            continue;
        };
        if g_root != root {
            continue;
        }

        // (3) Bound value: an immediate, or a single-def 2-operand
        // `Movz` constant (full-width Gpr64; shifted/Movk-completed
        // constants are unresolved -> keep).
        let kp = match gb.rhs {
            CmpRhs::Imm(kp) => kp,
            CmpRhs::Reg(rv) => {
                if rv.class != RegClass::Gpr64 {
                    continue;
                }
                let Some(&(mb, mpos)) = single_def.get(&rv) else {
                    continue;
                };
                let Some(m) = inst_at(func, mb, mpos) else {
                    continue;
                };
                match (m.opcode, m.operands.as_slice()) {
                    (AArch64Opcode::Movz, [MachOperand::VReg(_), MachOperand::Imm(c)]) => *c,
                    _ => continue,
                }
            }
        };
        if !(0..=MAX_IMM).contains(&kp) {
            continue;
        }

        // Guarded successor + strictness from the taken condition.
        let (t, strict) = match gb.cc {
            CondCode::LO => (gb.taken, true),
            CondCode::HS => (gb.not_taken, true),
            CondCode::LS => (gb.taken, false),
            CondCode::HI => (gb.not_taken, false),
            // Signed / equality conditions never prove an unsigned bound.
            _ => continue,
        };
        // Bound implication over non-negative immediates.
        let implied = if strict { kp <= k } else { kp < k };
        if !implied {
            continue;
        }

        // Guard-side anchor: the real compare, tightened by any
        // guard-side copy link (each must live in D before the compare).
        let mut d_from = gb.cmp_pos;
        let mut g_ok = true;
        for &(lb, li) in &g_links {
            if lb != d || li >= gb.cmp_pos {
                g_ok = false;
                break;
            }
            d_from = d_from.min(li);
        }
        if !g_ok {
            trace!("{c_blk:?}[{p}] decline: guard-side copy captured outside D-window");
            continue;
        }
        // Index-chain links captured in D fold into the same anchor.
        for &(lb, li) in idx_links {
            if lb == d {
                d_from = d_from.min(li);
            }
        }

        // (4) Edge-dominance: T's only predecessor is D, and T dom C.
        match func.block(t).preds.as_slice() {
            [only] if *only == d => {}
            _ => continue,
        }
        if !dom.dominates(t, c_blk) {
            continue;
        }
        // Index-chain links OUTSIDE D must live in a block dominated by
        // the guarded edge target, so each snapshot is inside the scan.
        if idx_links
            .iter()
            .any(|&(lb, _)| lb != d && !dom.dominates(t, lb))
        {
            trace!("{c_blk:?}[{p}] decline: index copy link outside guard {d:?} region");
            continue;
        }

        // (5) No-redefinition scan over the guarded region.
        if region_redefines_root(func, t, c_blk, p, d, d_from, root) {
            trace!(
                "{c_blk:?}[{p}] decline: root {root:?} redefined in guarded region (guard {d:?})"
            );
            continue;
        }

        trace!(
            "{c_blk:?}[{p}] ELIMINATE: idx<u{k} proven by guard {d:?} ({}{kp}) edge->{t:?}",
            if strict { "<u" } else { "<=u" }
        );
        return true;
    }
    false
}

// ===========================================================================
// Register-bound trap-branch arm
// ===========================================================================

/// A proven explicit bounds check to fold: `block` ends in
/// `Cmp(idx, bound) ; BCond cc ; B` whose failing edge enters the diverging
/// block `trap` (`is_diverging_sink`), and either a dominating guard already
/// establishes `idx <u len` on every path into it, or `idx`'s own definition
/// bounds it below a constant `bound` (the narrow-index arm). The fold unlinks
/// the `BCond` and retargets the trailing `B` to `cont`; the compare stays (its
/// flags are unchanged, and DCE removes it once nothing reads them).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct TrapBranchFold {
    block: BlockId,
    bcond: InstId,
    fall: InstId,
    cont: BlockId,
    trap: BlockId,
}

/// A failing successor the trap-branch fold may drop: a block with NO
/// successors whose LAST instruction is `Brk` — it can only diverge. That is
/// the bare trap block of a backend checked-trap guard (every instruction
/// `Brk`) and equally the RAISE block of a source panic: the payload and
/// `#[track_caller]` Location argument setup, the `Bl` to the exact panic entry
/// (`panic_bounds_check(index, len)`, …) and the `Brk` of its `Unreachable`.
///
/// Why the block's CONTENTS do not matter to soundness: the fold is justified
/// by the dominating guard proving the check's condition at the check — the
/// failing edge is never taken on any execution — so what that edge would have
/// run is irrelevant. Requiring a diverging, successor-less sink keeps the
/// rule to genuine checks (a branch to a returning or continuing block is an
/// ordinary branch and is left alone) and keeps the multi-fold argument in
/// `run_core` intact: a dropped edge leads into a block that guards nothing.
/// A raise that names an unwind landing pad (`Invoke`, so the block HAS
/// successors) is not matched and its check stays.
fn is_diverging_sink(func: &MachFunction, b: BlockId) -> bool {
    let block = func.block(b);
    block.succs.is_empty()
        && block
            .insts
            .last()
            .is_some_and(|&iid| func.inst(iid).opcode == AArch64Opcode::Brk)
}

/// Whether any instruction of `func` is a volatile access. The volatile-trace
/// preservation check treats every source edge as takeable and refuses a
/// function whose final stream lost a path, so the trap-branch arm leaves such
/// functions alone instead of trading a runtime check for a compile refusal.
fn function_has_volatile_access(func: &MachFunction) -> bool {
    func.block_order.iter().any(|&b| {
        func.block(b).insts.iter().any(|&iid| {
            matches!(
                func.inst(iid).opcode,
                AArch64Opcode::VolatileLdrRI
                    | AArch64Opcode::VolatileLdrbRI
                    | AArch64Opcode::VolatileLdrhRI
                    | AArch64Opcode::VolatileStrRI
                    | AArch64Opcode::VolatileStrbRI
                    | AArch64Opcode::VolatileStrhRI
            )
        })
    })
}

/// A decoded explicit register-bound bounds check at the end of `c`.
struct TrapCheck {
    guard: GuardBranch,
    idx: VReg,
    /// The bound: a `Gpr64` length register, or an immediate.
    bound: CmpRhs,
    bcond: InstId,
    fall: InstId,
    cont: BlockId,
    trap: BlockId,
}

/// Parse `c`'s terminator as `CmpRR(idx, len) ; BCond cc, X ; B Y` with both
/// operands `Gpr64` (or `CmpRI(idx, #K)` with `idx` `Gpr64`, a constant bound
/// only the narrow-index arm can use), `cc` a strict unsigned test (`LO`: `X` continues and `Y`
/// traps; `HS`: `X` traps and `Y` continues), `c`'s successors exactly
/// `{X, Y}`, and the failing successor a diverging sink. Proof-annotated
/// compares or branches belong to the kernel-gated proof path and are skipped.
fn parse_trap_check(func: &MachFunction, c: BlockId) -> Option<TrapCheck> {
    let insts = &func.block(c).insts;
    let n = insts.len();
    if n < 3 {
        return None;
    }
    let (bcond, fall) = (insts[n - 2], insts[n - 1]);
    if func.inst(fall).opcode != AArch64Opcode::B || func.inst(bcond).opcode != AArch64Opcode::BCond
    {
        return None;
    }
    let guard = parse_guard_branch(func, c)?;
    if guard.cmp_pos + 3 != n {
        return None;
    }
    let (idx, bound) = match (guard.op0, guard.rhs) {
        (idx, CmpRhs::Reg(len)) if idx.class == RegClass::Gpr64 && len.class == RegClass::Gpr64 => {
            (idx, CmpRhs::Reg(len))
        }
        (idx, CmpRhs::Imm(k)) if idx.class == RegClass::Gpr64 => (idx, CmpRhs::Imm(k)),
        _ => return None,
    };
    let fall_target = match func.inst(fall).operands.as_slice() {
        [MachOperand::Block(t)] => *t,
        _ => return None,
    };
    if fall_target == guard.taken {
        return None;
    }
    let succs = &func.block(c).succs;
    if succs.len() != 2 || !succs.contains(&guard.taken) || !succs.contains(&fall_target) {
        return None;
    }
    let (cont, trap) = match guard.cc {
        CondCode::LO => (guard.taken, fall_target),
        CondCode::HS => (fall_target, guard.taken),
        _ => return None,
    };
    if !is_diverging_sink(func, trap) {
        return None;
    }
    if [insts[guard.cmp_pos], bcond, fall]
        .iter()
        .any(|&iid| func.inst(iid).proof.is_some())
    {
        return None;
    }
    Some(TrapCheck {
        guard,
        idx,
        bound,
        bcond,
        fall,
        cont,
        trap,
    })
}

/// Whether the single-def values `a` and `b` are two plain loads of the same
/// bytes in one block with nothing between them that can write memory or
/// redefine their base: same opcode, destination class, base register and
/// immediate offset. Each execution of that block then gives both the same
/// value; the caller's region scan rules out a re-execution between the guard
/// and the check.
fn same_block_equal_loads(
    single_def: &HashMap<VReg, (BlockId, usize)>,
    func: &MachFunction,
    a: VReg,
    b: VReg,
) -> bool {
    let (Some(&(ba, pa)), Some(&(bb, pb))) = (single_def.get(&a), single_def.get(&b)) else {
        return false;
    };
    if ba != bb || pa == pb {
        return false;
    }
    let (Some(ia), Some(ib)) = (inst_at(func, ba, pa), inst_at(func, bb, pb)) else {
        return false;
    };
    if ia.opcode != ib.opcode
        || !matches!(
            ia.opcode,
            AArch64Opcode::LdrRI
                | AArch64Opcode::LdrbRI
                | AArch64Opcode::LdrhRI
                | AArch64Opcode::LdrsbRI
                | AArch64Opcode::LdrshRI
        )
    {
        return false;
    }
    let base = match (ia.operands.as_slice(), ib.operands.as_slice()) {
        (
            [
                MachOperand::VReg(da),
                MachOperand::VReg(base_a),
                MachOperand::Imm(off_a),
            ],
            [
                MachOperand::VReg(db),
                MachOperand::VReg(base_b),
                MachOperand::Imm(off_b),
            ],
        ) if *da == a && *db == b && da.class == db.class && base_a == base_b && off_a == off_b => {
            *base_a
        }
        _ => return false,
    };
    let (lo, hi) = (pa.min(pb), pa.max(pb));
    func.block(ba).insts[lo + 1..hi].iter().all(|&iid| {
        let inst = func.inst(iid);
        let effect = opcode_effect(inst.opcode);
        !effect.writes_memory() && !effect.is_barrier() && !inst_defines_vreg(inst, base)
    })
}

/// Fold every explicit register-bound bounds check that a dominating unsigned
/// guard decides. `idx <u len` holds at the check when some strict dominator
/// `D` ends in `Cmp(idx', len') ; BCond` whose strict unsigned `<` edge enters
/// `T`, with:
///
/// 1. `idx` and `idx'` canonicalizing (full-width `Gpr64` copies) to one root;
/// 2. `len` and `len'` canonicalizing to one root, or to two equal loads
///    ([`same_block_equal_loads`]);
/// 3. `T`'s only predecessor `D` and `T` dominating the check block `C`;
/// 4. every check-side copy link a snapshot inside the guarded window (in `C`
///    before the compare, in `D` before the guard compare, or in a block `T`
///    dominates) and every guard-side link in `D` before the guard compare;
/// 5. no root redefined in the guarded region or in `D` from the anchor on
///    ([`region_redefines_root`]).
///
/// A non-strict guard (`LS`/`HI`) proves only `idx <=u len` and never folds.
///
/// A check against a CONSTANT bound `K` folds instead when `idx`'s own
/// definition bounds it below `K` (the narrow-index arm), or when the carrier
/// arm's guard rule proves `idx <u K` at the check's compare
/// ([`constant_guard_proves_below`]: a dominating unsigned guard on the same
/// root against a constant `K'`, `K' <= K` strict or `K' < K` non-strict).
fn find_trap_branch_folds(func: &MachFunction, dom: &DomTree) -> Vec<TrapBranchFold> {
    let mut out = Vec::new();
    // Candidates first: the whole-function indexes below are built only for a
    // function that has an explicit register-bound check at all.
    let checks: Vec<(BlockId, TrapCheck)> = func
        .block_order
        .iter()
        .filter_map(|&b| parse_trap_check(func, b).map(|check| (b, check)))
        .collect();
    if checks.is_empty() || function_has_volatile_access(func) {
        return out;
    }
    let single_def = build_single_def_index(func);
    for (c_blk, check) in checks {
        let fold = TrapBranchFold {
            block: c_blk,
            bcond: check.bcond,
            fall: check.fall,
            cont: check.cont,
            trap: check.trap,
        };
        // NARROW-INDEX arm (the carrier arm's, applied to an explicit check
        // against a CONSTANT bound): the index's own single definition proves
        // `idx <u K` (a byte/half zero-extension or a constant mask), with no
        // dominating guard needed — the byte-histogram `h[b as usize]` shape.
        if let Some(k) = constant_bound(&single_def, func, check.bound) {
            if (0..=MAX_IMM).contains(&k)
                && narrow_index_proven_below(&single_def, func, check.idx, k)
            {
                out.push(fold);
                continue;
            }
            // CONSTANT-BOUND GUARD arm (the carrier arm's guard rule, applied to
            // an explicit check against a CONSTANT bound): a strict dominator's
            // unsigned guard on the same index root, against a constant `K'`
            // that implies `idx <u K` — `while i < N { .. a[i] .. }` over an
            // array of `N` elements, whose check stopped being a carrier when
            // its failing edge began to raise `panic_bounds_check`. The proof
            // is the guard's, at the check's compare; the failing block only
            // has to be a diverging sink (`parse_trap_check`).
            if let Some((idx_root, idx_links)) = chain_root(&single_def, func, check.idx)
                && constant_guard_proves_below(
                    func,
                    dom,
                    &single_def,
                    c_blk,
                    check.guard.cmp_pos,
                    idx_root,
                    &idx_links,
                    k,
                )
            {
                out.push(fold);
                continue;
            }
        }
        let CmpRhs::Reg(check_len) = check.bound else {
            continue;
        };
        let p = check.guard.cmp_pos;
        let Some((idx_root, idx_links)) = chain_root(&single_def, func, check.idx) else {
            continue;
        };
        let Some((len_root, len_links)) = chain_root(&single_def, func, check_len) else {
            continue;
        };
        if idx_root.class != RegClass::Gpr64 || len_root.class != RegClass::Gpr64 {
            continue;
        }
        let mut d = c_blk;
        for _hop in 0..MAX_DOM_HOPS {
            let Some(up) = dom.idom(d) else { break };
            if up == d {
                break;
            }
            d = up;
            let Some(gb) = parse_guard_branch(func, d) else {
                continue;
            };
            let CmpRhs::Reg(g_len) = gb.rhs else {
                continue;
            };
            if g_len.class != RegClass::Gpr64 {
                continue;
            }
            let t = match gb.cc {
                CondCode::LO => gb.taken,
                CondCode::HS => gb.not_taken,
                _ => continue,
            };
            let Some((g_idx_root, g_idx_links)) = chain_root(&single_def, func, gb.op0) else {
                continue;
            };
            let Some((g_len_root, g_len_links)) = chain_root(&single_def, func, g_len) else {
                continue;
            };
            if g_idx_root != idx_root {
                continue;
            }
            if g_len_root != len_root
                && !same_block_equal_loads(&single_def, func, g_len_root, len_root)
            {
                continue;
            }
            match func.block(t).preds.as_slice() {
                [only] if *only == d => {}
                _ => continue,
            }
            if !dom.dominates(t, c_blk) {
                continue;
            }
            // Guard-side links: inside D, before the guard compare.
            let mut d_from = gb.cmp_pos;
            let guard_links_ok = g_idx_links
                .iter()
                .chain(g_len_links.iter())
                .all(|&(lb, li)| lb == d && li < gb.cmp_pos);
            if !guard_links_ok {
                continue;
            }
            for &(_, li) in g_idx_links.iter().chain(g_len_links.iter()) {
                d_from = d_from.min(li);
            }
            // Check-side links: snapshots inside the guarded window.
            let mut check_links_ok = true;
            for &(lb, li) in idx_links.iter().chain(len_links.iter()) {
                if lb == c_blk {
                    if li >= p {
                        check_links_ok = false;
                    }
                } else if lb == d {
                    d_from = d_from.min(li);
                } else if !dom.dominates(t, lb) {
                    check_links_ok = false;
                }
            }
            if !check_links_ok {
                continue;
            }
            let mut roots = vec![idx_root, len_root];
            if g_len_root != len_root {
                roots.push(g_len_root);
            }
            if roots
                .iter()
                .any(|&r| region_redefines_root(func, t, c_blk, p, d, d_from, r))
            {
                continue;
            }
            out.push(fold);
            break;
        }
    }
    out
}

/// The constant value of a check's bound: the immediate of a `CmpRI`, or the
/// constant of a single-def two-operand `Movz` (full-width `Gpr64`; a shifted or
/// `Movk`-completed constant is unresolved) — the same resolution the carrier
/// arm applies to a guard's bound. `None` for anything else.
fn constant_bound(
    single_def: &HashMap<VReg, (BlockId, usize)>,
    func: &MachFunction,
    bound: CmpRhs,
) -> Option<i64> {
    match bound {
        CmpRhs::Imm(k) => Some(k),
        CmpRhs::Reg(r) if r.class == RegClass::Gpr64 => {
            let &(b, pos) = single_def.get(&r)?;
            match inst_at(func, b, pos) {
                Some(m) => match (m.opcode, m.operands.as_slice()) {
                    (AArch64Opcode::Movz, [MachOperand::VReg(_), MachOperand::Imm(c)]) => Some(*c),
                    _ => None,
                },
                None => None,
            }
        }
        CmpRhs::Reg(_) => None,
    }
}

/// Apply one recognized fold: unlink the `BCond`, retarget the trailing `B` to
/// the continuation and drop the edge into the trap block.
fn apply_trap_branch_fold(func: &mut MachFunction, fold: TrapBranchFold) {
    func.block_mut(fold.block)
        .insts
        .retain(|&iid| iid != fold.bcond);
    func.inst_mut(fold.fall).operands = vec![MachOperand::Block(fold.cont)];
    func.block_mut(fold.block).succs = vec![fold.cont];
    func.block_mut(fold.trap)
        .preds
        .retain(|&pred| pred != fold.block);
}

#[cfg(test)]
mod tests;
