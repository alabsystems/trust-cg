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

use std::collections::{HashMap, HashSet, VecDeque};

use trust_cg_ir::{
    AArch64Opcode, BlockId, CondCode, InstId, MachFunction, MachInst, MachOperand, RegClass, VReg,
};

use crate::dom::DomTree;
use crate::effects::{for_each_inst_def, inst_defines_vreg};
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
#[derive(Default)]
pub struct AArch64BoundsCheckElimination {
    /// Number of carriers eliminated by the most recent [`run`] invocation
    /// (diagnostics / tests only).
    ///
    /// [`run`]: MachinePass::run
    pub last_run_eliminations: usize,
}

impl AArch64BoundsCheckElimination {
    /// Create the pass.
    pub fn new() -> Self {
        Self {
            last_run_eliminations: 0,
        }
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
        if !enabled {
            return false;
        }
        let dom = DomTree::compute(func);
        self.run_core(func, &dom)
    }

    /// Core: recognize every provably-redundant carrier against the ORIGINAL,
    /// unmutated function, then delete them. Deletion removes only the carrier
    /// `InstId` from its block's instruction list; the `MachInst` stays inert
    /// in the arena (unreferenced, never encoded), and no CFG edge changes.
    fn run_core(&mut self, func: &mut MachFunction, dom: &DomTree) -> bool {
        let sites = find_carrier_eliminations(func, dom);
        if sites.is_empty() {
            return false;
        }
        // Group carrier InstIds by block, then unlink them (retain != id).
        let mut by_block: HashMap<BlockId, HashSet<InstId>> = HashMap::new();
        for &(b, id) in &sites {
            by_block.entry(b).or_default().insert(id);
        }
        for (b, ids) in by_block {
            func.block_mut(b).insts.retain(|iid| !ids.contains(iid));
        }
        self.last_run_eliminations = sites.len();
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
        if !bce_enabled() {
            return false;
        }
        let changed = {
            let dom = analyses.domtree(func);
            self.run_core(func, dom)
        };
        // A carrier delete changes no CFG edge, so the domtree stays valid; we
        // still invalidate defensively so downstream cached analyses recompute.
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
    let mut counts: HashMap<VReg, u32> = HashMap::new();
    let mut single: HashMap<VReg, (BlockId, usize)> = HashMap::new();
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

    Some(GuardBranch {
        cmp_pos,
        op0,
        rhs,
        cc,
        taken,
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
    let mut fwd: HashSet<BlockId> = HashSet::new();
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
    let mut bwd: HashSet<BlockId> = HashSet::new();
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
    // Scan the intersection for defs of `root` (slice `c_blk` at `p`).
    for &b in fwd.intersection(&bwd) {
        for (i, &iid) in func.block(b).insts.iter().enumerate() {
            if b == c_blk && i >= p {
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

/// A constant `AndRI [dst, src, Imm(m)]` mask that is non-negative and strictly
/// below `k` — so `dst = src & m` has an unsigned value in `[0, m]`, hence `< k`.
/// A negative or `>= k` mask (or a non-immediate operand) is unproven.
fn and_ri_mask_below(inst: &MachInst, k: i64) -> bool {
    matches!(inst.operands.get(2), Some(MachOperand::Imm(m)) if *m >= 0 && *m < k)
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
    let dbg = std::env::var_os("TCG_AARCH64_BCE_DEBUG").is_some();
    macro_rules! trace {
        ($($a:tt)*) => { if dbg { eprintln!("[a64-bce] {}", format!($($a)*)); } };
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
            // An index copy captured at/after the carrier in C is not a valid
            // snapshot of the guarded value.
            if idx_links.iter().any(|&(lb, li)| lb == c_blk && li >= p) {
                trace!("{c_blk:?}[{p}] decline: index copy after carrier in C");
                continue;
            }

            // (2) Walk strict dominators of C for a proving unsigned guard.
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
                let Some((g_root, g_links)) = chain_root(&single_def, func, gb.op0) else {
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
                            (AArch64Opcode::Movz, [MachOperand::VReg(_), MachOperand::Imm(c)]) => {
                                *c
                            }
                            _ => continue,
                        }
                    }
                };
                if !(0..=MAX_IMM).contains(&kp) {
                    continue;
                }

                // Guarded successor + strictness from the taken condition.
                let other = func.block(d).succs.iter().copied().find(|s| *s != gb.taken);
                let (t, strict) = match gb.cc {
                    CondCode::LO => (gb.taken, true),
                    CondCode::HS => match other {
                        Some(f) => (f, true),
                        None => continue,
                    },
                    CondCode::LS => (gb.taken, false),
                    CondCode::HI => match other {
                        Some(f) => (f, false),
                        None => continue,
                    },
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
                for &(lb, li) in &idx_links {
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
                out.push((c_blk, iid));
                continue 'carrier;
            }
            trace!("{c_blk:?}[{p}] decline: no proving dominator guard (K={k})");
        }
    }
    out
}

#[cfg(test)]
mod tests;
