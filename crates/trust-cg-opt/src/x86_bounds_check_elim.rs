// trust-cg-opt - x86-64 dominated-identical-compare bounds-check elimination
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! x86-64 machine-level elimination of a redundant "own-length" bounds-check
//! diamond that a dominating IDENTICAL compare already proves can never trap.
//!
//! # The shape this eliminates
//!
//! For a counted loop over a slice's own length (`for i in 0..s.len()
//! { .. s[i] .. }`) the x86 instruction selector emits, per iteration, TWO
//! structurally-related unsigned range checks against the same `(iv, len)`:
//!
//! ```text
//!   header (guard):   cmp iv, len ; jb body        ; jmp exit
//!   body   (check):   ... ; cmp iv, len ; jb cont  ; <else> -> trap(ud2)
//! ```
//!
//! The guard's taken edge (`jb body`) establishes `iv <u len` on the ONLY path
//! into `body`. The body's bounds check tests the SAME comparison against the
//! SAME operands, so its trap edge is provably dead. LLVM elides this; this pass
//! makes trust-cg match it.
//!
//! # Why this is memory-safe (sound by construction, fail-safe by default)
//!
//! This pass is SAFETY-CRITICAL: removing a bounds check that is actually needed
//! is a silent out-of-bounds access (memory unsafety), strictly worse than a
//! wrong value. A check is eliminated ONLY when ALL of the following hold; ANY
//! unproven condition keeps the check (there is no wildcard/optimistic arm):
//!
//! 1. **Pure-trap target.** One of the bounds-check block's two successors is a
//!    pure trap in the sense of `crate::x86_trap_block`: a no-successor dead
//!    end that is exactly `[Ud2]` (`emit_synthetic_trap_block`) or
//!    `[Call abort, Ud2]` (the bridge's panic=abort assert block). That is the
//!    trap edge; the other successor is the fall-through (`cont`).
//! 2. **Single dominating guard.** The bounds-check block's UNIQUE predecessor
//!    `db` ends in a conditional branch, and `db` strictly dominates it. A
//!    unique predecessor means every path to the check traverses the `db->check`
//!    edge, so the predicate that edge establishes holds at the check.
//! 3. **Identical comparison.** `db`'s branch and the bounds check both compare
//!    with `CmpRR` on operands that canonicalize (through `MovRR`/`MovRR32`
//!    copies) to the SAME vregs in the SAME positions, and the guard-taken-edge
//!    predicate is the SAME unsigned relation (identical effective condition
//!    code) as the predicate needed to reach `cont`. Guard-taken therefore
//!    IMPLIES bounds-safe.
//! 4. **No redefinition between.** Neither canonical operand's root vreg is
//!    redefined between `db`'s compare and the bounds check (only `db`'s tail —
//!    its branch instructions — and the check block's head, since `db` is the
//!    check's direct and only predecessor, lie between them). A single-def root
//!    cannot be redefined at all; a multi-def root (a loop-carried `iv` merge
//!    vreg) is redefined only on its back-edge, never on the forward
//!    header->body path.
//!
//! A cross-length check (`x[i]` guarded by `i < y.len()`), a redefined index
//! (`i+1`, `i*2`), a check with no dominating identical compare, and an index
//! not derived from the guarded IV all FAIL one of (3)/(4) and are kept.
//!
//! # The rewrite
//!
//! The bounds-check block's `cmp; jcc; [jmp]` terminator is replaced by an
//! unconditional `jmp cont`, and its successor set becomes `[cont]`. The
//! redundant compare is also dropped when its RFLAGS are provably dead along
//! every path out of `cont` (a bounded flag-liveness walk); otherwise the
//! compare is retained (still correct — its flags are simply unused). Any trap
//! block left with no predecessors is deleted and the block ids are renumbered
//! back to the gap-free `0..n` range the x86 regalloc replay requires.
//!
//! Kill switch: `-Ztrust-ir-cg-args=no-x86-bce` (or `TCG_NO_X86_BCE` when used
//! standalone) disables the pass. Default ON at O2/O3, mirroring
//! `TCG_NO_VECTORIZE` / `TCG_NO_X86_SROA`.

use crate::fast_hash::{FxHashMap as HashMap, FxHashSet as HashSet};
use std::collections::VecDeque;

use trust_cg_ir::regs::VReg;
use trust_cg_ir::x86_64_ops::{X86CondCode, X86Opcode};
use trust_cg_lower::instructions::Block;
use trust_cg_lower::{X86ISelBlock, X86ISelFunction, X86ISelInst, X86ISelOperand};

use crate::x86_trap_block::is_pure_trap_block;

use crate::effects::{
    FlagOverwrite, MemoryEffect, condition_flag_overwrite, x86_opcode_effect, x86_produces_value,
    x86_reads_flags,
};
use crate::mach_view::{CfgAnalysis, predecessor_map};
use crate::x86_pass_manager::X86MachinePass;

static BCE_EARLY_COPY_DISABLED_SETTING: std::sync::OnceLock<bool> = std::sync::OnceLock::new();

/// Install an opt-out for the EARLY-GUARD-COPY arm alone (case 3b), from a
/// tracked compiler option, once
/// (`-Ztrust-ir-cg-args=no-x86-bce-earlycopy`). DEFAULT OFF (the arm is on).
///
/// Exists for the same reason as [`set_bce_reload_disabled`]: an arm that cannot
/// be toggled on its own cannot be credited with anything.
pub fn set_bce_early_copy_disabled(disabled: bool) -> bool {
    match BCE_EARLY_COPY_DISABLED_SETTING.set(disabled) {
        Ok(()) => true,
        Err(requested) => BCE_EARLY_COPY_DISABLED_SETTING.get() == Some(&requested),
    }
}

/// True iff the early-guard-copy arm (case 3b) may fire.
fn bce_early_copy_enabled() -> bool {
    if let Some(disabled) = BCE_EARLY_COPY_DISABLED_SETTING.get() {
        return !*disabled;
    }
    !crate::tcg_env_flag("TCG_NO_X86_BCE_EARLYCOPY")
}

static BCE_RELOAD_DISABLED_SETTING: std::sync::OnceLock<bool> = std::sync::OnceLock::new();

/// Install an opt-out for the RELOADED-LENGTH arm alone (case 4), from a tracked
/// compiler option, once (`-Ztrust-ir-cg-args=no-x86-bce-reload`). DEFAULT OFF
/// (the arm is on).
///
/// This exists because `no-x86-bce` turns off the WHOLE pass, so an A/B against
/// it cannot tell what case 4 contributed from what cases 1-3 already did. That
/// distinction is not cosmetic: a first measurement of this arm read a 12 -> 9
/// instruction win in a hot loop off the whole-pass A/B and attributed it to
/// case 4, which was wrong. An arm that cannot be isolated cannot be credited.
pub fn set_bce_reload_disabled(disabled: bool) -> bool {
    match BCE_RELOAD_DISABLED_SETTING.set(disabled) {
        Ok(()) => true,
        Err(requested) => BCE_RELOAD_DISABLED_SETTING.get() == Some(&requested),
    }
}

/// True iff the reloaded-length arm (case 4) may fire.
fn bce_reload_enabled() -> bool {
    if let Some(disabled) = BCE_RELOAD_DISABLED_SETTING.get() {
        return !*disabled;
    }
    !crate::tcg_env_flag("TCG_NO_X86_BCE_RELOAD")
}

static BCE_POINTER_RELOAD: std::sync::OnceLock<bool> = std::sync::OnceLock::new();

/// Install the case-5 same-pointer reload opt-in from a TRACKED compiler option
/// (`-Ztrust-ir-cg-args=x86-bce-ptr-reload`). DEFAULT OFF: this pass removes
/// bounds checks, so a new admission arm ships opt-in and is measured before any
/// question of a default arises.
pub fn set_bce_pointer_reload_enabled(enabled: bool) -> bool {
    match BCE_POINTER_RELOAD.set(enabled) {
        Ok(()) => true,
        Err(requested) => BCE_POINTER_RELOAD.get() == Some(&requested),
    }
}

static BCE_TRACE: std::sync::OnceLock<bool> = std::sync::OnceLock::new();

/// Install the branch-form accept/decline trace from a TRACKED compiler option
/// (`-Ztrust-ir-cg-args=trace-x86-bce`).
///
/// The carrier path already had a trace, but only behind the `TCG_*` environment
/// variable `TCG_X86_BCE_CARRIER_DEBUG`, which `trustc` REFUSES before the backend
/// loads — so it was unreachable through the bridge, and the BRANCH-form path (the
/// one that decides `while k < v.len() { .. v[k] .. }`) had no trace at all.
pub fn set_bce_trace_enabled(enabled: bool) -> bool {
    match BCE_TRACE.set(enabled) {
        Ok(()) => true,
        Err(requested) => BCE_TRACE.get() == Some(&requested),
    }
}

fn bce_trace_enabled() -> bool {
    if let Some(enabled) = BCE_TRACE.get() {
        return *enabled;
    }
    crate::tcg_env_flag("TCG_X86_BCE_TRACE")
}

fn bce_pointer_reload_enabled() -> bool {
    if let Some(enabled) = BCE_POINTER_RELOAD.get() {
        return *enabled;
    }
    crate::tcg_env_flag("TCG_X86_BCE_PTR_RELOAD")
}

static BCE_DISABLED_SETTING: std::sync::OnceLock<bool> = std::sync::OnceLock::new();

/// Install this pass's opt-out from a TRACKED compiler option, once
/// (`-Ztrust-ir-cg-args=no-x86-bce`). Same contract as
/// [`crate::x86_vectorize::set_trace_enabled`]: `true` when the installed value
/// is `disabled` (first install, or an identical re-install), `false` when an
/// earlier install disagrees, so the embedder refuses rather than run one
/// compilation under two bounds-check policies.
///
/// `true` means the opt-out is ON, i.e. every bounds check is kept (always
/// correct, never faster). Under `trustc` the `TCG_NO_X86_BCE` variable is
/// refused before the backend loads, so this setter is the ONLY channel that
/// reaches the pass there -- which is what makes an A/B of a safety-critical
/// pass possible through the bridge instead of by rebuilding it twice.
pub fn set_bce_disabled(disabled: bool) -> bool {
    match BCE_DISABLED_SETTING.set(disabled) {
        Ok(()) => true,
        Err(requested) => BCE_DISABLED_SETTING.get() == Some(&requested),
    }
}

/// True iff the pass may run. The tracked option wins; the environment read is
/// the fallback for standalone (non-`trustc`) use.
pub fn bce_enabled() -> bool {
    if let Some(disabled) = BCE_DISABLED_SETTING.get() {
        return !*disabled;
    }
    !crate::tcg_env_flag("TCG_NO_X86_BCE")
}

/// x86-64 dominated-identical-compare bounds-check elimination pass.
#[derive(Default)]
pub struct X86BoundsCheckElimination {
    /// Number of bounds checks eliminated by the most recent [`run`]
    /// invocation (diagnostics / tests only).
    ///
    /// [`run`]: X86MachinePass::run
    pub last_run_eliminations: usize,
    /// Admit case 5, the same-POINTER reload arm (see
    /// [`same_value_by_pointer_reload`]). DEFAULT OFF.
    ///
    /// Threaded through the pass as well as installable globally, because a
    /// `OnceLock` cannot be flipped twice in one process and the refutations for
    /// this arm must run with it BOTH on and off in the same test binary.
    pointer_reload: bool,
}

impl X86BoundsCheckElimination {
    /// Enable case 5, the same-pointer reload admission arm, for this pass
    /// instance (see [`same_value_by_pointer_reload`]). DEFAULT OFF; the
    /// production lever is `-Ztrust-ir-cg-args=x86-bce-ptr-reload`.
    pub fn with_pointer_reload(mut self, enabled: bool) -> Self {
        self.pointer_reload = enabled;
        self
    }

    /// Create the pass.
    pub fn new() -> Self {
        Self {
            last_run_eliminations: 0,
            pointer_reload: false,
        }
    }

    /// Run the pass directly on a function (tests / standalone use).
    pub fn run_on_function(&mut self, func: &mut X86ISelFunction) -> bool {
        <Self as X86MachinePass>::run(self, func)
    }
}

impl X86MachinePass for X86BoundsCheckElimination {
    fn name(&self) -> &str {
        "x86-bounds-check-elim"
    }

    fn run(&mut self, func: &mut X86ISelFunction) -> bool {
        self.last_run_eliminations = 0;
        if !bce_enabled() {
            return false;
        }
        let mut changed = false;

        // Carrier-aware arm (opt-in): eliminate still-unexpanded
        // `TrapBoundsCheckExact` proof carriers whose enclosing-guard bound is
        // machine-proven at the carrier site. Runs FIRST — the carriers exist
        // only until the post-pass expansion, and deleting one is a single
        // instruction removal with no CFG surgery.
        if bce_carrier_enabled() {
            let sites = find_carrier_eliminations(func);
            if !sites.is_empty() {
                let mut by_block: HashMap<Block, Vec<usize>> = HashMap::default();
                for (b, i) in &sites {
                    by_block.entry(*b).or_default().push(*i);
                }
                for (b, mut idxs) in by_block {
                    idxs.sort_unstable_by(|a, b| b.cmp(a)); // descending
                    if let Some(block) = func.blocks.get_mut(&b) {
                        for i in idxs {
                            block.insts.remove(i);
                        }
                    }
                }
                self.last_run_eliminations += sites.len();
                changed = true;
            }
        }

        // All candidates are found against the ORIGINAL, unmutated function so
        // that chained checks (`s[i]` then `t[i]` at the same length) each match
        // the compare that dominates them before any of them is stripped.
        let elims = find_eliminations(func, self.pointer_reload || bce_pointer_reload_enabled());
        if elims.is_empty() {
            return changed;
        }

        for elim in &elims {
            apply_elimination(func, elim);
        }
        self.last_run_eliminations += elims.len();

        // Delete any trap block that lost its last predecessor, then restore the
        // contiguous block-id range the regalloc replay requires.
        cleanup_orphan_traps(func, &elims);

        true
    }
}

/// Opt-in gate for the carrier-aware arm: set `TCG_X86_BCE_CARRIER=1` to
/// enable. Default OFF; `TCG_X86_BCE_CARRIER_DEBUG=1` traces every accept/decline
/// decision.
///
/// CORRECTNESS is validated (2026-07-18): full 18-bench suite clean, an
/// adversarial bounds corpus (own-length forward, `a[i-1]`, nested 2-D,
/// runtime-bound-that-must-NOT-eliminate, explicit OOB, reverse iteration,
/// guard-on-a-different-variable, clamp-derived index) all MATCH LLVM, and an
/// OOB access still TRAPS identically arm-on vs arm-off (fail-safe posture keeps
/// every check it cannot machine-prove redundant). But it stays OFF because it
/// is a PERFORMANCE NEGATIVE: a controlled interleaved full-suite A/B measured
/// geomean(on)/(off) = 1.0165 (1.65% SLOWER — the eliminated `cmp; jae`
/// never-taken checks are ~free, and removing them perturbs downstream regalloc:
/// b12 crc32 +15%, b01 +8%, b04 +7%; the sorts are neutral). Do not re-flip on a
/// single-bench measurement — that was noise; the controlled A/B is the signal.
static BCE_CARRIER: std::sync::OnceLock<bool> = std::sync::OnceLock::new();

/// Install the CARRIER arm of x86 bounds-check elimination from a TRACKED compiler option, once. DEFAULT OFF.
///
/// Until 2026-09-30 the only channel was `TCG_X86_BCE_CARRIER`, and `trustc` refuses every `TCG_*`
/// variable before the backend loads, so this opt-in had never been measured through the
/// bridge. Three levers found the same way turned out to carry recorded numbers that no
/// longer reproduced, and a fourth (the vectorizer's reduction unroll factor) was leaving
/// 23% on the table, so an unmeasured opt-in here is an open question, not a settled one.
pub fn set_bce_carrier_enabled(enabled: bool) -> bool {
    match BCE_CARRIER.set(enabled) {
        Ok(()) => true,
        Err(requested) => BCE_CARRIER.get() == Some(&requested),
    }
}

fn bce_carrier_enabled() -> bool {
    if let Some(enabled) = BCE_CARRIER.get() {
        return *enabled;
    }
    std::env::var_os("TCG_X86_BCE_CARRIER").is_some()
}

// ===========================================================================
// Carrier-aware arm
//
// Bounds checks travel the whole pass pipeline as opaque, single-instruction
// `TrapBoundsCheckExact [base, index, Imm(K)]` proof carriers; they are only
// expanded into a real `cmp; jae trap` diamond AFTER every pass has run, so
// the diamond arm above can never see them, and its single-predecessor window
// could never reach a check whose proving guard is an OUTER loop header
// several CFG levels up.
//
// This arm deletes a carrier when the machine CFG itself proves the check
// redundant. A carrier at position `p` of block `C` testing `index <u K` is
// deleted ONLY when ALL of the following hold (any unproven condition keeps
// it — same fail-safe posture as the diamond arm):
//
// 1. `index` canonicalizes (single-def MovRR/MovRR32 copies) to a root vreg
//    `r`, and its copy chain has depth <= 1 with the copy defined in `C`
//    before `p` (or `index` IS `r`).
// 2. Some strict dominator `D` of `C` ends in `CmpRI/CmpRI8 (op0, Imm(K'));
//    Jcc cc` where `canon(op0) == r` (same depth<=1 chain rule, copy defined
//    in `D` before the compare), `0 <= K' <= i32::MAX`, and `cc` is an
//    unsigned bound (`B`/`AE`/`BE`/`A`). The successor `T` on which the bound
//    holds (`B`: taken; `AE`: fall-through; `BE`/`A`: the `<=` forms)
//    establishes `r <u K'` (or `r <=u K'`).
// 3. Bound implication: `K' <= K` for the strict form, `K' < K` for the
//    `<=` form (all immediates in `[0, i32::MAX]`, so sign/width coincide).
// 4. Edge-dominance: `T`'s ONLY predecessor is `D`, and `T` dominates `C` —
//    so every path to the carrier enters through the guarded edge.
// 5. No-redefinition: `r` has NO def in the guarded region — the blocks
//    forward-reachable from `T` avoiding `D` intersected with the blocks
//    backward-reachable from `C` avoiding `D` (with `C` sliced at `p`) — and
//    no def of `r` in `D` at/after the guard compare (nor between a guard-side
//    copy and the compare). Paths that leave through `D` (the loop latch
//    re-entering the header) re-establish the predicate before re-reaching
//    `T`, which is exactly why avoiding-`D` regions are the sound scan set.
//
// Deletion removes ONE instruction: no trap block exists yet (expansion mints
// them later), no successor edges change, no renumbering. The stale
// `guard_obligations` entry is inert — production feeds the kernel gate empty
// evidence, so nothing downstream consumes it.
// ===========================================================================

/// A candidate's canonical root plus every full-width copy link on the way:
/// follows single-def `MovRR` chains to a fixed point (the root is the first
/// multi-def vreg, parameter, or non-copy def) and records each link's def
/// site. The caller must prove every link's SNAPSHOT of the root is covered
/// by the guarded-region no-redefinition proof (each def dominated by the
/// guarded edge target, or anchored inside the guard block itself).
///
/// Width discipline (stricter than the diamond arm's `canon`): only `MovRR`
/// (64-bit) copies are followed — `MovRR32` truncates, and the carrier's
/// post-expansion compare is full-width, so a truncating link would let a
/// 32-bit guard fact "prove" a 64-bit bound. Same reason the caller requires
/// Gpr64 register class on the root and every link.
fn carrier_chain_root(
    single_def: &HashMap<VReg, (Block, usize)>,
    func: &X86ISelFunction,
    v: VReg,
) -> Option<(VReg, Vec<(Block, usize)>)> {
    let mut links: Vec<(Block, usize)> = Vec::new();
    let mut cur = v;
    for _ in 0..8 {
        match single_def.get(&cur) {
            // Multi-def (or never-defined arg) vreg: it is the root.
            None => return Some((cur, links)),
            Some(&(b, i)) => {
                let inst = func.blocks.get(&b)?.insts.get(i)?;
                match inst.opcode {
                    X86Opcode::MovRR => match inst.operands.get(1) {
                        Some(X86ISelOperand::VReg(s)) => {
                            if !matches!(s.class, trust_cg_ir::regs::RegClass::Gpr64) {
                                return None;
                            }
                            links.push((b, i));
                            cur = *s;
                        }
                        _ => return None,
                    },
                    // Defined by a non-copy (or truncating copy): the root.
                    _ => return Some((cur, links)),
                }
            }
        }
    }
    None // chain too deep — fail safe
}

/// A decoded guard bound: at `D`'s terminator, the branch decides
/// `op0 <cc> rhs`, with `cc`-true on `true_target`. `anchor_pos` is the
/// position of the REAL bound compare in `D` (the no-redefinition anchor).
struct GuardBound {
    cc: X86CondCode,
    op0: VReg,
    rhs: CmpRhs,
    true_target: Block,
    anchor_pos: usize,
}

/// Decode `D`'s terminator into a [`GuardBound`]. Two shapes:
///
/// 1. DIRECT (post-peephole fusion): `Cmp op0, rhs ; Jcc cc T` — the branch
///    condition IS the bound relation.
/// 2. MATERIALIZED BOOLEAN (the frontend's un-fused guard shape, same chain
///    the pure-call hoist's ≥1-trip interpreter walks): `Cmp op0, rhs ;
///    Setcc cc0 b ; [Movzx/MovRR/AndRI-1 b']* ; CmpRI b', 0 ; Jcc NE/E T` —
///    the branch tests the materialized boolean, so `cc0`-true holds on the
///    `NE`-taken (resp. `E`-fall-through) edge. Every chain link must be a
///    single-def 0/1-preserving op (`Setcc` writes 0/1; `Movzx`/`MovRR`/
///    `MovRR32` copy it; `AndRI ..,1` preserves it) defined in `D` strictly
///    between the real compare and the boolean test — anything else fails the
///    decode (fail-safe).
fn decode_guard_bound(
    func: &X86ISelFunction,
    single_def: &HashMap<VReg, (Block, usize)>,
    d: Block,
    cb: &CondBranch,
) -> Option<GuardBound> {
    // Shape 1: a direct bound compare.
    let is_bool_test =
        matches!(cb.rhs, CmpRhs::Imm(0)) && matches!(cb.cc, X86CondCode::NE | X86CondCode::E);
    if !is_bool_test {
        return Some(GuardBound {
            cc: cb.cc,
            op0: cb.op0,
            rhs: cb.rhs,
            true_target: cb.jcc_target,
            anchor_pos: cb.cmp_pos,
        });
    }
    // Shape 2: walk the boolean back to its Setcc, staying inside `D` and
    // strictly before the boolean test.
    let insts = &func.blocks.get(&d)?.insts;
    let mut v = cb.op0;
    let mut setcc: Option<(usize, X86CondCode)> = None;
    for _ in 0..8 {
        let &(db, di) = single_def.get(&v)?;
        if db != d || di >= cb.cmp_pos {
            return None;
        }
        let inst = insts.get(di)?;
        match inst.opcode {
            X86Opcode::Setcc => {
                let [X86ISelOperand::VReg(_), X86ISelOperand::CondCode(cc0)] =
                    inst.operands.as_slice()
                else {
                    return None;
                };
                setcc = Some((di, *cc0));
                break;
            }
            X86Opcode::Movzx | X86Opcode::MovzxW | X86Opcode::MovRR | X86Opcode::MovRR32 => {
                let Some(X86ISelOperand::VReg(s)) = inst.operands.get(1) else {
                    return None;
                };
                v = *s;
            }
            X86Opcode::AndRI => {
                let [
                    X86ISelOperand::VReg(_),
                    X86ISelOperand::VReg(s),
                    X86ISelOperand::Imm(1),
                ] = inst.operands.as_slice()
                else {
                    return None;
                };
                v = *s;
            }
            _ => return None,
        }
    }
    let (setcc_pos, cc0) = setcc?;
    // The real bound compare must IMMEDIATELY precede the Setcc (its flag
    // producer), exactly as parse_cond_branch requires for the boolean test.
    let real_pos = setcc_pos.checked_sub(1)?;
    let real = insts.get(real_pos)?;
    let (op0, rhs) = match real.opcode {
        X86Opcode::CmpRR => match real.operands.as_slice() {
            [X86ISelOperand::VReg(a), X86ISelOperand::VReg(b)] => (*a, CmpRhs::Reg(*b)),
            _ => return None,
        },
        X86Opcode::CmpRI | X86Opcode::CmpRI8 => match real.operands.as_slice() {
            [X86ISelOperand::VReg(a), X86ISelOperand::Imm(c)] => (*a, CmpRhs::Imm(*c)),
            _ => return None,
        },
        _ => return None,
    };
    // Branch NE-taken = boolean true = cc0 held; E-taken = boolean false.
    let true_target = if cb.cc == X86CondCode::NE {
        cb.jcc_target
    } else {
        // `E`: the cc0-true edge is the OTHER successor.
        func.blocks
            .get(&d)?
            .successors
            .iter()
            .copied()
            .find(|s| *s != cb.jcc_target)?
    };
    Some(GuardBound {
        cc: cc0,
        op0,
        rhs,
        true_target,
        anchor_pos: real_pos,
    })
}

/// True iff `root` is defined anywhere in the avoiding-`D` region between the
/// guarded edge target `t` and the carrier at `(c_blk, p)`, or inside `D`
/// at/after `d_from` (the guard compare or the guard-side copy position).
#[derive(Clone, Copy)]
struct GuardedCarrierRegion {
    guarded_target: Block,
    carrier_block: Block,
    carrier_position: usize,
    guard_block: Block,
    guard_scan_start: usize,
}

fn carrier_region_redefines_root(
    func: &X86ISelFunction,
    cfg: &CfgAnalysis<Block>,
    region: GuardedCarrierRegion,
    root: VReg,
) -> bool {
    let GuardedCarrierRegion {
        guarded_target: t,
        carrier_block: c_blk,
        carrier_position: p,
        guard_block: d,
        guard_scan_start: d_from,
    } = region;
    // Forward reachability from `t`, never entering `d`.
    let mut fwd: HashSet<Block> = HashSet::default();
    let mut work: VecDeque<Block> = VecDeque::new();
    fwd.insert(t);
    work.push_back(t);
    while let Some(b) = work.pop_front() {
        let Some(block) = func.blocks.get(&b) else {
            continue;
        };
        for &s in &block.successors {
            if s != d && fwd.insert(s) {
                work.push_back(s);
            }
        }
    }
    // Backward reachability from `c_blk`, never entering `d`.
    let mut bwd: HashSet<Block> = HashSet::default();
    work.clear();
    bwd.insert(c_blk);
    work.push_back(c_blk);
    while let Some(b) = work.pop_front() {
        for &pr in cfg.preds.get(&b).map(|v| v.as_slice()).unwrap_or(&[]) {
            if pr != d && bwd.insert(pr) {
                work.push_back(pr);
            }
        }
    }
    // Scan the intersection for defs of `root` (slice `c_blk` at `p`).
    for &b in fwd.intersection(&bwd) {
        let Some(block) = func.blocks.get(&b) else {
            continue;
        };
        for (i, inst) in block.insts.iter().enumerate() {
            if b == c_blk && i >= p {
                break;
            }
            if inst_def_vreg(inst) == Some(root) {
                return true;
            }
        }
    }
    // Defs of `root` inside `D` at/after the guard-side anchor.
    if let Some(block) = func.blocks.get(&d) {
        for inst in block.insts.iter().skip(d_from) {
            if inst_def_vreg(inst) == Some(root) {
                return true;
            }
        }
    }
    false
}

/// Find every provably-redundant `TrapBoundsCheckExact` carrier. See the
/// module-section comment above for the exact soundness conditions.
fn find_carrier_eliminations(func: &X86ISelFunction) -> Vec<(Block, usize)> {
    let dbg = std::env::var_os("TCG_X86_BCE_CARRIER_DEBUG").is_some();
    macro_rules! trace {
        ($($a:tt)*) => { if dbg { eprintln!("[bce-carrier] {}", format!($($a)*)); } };
    }
    const MAXI: i64 = i32::MAX as i64;

    let cfg = CfgAnalysis::compute(func);
    let single_def = build_single_def_index(func);
    let mut out: Vec<(Block, usize)> = Vec::new();

    for &c_blk in &func.block_order {
        let Some(cblock) = func.blocks.get(&c_blk) else {
            continue;
        };
        'carrier: for (p, inst) in cblock.insts.iter().enumerate() {
            if inst.opcode != X86Opcode::TrapBoundsCheckExact {
                continue;
            }
            if inst.proof_origin.is_some() {
                continue;
            }
            let [_, X86ISelOperand::VReg(idx), X86ISelOperand::Imm(k)] = inst.operands.as_slice()
            else {
                continue;
            };
            let (k, idx) = (*k, *idx);
            if !(0..=MAXI).contains(&k) {
                continue;
            }
            // Full-depth chain: idx follows single-def MovRR links to a root.
            // Each link's snapshot-location constraint is guard-relative, so
            // links are validated inside the dominator walk below.
            let Some((root, idx_links)) = carrier_chain_root(&single_def, func, idx) else {
                continue;
            };
            if idx_links.iter().any(|&(cb, ci)| cb == c_blk && ci >= p) {
                trace!("{c_blk:?}[{p}] decline: index copy after carrier in C");
                continue;
            }

            // Width discipline: the carrier's expansion compares full-width,
            // so the guard fact must be a full-width fact. Gpr64 roots only.
            if !matches!(root.class, trust_cg_ir::regs::RegClass::Gpr64) {
                trace!("{c_blk:?}[{p}] decline: root {root:?} not Gpr64");
                continue;
            }

            // Walk strict dominators of C looking for a proving guard.
            let mut d = c_blk;
            for _hop in 0..64 {
                let Some(&up) = cfg.idom.get(&d) else { break };
                if up == d {
                    break;
                }
                d = up;
                let Some(cb) = parse_cond_branch(func, d) else {
                    continue;
                };
                // Decode the guard (direct compare or materialized-boolean
                // chain) into the effective bound relation at D's terminator.
                let Some(gb) = decode_guard_bound(func, &single_def, d, &cb) else {
                    continue;
                };
                // Bound value: an immediate, or a full-width register compare
                // against a constant-materialized (single-def MovRI) vreg —
                // the pre-peephole header shape.
                let kp = match gb.rhs {
                    CmpRhs::Imm(kp) => kp,
                    CmpRhs::Reg(rv) => {
                        if !matches!(rv.class, trust_cg_ir::regs::RegClass::Gpr64) {
                            continue;
                        }
                        let Some(m) = single_def
                            .get(&rv)
                            .and_then(|&(b, i)| func.blocks.get(&b)?.insts.get(i))
                        else {
                            continue;
                        };
                        if m.opcode != X86Opcode::MovRI {
                            continue;
                        }
                        match m.operands.as_slice() {
                            [X86ISelOperand::VReg(_), X86ISelOperand::Imm(c)] => *c,
                            _ => continue,
                        }
                    }
                };
                if !(0..=MAXI).contains(&kp) {
                    continue;
                }
                let Some((g_root, g_links)) = carrier_chain_root(&single_def, func, gb.op0) else {
                    continue;
                };
                if g_root != root {
                    continue;
                }
                if !matches!(gb.op0.class, trust_cg_ir::regs::RegClass::Gpr64) {
                    continue;
                }
                // Guard-side anchor: the real compare, tightened by any chain
                // link captured inside D — no def of root may follow it there.
                // Every guard-side link must live in D before the compare (the
                // guard's snapshot must be taken on the guard's own path).
                let mut d_from = gb.anchor_pos;
                let mut g_ok = true;
                for &(gbk, gi) in &g_links {
                    if gbk != d || gi >= gb.anchor_pos {
                        g_ok = false;
                        break;
                    }
                    d_from = d_from.min(gi);
                }
                if !g_ok {
                    continue;
                }
                // Index-chain links captured in D fold into the same anchor;
                // links elsewhere are validated against `t` below.
                for &(cbk, ci) in &idx_links {
                    if cbk == d {
                        d_from = d_from.min(ci);
                    }
                }
                // Which successor carries the bound, and its strength.
                let other = func
                    .blocks
                    .get(&d)
                    .and_then(|b| b.successors.iter().copied().find(|s| *s != gb.true_target));
                let (t, strict) = match gb.cc {
                    X86CondCode::B => (gb.true_target, true),
                    X86CondCode::AE => match other {
                        Some(f) => (f, true),
                        None => continue,
                    },
                    X86CondCode::BE => (gb.true_target, false),
                    X86CondCode::A => match other {
                        Some(f) => (f, false),
                        None => continue,
                    },
                    _ => continue,
                };
                // Bound implication over non-negative immediates.
                let implied = if strict { kp <= k } else { kp < k };
                if !implied {
                    continue;
                }
                // Edge-dominance: T's only predecessor is D, and T dominates C.
                match cfg.preds.get(&t).map(|v| v.as_slice()) {
                    Some([only]) if *only == d => {}
                    _ => continue,
                }
                if !cfg.dominates(t, c_blk) {
                    continue;
                }
                // Index-chain links (continued): outside D, every link's block
                // must be dominated by the guarded edge target so its snapshot
                // of `root` is inside the scanned region.
                if idx_links
                    .iter()
                    .any(|&(cbk, _)| cbk != d && !cfg.dominates(t, cbk))
                {
                    trace!("{c_blk:?}[{p}] decline: index chain link outside guard {d:?} region");
                    continue;
                }
                // No-redefinition scan over the guarded region.
                if carrier_region_redefines_root(
                    func,
                    &cfg,
                    GuardedCarrierRegion {
                        guarded_target: t,
                        carrier_block: c_blk,
                        carrier_position: p,
                        guard_block: d,
                        guard_scan_start: d_from,
                    },
                    root,
                ) {
                    trace!(
                        "{c_blk:?}[{p}] decline: root {root:?} redefined in guarded region (guard {d:?})"
                    );
                    continue;
                }
                trace!(
                    "{c_blk:?}[{p}] ELIMINATE: idx<u{k} proven by guard {d:?} ({}{kp}) via edge->{t:?}",
                    if strict { "<u" } else { "<=u" }
                );
                out.push((c_blk, p));
                continue 'carrier;
            }
            trace!("{c_blk:?}[{p}] decline: no proving dominator guard (K={k})");
        }
    }
    out
}

/// A validated elimination: rewrite `block`'s bounds-check terminator into an
/// unconditional jump to `safe_target`, dropping `trap_block`'s edge.
struct Elimination {
    /// The bounds-check block.
    block: Block,
    /// Index of the redundant `CmpRR` within `block`.
    cmp_pos: usize,
    /// The non-trap successor (the `cont` fall-through).
    safe_target: Block,
    /// The pure-`Ud2` trap successor whose edge is removed.
    trap_block: Block,
    /// True iff the redundant compare's flags are provably dead out of
    /// `safe_target`, so the compare itself may be removed.
    remove_compare: bool,
}

/// The right-hand operand of a comparison: another register, or an immediate.
#[derive(Clone, Copy, PartialEq, Eq)]
enum CmpRhs {
    Reg(VReg),
    Imm(i64),
}

/// A block terminated by `[.. ; Cmp(op0, rhs) ; Jcc(cc, jcc_target) ; [Jmp]]`,
/// where the compare is `CmpRR` (`rhs = Reg`) or `CmpRI`/`CmpRI8` (`rhs = Imm`).
struct CondBranch {
    cmp_pos: usize,
    /// The comparison opcode (`CmpRR` / `CmpRI` / `CmpRI8`). Identity requires
    /// the guard and the check to share this exact opcode.
    cmp_opcode: X86Opcode,
    op0: VReg,
    rhs: CmpRhs,
    cc: X86CondCode,
    jcc_target: Block,
}

/// Parse a block whose terminator is a compare-driven conditional branch.
///
/// Handles both the `Jcc + Jmp` explicit form and the `Jcc` + fall-through
/// form. The compare must be the instruction immediately preceding the `Jcc`
/// (the flag producer the branch consumes) and must be an unsigned-range-shaped
/// register/register or register/immediate integer compare. Returns `None`
/// (fail-safe) for anything else.
fn parse_cond_branch(func: &X86ISelFunction, block: Block) -> Option<CondBranch> {
    let insts = &func.blocks.get(&block)?.insts;
    let n = insts.len();
    if n < 2 {
        return None;
    }
    // Locate the terminating Jcc.
    let jcc_pos = if insts[n - 1].opcode == X86Opcode::Jcc {
        n - 1
    } else if insts[n - 1].opcode == X86Opcode::Jmp && insts[n - 2].opcode == X86Opcode::Jcc {
        n - 2
    } else {
        return None;
    };
    if jcc_pos == 0 {
        return None;
    }
    let cmp_pos = jcc_pos - 1;

    let cmp = &insts[cmp_pos];
    let (op0, rhs) = match cmp.opcode {
        X86Opcode::CmpRR => {
            let [X86ISelOperand::VReg(a), X86ISelOperand::VReg(b)] = cmp.operands.as_slice() else {
                return None;
            };
            (*a, CmpRhs::Reg(*b))
        }
        X86Opcode::CmpRI | X86Opcode::CmpRI8 => {
            let [X86ISelOperand::VReg(a), X86ISelOperand::Imm(imm)] = cmp.operands.as_slice()
            else {
                return None;
            };
            (*a, CmpRhs::Imm(*imm))
        }
        _ => return None,
    };

    let jcc = &insts[jcc_pos];
    let [
        X86ISelOperand::CondCode(cc),
        X86ISelOperand::Block(jcc_target),
    ] = jcc.operands.as_slice()
    else {
        return None;
    };

    Some(CondBranch {
        cmp_pos,
        cmp_opcode: cmp.opcode,
        op0,
        rhs,
        cc: *cc,
        jcc_target: *jcc_target,
    })
}

// The pure-trap predicate (condition 1 of the module doc) is the shared
// `crate::x86_trap_block::is_pure_trap_block`: a no-successor block that is
// exactly `[Ud2]` (ISel's `emit_synthetic_trap_block`, the fail edge of an
// unfused MIR `Assert`) or `[Call abort, Ud2]` (the bridge's shared
// panic=abort assert block, `emit_panic_abort_trap`, which every intercepted
// `Vec`/slice index check under panic=abort branches to). Both diverge, so an
// eliminated edge into either can only change how a never-failing check
// would have died, never what a passing program computes.

/// The vreg an instruction defines, if it produces a value into one.
fn inst_def_vreg(inst: &X86ISelInst) -> Option<VReg> {
    if !x86_produces_value(inst.opcode) {
        return None;
    }
    // Proof-only guard carriers (TrapBoundsCheckExact etc.) carry the checked
    // vreg in operand[0] but never write a register (the post-pipeline
    // expansion emits only compare+branch). Counting them as defs poisons the
    // single-def index for exactly the bounds-checked vregs this pass reasons
    // about. Pass-local exclusion, mirroring x86_licm/x86_strength_reduce
    // (commit 6878cf2); the global x86_produces_value stays untouched.
    if trust_cg_ir::guard_target::classify_x86_carrier(inst.opcode).is_some() {
        return None;
    }
    match inst.operands.first() {
        Some(X86ISelOperand::VReg(v)) => Some(*v),
        _ => None,
    }
}

/// Follow single-def `MovRR`/`MovRR32` copy chains to a canonical root vreg.
/// Value-preserving: a copy carries its source's value, so two syntactic uses
/// that canonicalize equal denote the same runtime value.
fn canon(single_def: &HashMap<VReg, (Block, usize)>, func: &X86ISelFunction, mut v: VReg) -> VReg {
    for _ in 0..64 {
        let Some(&(b, i)) = single_def.get(&v) else {
            return v;
        };
        let Some(inst) = func.blocks.get(&b).and_then(|blk| blk.insts.get(i)) else {
            return v;
        };
        match inst.opcode {
            X86Opcode::MovRR | X86Opcode::MovRR32 => {
                if let Some(X86ISelOperand::VReg(s)) = inst.operands.get(1) {
                    v = *s;
                    continue;
                }
                return v;
            }
            _ => return v,
        }
    }
    v
}

/// True iff a definition at `(b, i)` lies strictly inside the "covered window"
/// between the guard's compare and the check's compare — the code that provably
/// executes on the single `db -> bb` edge (`db` is `bb`'s unique predecessor):
/// `db`'s tail (instructions after `db_cmp_pos`) and `bb`'s head (instructions
/// before `bb_cmp_pos`). This is the SAME region [`operand_redefined_between`]
/// scans.
#[derive(Clone, Copy)]
struct CoveredWindow {
    guard_block: Block,
    guard_compare: usize,
    check_block: Block,
    check_compare: usize,
}

fn def_in_covered_window(b: Block, i: usize, window: CoveredWindow) -> bool {
    (b == window.guard_block && i > window.guard_compare)
        || (b == window.check_block && i < window.check_compare)
}

/// True iff every `MovRR`/`MovRR32` copy on the single-def chain from `v` up to
/// `root` was DEFINED inside the covered window (see [`def_in_covered_window`]).
///
/// A copy captured inside the window snapshotted `root`'s value at a point the
/// caller's window redefinition scan also covers — so if `root` is not
/// redefined in the window, the copy equals `root`'s value at BOTH compares. A
/// copy captured OUTSIDE the window may hold a stale `root` value the scan never
/// sees, so it is rejected (fail-safe). Reaching `root` itself (no copy) is
/// trivially fine.
fn copy_chain_captured_in_window(
    single: &HashMap<VReg, (Block, usize)>,
    func: &X86ISelFunction,
    mut v: VReg,
    root: VReg,
    window: CoveredWindow,
) -> bool {
    for _ in 0..64 {
        if v == root {
            return true;
        }
        let Some(&(b, i)) = single.get(&v) else {
            return false;
        };
        let Some(inst) = func.blocks.get(&b).and_then(|blk| blk.insts.get(i)) else {
            return false;
        };
        match inst.opcode {
            X86Opcode::MovRR | X86Opcode::MovRR32 => {
                if !def_in_covered_window(b, i, window) {
                    return false;
                }
                match inst.operands.get(1) {
                    Some(X86ISelOperand::VReg(s)) => v = *s,
                    _ => return false,
                }
            }
            _ => return false,
        }
    }
    false
}

// ---------------------------------------------------------------------------
// Case 4 support: two loads that RELOAD the same frame location
// ---------------------------------------------------------------------------
//
// A `&[T]` passes `len` in a register, so the guard and the bounds check read
// ONE vreg and cases 1-3 above match. A `Vec`/`String` keeps `len` in its
// header, so `while k < v.len() { .. v[k] .. }` RELOADS it: the guard compares
// against one load's result and the check against a second, textually distinct
// load. Those are different vregs with different roots, so cases 1-3 all
// decline and the redundant check survives -- which is why this pass fired on
// slices and not on the commonest owning-container loop in Rust.
//
// Two loads denote the same value when they read the same bytes and nothing
// between them may have written those bytes. Both halves are proved here
// STATICALLY or the case is declined; there is no optimistic arm, because a
// wrongly-removed bounds check is memory unsafety.

/// Byte width of a width-known scalar frame access, or `None` for any opcode
/// this pass will not reason about (vector, extending, SIB, `Push`/`Pop`, ...).
///
/// `None` is a REFUSAL, not a default: an unknown width cannot be range-checked
/// for overlap, so every caller declines on it.
fn frame_access_bytes(op: X86Opcode) -> Option<u32> {
    Some(match op {
        X86Opcode::MovRM8 | X86Opcode::MovzxRM8 | X86Opcode::MovMR8 => 1,
        X86Opcode::MovRM16 | X86Opcode::MovzxRM16 | X86Opcode::MovMR16 => 2,
        X86Opcode::MovRM32 | X86Opcode::MovMR32 => 4,
        X86Opcode::MovRM | X86Opcode::MovMR => 8,
        _ => return None,
    })
}

/// A statically-resolved frame location: a fixed byte range inside ONE named
/// stack slot. Two `FrameRef`s in DIFFERENT slots can never alias, because
/// frame lowering assigns each slot a disjoint region of the frame.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct FrameRef {
    slot: u32,
    off: i64,
    bytes: u32,
}

impl FrameRef {
    /// True iff the two byte ranges intersect. Different slots never do; within
    /// one slot this is an exact half-open interval overlap, so a store to a
    /// `Vec`'s `ptr` field does not block a reload of its `len` field.
    fn overlaps(self, other: Self) -> bool {
        self.slot == other.slot
            && self.off < other.off.saturating_add(i64::from(other.bytes))
            && other.off < self.off.saturating_add(i64::from(self.bytes))
    }
}

/// Resolve a load/store address operand to the frame bytes it touches, or
/// `None` when that is not statically provable.
///
/// Accepted forms -- exactly the two the x86 selector emits for a frame local,
/// plus the `Lea` root form SROA documents:
///
/// * `StackSlot(s)` -> slot `s` at offset 0.
/// * `MemAddr { base: StackSlot(s), disp }` -> slot `s` at `disp`.
/// * `MemAddr { base: VReg(v), disp }` where `v` canonicalizes (through
///   value-preserving `MovRR` copies) to a SINGLE-DEF `Lea r, [StackSlot(s) +
///   d0]` -> slot `s` at `d0 + disp`.
///
/// Everything else is `None`: a SIB address (a runtime index could land
/// anywhere), a register base that is not such a `Lea` (it could hold any
/// pointer, including into the heap), a RIP-relative or symbol address, and a
/// multi-def base. Callers treat `None` as "may alias anything".
fn resolve_frame_ref(
    single: &HashMap<VReg, (Block, usize)>,
    func: &X86ISelFunction,
    addr: &X86ISelOperand,
    bytes: u32,
) -> Option<FrameRef> {
    match addr {
        X86ISelOperand::StackSlot(s) => Some(FrameRef {
            slot: *s,
            off: 0,
            bytes,
        }),
        X86ISelOperand::MemAddr { base, disp } => match base.as_ref() {
            X86ISelOperand::StackSlot(s) => Some(FrameRef {
                slot: *s,
                off: i64::from(*disp),
                bytes,
            }),
            X86ISelOperand::VReg(v) => {
                let (slot, off) = resolve_frame_address_reg(single, func, *v)?;
                Some(FrameRef {
                    slot,
                    off: off.saturating_add(i64::from(*disp)),
                    bytes,
                })
            }
            _ => None,
        },
        _ => None,
    }
}

/// Resolve a register that holds a frame ADDRESS to the `(slot, offset)` it
/// points at, following a CHAIN of slot-based `Lea`s to a fixed point.
///
/// The chain matters. `Lea a, [StackSlot(s) + 0]` followed by
/// `Lea b, [a + 16]` is how the selector spells the address of a FIELD of a
/// frame local -- a `Vec` header's `len` at `[vec + 16]` is exactly this. A
/// resolver that follows only ONE `Lea` sees `b` as opaque and declines, which
/// is precisely the case that made the reloaded-length arm miss the shape it was
/// written for.
///
/// Value-preserving `MovRR` copies are followed via [`canon`]. Anything else --
/// a `LeaSib` (its index is a runtime value, so the address is not fixed), a
/// non-`Lea` definition, a multi-def register, or a chain longer than the bound
/// -- returns `None`, which callers read as "may alias anything".
fn resolve_frame_address_reg(
    single: &HashMap<VReg, (Block, usize)>,
    func: &X86ISelFunction,
    v: VReg,
) -> Option<(u32, i64)> {
    let mut cur = v;
    let mut off: i64 = 0;
    for _ in 0..8 {
        let root = canon(single, func, cur);
        let &(b, i) = single.get(&root)?;
        let inst = func.blocks.get(&b)?.insts.get(i)?;
        if inst.opcode != X86Opcode::Lea {
            return None;
        }
        let X86ISelOperand::MemAddr { base, disp } = inst.operands.get(1)? else {
            return None;
        };
        off = off.saturating_add(i64::from(*disp));
        match base.as_ref() {
            X86ISelOperand::StackSlot(s) => return Some((*s, off)),
            X86ISelOperand::VReg(next) => cur = *next,
            _ => return None,
        }
    }
    None
}

/// True iff NO instruction executed strictly between the two load sites may
/// write `target`.
///
/// `window.check_block`'s unique predecessor is `window.guard_block`, so the
/// only code between a load in the guard block and a load in the check block is
/// the guard block's tail after the first load plus the check block's head
/// before the second. Only two placements are admitted -- both loads in the
/// guard block, or guard-block load then check-block load -- and any other
/// (either load in a third block, or the check's load textually before the
/// guard's within one block) returns `false` rather than guessing at the path.
///
/// An instruction passes when it is `Pure`, a `Load` (a read cannot clobber),
/// or a `Store` whose destination resolves to a frame range DISJOINT from
/// `target`. It fails on a `Call` -- which by `x86_opcode_effect` also covers
/// every volatile access -- on `Push`/`Pop` (they move `rsp`), on a store whose
/// width or address does not resolve, and on a store that overlaps.
fn no_aliasing_write_between(
    single: &HashMap<VReg, (Block, usize)>,
    func: &X86ISelFunction,
    guard_load: (Block, usize),
    check_load: (Block, usize),
    target: FrameRef,
    window: CoveredWindow,
) -> bool {
    let (gb, gi) = guard_load;
    let (cb, ci) = check_load;
    // The guard's load feeds the guard compare, so it must precede it.
    if gb != window.guard_block || gi >= window.guard_compare {
        return false;
    }
    // Half-open [lo, hi) ranges of instructions that lie between the loads.
    let ranges: Vec<(Block, usize, usize)> = if cb == window.guard_block {
        if ci <= gi {
            return false;
        }
        vec![(window.guard_block, gi + 1, ci)]
    } else if cb == window.check_block {
        if ci >= window.check_compare {
            return false;
        }
        let Some(guard_block) = func.blocks.get(&window.guard_block) else {
            return false;
        };
        vec![
            (window.guard_block, gi + 1, guard_block.insts.len()),
            (window.check_block, 0, ci),
        ]
    } else {
        return false;
    };

    for (b, lo, hi) in ranges {
        let Some(block) = func.blocks.get(&b) else {
            return false;
        };
        for inst in block.insts.iter().take(hi.min(block.insts.len())).skip(lo) {
            if matches!(inst.opcode, X86Opcode::Push | X86Opcode::Pop) {
                return false;
            }
            match x86_opcode_effect(inst.opcode) {
                MemoryEffect::Pure | MemoryEffect::Load => {}
                MemoryEffect::Store => {
                    let Some(bytes) = frame_access_bytes(inst.opcode) else {
                        return false;
                    };
                    let Some(dst) = inst
                        .operands
                        .first()
                        .and_then(|o| resolve_frame_ref(single, func, o, bytes))
                    else {
                        return false;
                    };
                    if dst.overlaps(target) {
                        return false;
                    }
                }
                MemoryEffect::Call => return false,
            }
        }
    }
    true
}

/// Case 4: prove two DISTINCT load-defined vregs hold the same value because
/// they reload the same frame bytes with no aliasing write between.
///
/// Returns the guard-side vreg as the shared "root". That is honest for the
/// caller's redefinition scan: both vregs are single-def here, so neither can
/// be redefined in the covered window and the scan is a trivially-passing
/// no-op. Memory stability -- the condition that actually matters for a reload
/// -- is proved by [`no_aliasing_write_between`], not by that scan.
fn same_value_by_frame_reload(
    single: &HashMap<VReg, (Block, usize)>,
    func: &X86ISelFunction,
    guard_v: VReg,
    check_v: VReg,
    window: CoveredWindow,
) -> Option<VReg> {
    let &(gb, gi) = single.get(&guard_v)?;
    let &(cb, ci) = single.get(&check_v)?;
    let guard_load = func.blocks.get(&gb)?.insts.get(gi)?;
    let check_load = func.blocks.get(&cb)?.insts.get(ci)?;
    // Identical opcode: same access width AND same load kind, so the two reads
    // return the same bytes interpreted the same way.
    if guard_load.opcode != check_load.opcode {
        return None;
    }
    if x86_opcode_effect(guard_load.opcode) != MemoryEffect::Load {
        return None;
    }
    let bytes = frame_access_bytes(guard_load.opcode)?;
    let ga = resolve_frame_ref(single, func, guard_load.operands.get(1)?, bytes)?;
    let ca = resolve_frame_ref(single, func, check_load.operands.get(1)?, bytes)?;
    if ga != ca {
        return None;
    }
    if !no_aliasing_write_between(single, func, (gb, gi), (cb, ci), ga, window) {
        return None;
    }
    Some(guard_v)
}

/// Case 5: prove two DISTINCT load-defined vregs hold the same value because they
/// load from the SAME POINTER at the same displacement with NO STORE between.
///
/// Case 4 ([`same_value_by_frame_reload`]) resolves both addresses to frame bytes
/// via [`resolve_frame_ref`]. That misses the shape an OWNING container actually
/// presents once its header address is materialized into a register:
///
/// ```text
/// preheader:  lea  rdi, [slot_ptr + 16]     ; &v.len
///             mov  rsi, rdi                 ; a plain copy
/// guard:      mov  rax, [rdi + 0]           ; the while condition's length
///             cmp  rbx, rax ; jae exit
/// check:      mov  rax, [rsi + 0]           ; the bounds check's length
///             cmp  rcx, rax ; jae panic
/// ```
///
/// Here `resolve_frame_ref` cannot classify either load — the address is a
/// computed pointer, not `[rbp + disp]` — so case 4 declines, although the two
/// loads read *the same address*: `rsi` is one `MovRR` from `rdi`, which
/// [`canon`] already follows.
///
/// # Why this is sound, and where it is deliberately stricter than case 4
///
/// * **Same address.** Both loads must carry `MemAddr { base, disp }` whose
///   canonical bases are the SAME vreg and whose displacements are equal. Same
///   base register plus same displacement is the same address, whatever it points
///   to — no aliasing question arises, because it is one location, not two.
/// * **The address cannot move.** The shared canonical base must be single-def
///   function-wide, so nothing can redefine it anywhere, let alone between the
///   loads. (Case 4 gets this from frame identity; here it is the register.)
/// * **Identical opcode**, so both reads return the same bytes interpreted the
///   same way — the same condition case 4 imposes.
/// * **NO STORE AT ALL between the loads**, not merely no *aliasing* store. Case 4
///   can compare a store's frame target against its own, because it resolved both
///   to frame refs; this arm has no such target to compare against, so it refuses
///   on ANY store, call, `Push` or `Pop` in the region. That is strictly stronger
///   than case 4's test and it is what discharges "the memory did not change".
///   It is exactly the premise upstream named as missing when it declined to
///   assume a write-free loop was enough: the concern was "a store may separate
///   the trip-bound load from the element guard's reload", and this scans the
///   region between them for precisely that.
/// * **The region is the one already modeled.** [`region_between_loads`] is the
///   same two-range path [`no_aliasing_write_between`] walks: from just after the
///   guard load to the end of the guard block, then from the top of the check
///   block to the check load. The caller's [`CoveredWindow`] guarantees the guard
///   block's compare dominates the check block and that this is the path taken,
///   so there is no other route between the two loads to account for.
///
/// DEFAULT OFF. This is bounds-check elimination: a wrong answer is a memory
/// safety defect, not a slow program. `-Ztrust-ir-cg-args=x86-bce-ptr-reload` is
/// the opt-in, and `no-x86-bce-ptrreload` cannot be the lever because the arm is
/// not on to begin with.
fn same_value_by_pointer_reload(
    single: &HashMap<VReg, (Block, usize)>,
    func: &X86ISelFunction,
    guard_v: VReg,
    check_v: VReg,
    window: CoveredWindow,
) -> Option<VReg> {
    let &(gb, gi) = single.get(&guard_v)?;
    let &(cb, ci) = single.get(&check_v)?;
    let guard_load = func.blocks.get(&gb)?.insts.get(gi)?;
    let check_load = func.blocks.get(&cb)?.insts.get(ci)?;
    if guard_load.opcode != check_load.opcode {
        return None;
    }
    if x86_opcode_effect(guard_load.opcode) != MemoryEffect::Load {
        return None;
    }
    let (gbase, gdisp) = plain_mem_base_disp(guard_load.operands.get(1)?)?;
    let (cbase, cdisp) = plain_mem_base_disp(check_load.operands.get(1)?)?;
    if gdisp != cdisp {
        return None;
    }
    let root = canon(single, func, gbase);
    if root != canon(single, func, cbase) {
        return None;
    }
    // The shared address register must be unique-def function-wide, so it cannot
    // be redefined between the two loads (or anywhere else).
    if !single.contains_key(&root) {
        return None;
    }
    if !no_store_between_loads(func, (gb, gi), (cb, ci), window) {
        return None;
    }
    Some(guard_v)
}

/// A `MemAddr { base: VReg, disp }` operand's `(base, disp)`. Refuses a SIB
/// operand: an index term makes the address depend on a second register this arm
/// does not reason about.
fn plain_mem_base_disp(op: &X86ISelOperand) -> Option<(VReg, i32)> {
    match op {
        X86ISelOperand::MemAddr { base, disp } => match base.as_ref() {
            X86ISelOperand::VReg(b) => Some((*b, *disp)),
            _ => None,
        },
        _ => None,
    }
}

/// The half-open instruction ranges strictly between two loads along the covered
/// window's path. `None` when the two loads do not lie on that path in that
/// order. Shared shape with [`no_aliasing_write_between`], kept separate so that
/// function's frame-target test is not weakened.
fn region_between_loads(
    func: &X86ISelFunction,
    guard_load: (Block, usize),
    check_load: (Block, usize),
    window: CoveredWindow,
) -> Option<Vec<(Block, usize, usize)>> {
    let (gb, gi) = guard_load;
    let (cb, ci) = check_load;
    // The guard's load feeds the guard compare, so it must precede it.
    if gb != window.guard_block || gi >= window.guard_compare {
        return None;
    }
    if cb == window.guard_block {
        if ci <= gi {
            return None;
        }
        Some(vec![(window.guard_block, gi + 1, ci)])
    } else if cb == window.check_block {
        if ci >= window.check_compare {
            return None;
        }
        let guard_block = func.blocks.get(&window.guard_block)?;
        Some(vec![
            (window.guard_block, gi + 1, guard_block.insts.len()),
            (window.check_block, 0, ci),
        ])
    } else {
        None
    }
}

/// True when NO instruction between the two loads writes memory in any way.
///
/// Stricter than [`no_aliasing_write_between`] on purpose — see
/// [`same_value_by_pointer_reload`] for why this arm cannot compare a store's
/// target against its own and so must refuse every store.
fn no_store_between_loads(
    func: &X86ISelFunction,
    guard_load: (Block, usize),
    check_load: (Block, usize),
    window: CoveredWindow,
) -> bool {
    let Some(ranges) = region_between_loads(func, guard_load, check_load, window) else {
        return false;
    };
    for (b, lo, hi) in ranges {
        let Some(block) = func.blocks.get(&b) else {
            return false;
        };
        for inst in block.insts.iter().take(hi.min(block.insts.len())).skip(lo) {
            if matches!(inst.opcode, X86Opcode::Push | X86Opcode::Pop) {
                return false;
            }
            match x86_opcode_effect(inst.opcode) {
                MemoryEffect::Pure | MemoryEffect::Load => {}
                MemoryEffect::Store | MemoryEffect::Call => return false,
            }
        }
    }
    true
}

/// What [`same_value_operand`] proved, plus where the caller's redefinition scan
/// must START inside the guard block.
///
/// `guard_scan_from` is normally the guard's compare, because the covered window
/// begins just after it. Case 3b lowers it to the definition index of the
/// earliest guard-side copy, which is exactly what makes that copy's snapshot
/// provably equal to the root at BOTH compares.
#[derive(Clone, Copy)]
struct SameValue {
    root: VReg,
    guard_scan_from: usize,
}

/// Case 3b: the guard side reaches the root through copies defined in the GUARD
/// BLOCK before the guard compare.
///
/// Case 3 admits only "the guard uses the root directly", because a guard-side
/// copy feeds the guard compare and so can never lie inside the covered window.
/// Such a copy is not unprovable, though -- it is provable with a WIDER window.
/// If the root is not redefined anywhere between that copy's definition and the
/// check's compare, then the copy holds the root's value at the guard compare AND
/// the root still holds it at the check compare, so the two compares read one
/// value. This returns the earliest such definition index and the caller scans
/// from there instead of from the compare, which is what discharges the "not
/// redefined" side.
///
/// Requires every link to be a single-def `MovRR`/`MovRR32` defined in `db`
/// strictly before `guard_compare`. A link in any OTHER block is rejected:
/// proving "not redefined" along an arbitrary dominator path is not something
/// this scan does, and guessing is how a bounds check gets removed wrongly.
///
/// This is the shape a `while k < v.len() { .. v[k] .. }` loop actually presents
/// after the cleanup cluster -- both compares read a copy of the loop IV rather
/// than the IV itself.
fn guard_side_copy_scan_start(
    single: &HashMap<VReg, (Block, usize)>,
    func: &X86ISelFunction,
    mut v: VReg,
    root: VReg,
    window: CoveredWindow,
) -> Option<usize> {
    let mut earliest = window.guard_compare;
    for _ in 0..64 {
        if v == root {
            return Some(earliest);
        }
        let &(b, i) = single.get(&v)?;
        if b != window.guard_block || i >= window.guard_compare {
            return None;
        }
        let inst = func.blocks.get(&b)?.insts.get(i)?;
        match inst.opcode {
            X86Opcode::MovRR | X86Opcode::MovRR32 => {
                earliest = earliest.min(i);
                match inst.operands.get(1) {
                    Some(X86ISelOperand::VReg(s)) => v = *s,
                    _ => return None,
                }
            }
            _ => return None,
        }
    }
    None
}

/// Prove that `guard_v` (compared at the dominating guard) and `check_v`
/// (compared at the bounds check) denote the SAME runtime value, returning their
/// shared canonical root vreg if so, or `None` (fail-safe) otherwise.
///
/// Two vregs share a value when they canonicalize (through single-def
/// `MovRR`/`MovRR32` copies) to the same root `R` AND that equality is stable
/// across the guard->check region. Three sound cases:
///
/// 1. **Identical source vregs.** Both compares read the same vreg directly; the
///    caller's window redefinition scan on `R` then guarantees stability.
/// 2. **Single-def root.** `R` has one global definition, so any copies of it
///    hold one fixed value — divergent capture is impossible.
/// 3. **Multi-def root reached only through window-captured copies.** This is the
///    real loop shape: the guard compares the loop `iv` (a multi-def merge vreg)
///    DIRECTLY, while the bounds check compares a fresh single-def COPY of it
///    (`v_copy = mov iv`) materialised inside the loop body. That copy is defined
///    within the covered window, so together with the caller's "`R` not redefined
///    in the window" scan it provably equals `iv`'s value at BOTH compares. Any
///    copy captured OUTSIDE the window (a stale snapshot the scan cannot see) is
///    rejected — closing the divergent-capture hole while still firing on the
///    genuine own-length loop.
fn same_value_operand(
    single: &HashMap<VReg, (Block, usize)>,
    func: &X86ISelFunction,
    guard_v: VReg,
    check_v: VReg,
    window: CoveredWindow,
    pointer_reload: bool,
) -> Option<SameValue> {
    let r = canon(single, func, guard_v);
    if r != canon(single, func, check_v) {
        // Case 4: the roots genuinely differ, but both may be loads that RELOAD
        // the SAME frame bytes with no aliasing write between them -- the
        // owning-container (`Vec`/`String`) own-length loop. Proved statically
        // or declined; see `same_value_by_frame_reload`.
        if !bce_reload_enabled() {
            return None;
        }
        if let Some(root) = same_value_by_frame_reload(single, func, guard_v, check_v, window) {
            return Some(SameValue {
                root,
                guard_scan_from: window.guard_compare,
            });
        }
        // Case 5: not the same frame bytes, but the same POINTER at the same
        // displacement with no store between -- the owning-container shape once
        // its header address is in a register. See
        // [`same_value_by_pointer_reload`]. DEFAULT OFF.
        if pointer_reload {
            return same_value_by_pointer_reload(single, func, guard_v, check_v, window).map(
                |root| SameValue {
                    root,
                    guard_scan_from: window.guard_compare,
                },
            );
        }
        return None;
    }
    // Cases 1 & 2: identical vregs, or a single-def (globally-fixed) root.
    if guard_v == check_v || single.contains_key(&r) {
        return Some(SameValue {
            root: r,
            guard_scan_from: window.guard_compare,
        });
    }
    // Case 3: multi-def root. Every copy on BOTH chains to `r` must have been
    // captured inside the covered window (so the caller's redefinition scan on
    // `r` proves each snapshot equals `r` at both compares). Note a guard-side
    // copy would have to be defined before `db_cmp_pos` (it is USED at the guard
    // compare) and so can never be "in window" — this admits exactly the
    // guard-uses-root-directly / check-uses-window-copy shape and rejects the
    // rest.
    if !copy_chain_captured_in_window(single, func, check_v, r, window) {
        return None;
    }
    if copy_chain_captured_in_window(single, func, guard_v, r, window) {
        return Some(SameValue {
            root: r,
            guard_scan_from: window.guard_compare,
        });
    }
    // Case 3b: the guard side is a copy defined in the guard block BEFORE its
    // compare. Provable with a window widened back to that copy's definition.
    if bce_early_copy_enabled()
        && let Some(guard_scan_from) = guard_side_copy_scan_start(single, func, guard_v, r, window)
    {
        return Some(SameValue {
            root: r,
            guard_scan_from,
        });
    }
    None
}

/// Build the single-def index (vregs with EXACTLY one definition in the
/// function). A hit means "this vreg has a unique, globally-fixed value".
fn build_single_def_index(func: &X86ISelFunction) -> HashMap<VReg, (Block, usize)> {
    let mut counts: HashMap<VReg, u32> = HashMap::default();
    let mut single: HashMap<VReg, (Block, usize)> = HashMap::default();
    for block_id in &func.block_order {
        let Some(block) = func.blocks.get(block_id) else {
            continue;
        };
        for (idx, inst) in block.insts.iter().enumerate() {
            if let Some(v) = inst_def_vreg(inst) {
                *counts.entry(v).or_insert(0) += 1;
                single.insert(v, (*block_id, idx));
            }
        }
    }
    single.retain(|v, _| counts.get(v) == Some(&1));
    single
}

/// True iff `root0` or `root1` is redefined between `db`'s compare and `bb`'s
/// compare. Because `db` is `bb`'s direct and only predecessor, the only code
/// between the two compares is `db`'s tail (its branch instructions, after
/// `db_cmp_pos`) and `bb`'s head (before `bb_cmp_pos`). A def of a root vreg in
/// that window means its value may differ between the guard and the check, so
/// the elimination is rejected (fail-safe).
fn operand_redefined_between(
    func: &X86ISelFunction,
    db: Block,
    db_cmp_pos: usize,
    bb: Block,
    bb_cmp_pos: usize,
    roots: &[VReg],
) -> bool {
    if let Some(dblk) = func.blocks.get(&db) {
        for inst in dblk.insts.iter().skip(db_cmp_pos + 1) {
            if let Some(v) = inst_def_vreg(inst)
                && roots.contains(&v)
            {
                return true;
            }
        }
    }
    if let Some(bblk) = func.blocks.get(&bb) {
        for inst in bblk.insts.iter().take(bb_cmp_pos) {
            if let Some(v) = inst_def_vreg(inst)
                && roots.contains(&v)
            {
                return true;
            }
        }
    }
    false
}

/// True iff the RFLAGS produced by the bounds-check compare are dead along every
/// path out of `start` (the `cont` successor), so the compare may be removed.
///
/// Bounded forward walk: within each block, the first flag-READER encountered
/// (before any full flag overwrite) means the flags are live -> not dead (keep
/// the compare); a full overwrite makes them dead on that path (stop). A
/// block that neither reads nor fully clobbers before its terminator lets the
/// flags flow to its successors, which are then checked. A `visited` set bounds
/// the walk (loops terminate because a loop guard's own compare clobbers).
/// Reads are checked before writes so a read-modify-writes flag op (ADC/SBB)
/// counts as a reader.
fn compare_flags_dead_after(func: &X86ISelFunction, start: Block) -> bool {
    let mut visited: HashSet<Block> = HashSet::default();
    let mut queue: VecDeque<Block> = VecDeque::new();
    queue.push_back(start);
    while let Some(b) = queue.pop_front() {
        if !visited.insert(b) {
            continue;
        }
        let Some(block) = func.blocks.get(&b) else {
            // Unknown successor: cannot prove dead -> conservative "live".
            return false;
        };
        let mut clobbered = false;
        for inst in &block.insts {
            if x86_reads_flags(inst.opcode) {
                return false; // flags are live: keep the compare
            }
            if condition_flag_overwrite(inst) == FlagOverwrite::Full {
                clobbered = true; // clobbered before any read on this path
                break;
            }
        }
        if !clobbered {
            for &s in &block.successors {
                queue.push_back(s);
            }
        }
    }
    true
}

/// Find every provably-dead bounds-check diamond in `func`. See the module docs
/// for the four conditions that ALL must hold; anything unproven is skipped.
fn find_eliminations(func: &X86ISelFunction, pointer_reload: bool) -> Vec<Elimination> {
    let single = build_single_def_index(func);
    let cfg = CfgAnalysis::compute(func);
    let dbg = bce_trace_enabled();
    macro_rules! decline {
        ($bb:expr, $($t:tt)*) => {{
            if dbg {
                eprintln!("[bce] {}:{:?} decline: {}", func.name, $bb, format!($($t)*));
            }
            continue;
        }};
    }

    let mut elims: Vec<Elimination> = Vec::new();

    for &bb in &func.block_order {
        // (1) The bounds-check block ends in a CmpRR-driven conditional branch.
        let Some(check) = parse_cond_branch(func, bb) else {
            if dbg {
                let tail: Vec<_> = func
                    .blocks
                    .get(&bb)
                    .map(|b| b.insts.iter().rev().take(4).map(|i| i.opcode).collect())
                    .unwrap_or_default();
                eprintln!(
                    "[bce] {}:{bb:?} decline: not a CmpRR cond branch; tail={tail:?}",
                    func.name
                );
            }
            continue;
        };
        let Some(block) = func.blocks.get(&bb) else {
            continue;
        };
        if block.successors.len() != 2 {
            decline!(bb, "{} successors, not 2", block.successors.len());
        }
        // The two successors: the Jcc target and "the other".
        let jcc_target = check.jcc_target;
        let others: Vec<Block> = block
            .successors
            .iter()
            .copied()
            .filter(|&s| s != jcc_target)
            .collect();
        let [other_target] = others.as_slice() else {
            decline!(bb, "successor set is not {{jcc, one other}}");
        };
        let other_target = *other_target;

        // Exactly one successor must be a pure trap; the other is `cont`.
        let jcc_is_trap = is_pure_trap_block(func, jcc_target);
        let other_is_trap = is_pure_trap_block(func, other_target);
        let (trap_block, safe_target, safe_is_jcc) = match (jcc_is_trap, other_is_trap) {
            (true, false) => (jcc_target, other_target, false),
            (false, true) => (other_target, jcc_target, true),
            // Neither or both a trap: not a bounds-check diamond. No wildcard
            // optimism — keep the check.
            (false, false) => {
                if dbg {
                    let show = |b: Block| -> String {
                        func.blocks
                            .get(&b)
                            .map(|x| {
                                format!(
                                    "{b:?}{:?} succs={:?}",
                                    x.insts.iter().map(|i| i.opcode).collect::<Vec<_>>(),
                                    x.successors
                                )
                            })
                            .unwrap_or_else(|| format!("{b:?}<missing>"))
                    };
                    eprintln!(
                        "[bce] {}:{bb:?} decline: neither successor is a pure trap; jcc={} other={}",
                        func.name,
                        show(jcc_target),
                        show(other_target)
                    );
                }
                continue;
            }
            (true, true) => decline!(bb, "BOTH successors are pure traps"),
        };

        // The unsigned relation that must hold to reach `cont` (avoid the trap).
        let safe_cc = if safe_is_jcc {
            check.cc
        } else {
            check.cc.invert()
        };

        // (2) A single dominating predecessor that ends in a conditional branch.
        let empty: Vec<Block> = Vec::new();
        let preds = cfg.preds.get(&bb).unwrap_or(&empty);
        let [db] = preds.as_slice() else {
            decline!(bb, "check block has {} preds, not 1", preds.len());
        };
        let db = *db;
        if db == bb || !cfg.dominates(db, bb) {
            decline!(bb, "pred {db:?} does not dominate (or is self)");
        }
        let Some(guard) = parse_cond_branch(func, db) else {
            decline!(bb, "pred {db:?} is not a CmpRR conditional branch");
        };

        // The predicate the `db -> bb` edge establishes.
        let Some(dblock) = func.blocks.get(&db) else {
            continue;
        };
        let d_others: Vec<Block> = dblock
            .successors
            .iter()
            .copied()
            .filter(|&s| s != guard.jcc_target)
            .collect();
        let guard_cc = if bb == guard.jcc_target {
            guard.cc
        } else if d_others.as_slice() == [bb] {
            guard.cc.invert()
        } else {
            // `bb` is not cleanly one of `db`'s two edges: cannot attribute a
            // predicate to the edge -> keep the check.
            decline!(bb, "not cleanly one of {db:?}'s two edges");
        };

        // (3) Identical comparison: same compare opcode, same left operand
        // (through window-captured copies), same right operand (register through
        // window-captured copies, or an identical immediate), and the guard-taken
        // predicate is the SAME unsigned relation the check needs. Guard-taken
        // then implies bounds-safe.
        if check.cmp_opcode != guard.cmp_opcode {
            decline!(
                bb,
                "cmp opcode {:?} != guard {:?}",
                check.cmp_opcode,
                guard.cmp_opcode
            );
        }
        // Left operand: guard and check must compare the SAME value. Identical
        // vregs, a single-def root, or the loop-`iv` shape (guard uses the merge
        // vreg directly; check uses a copy of it captured inside the covered
        // window) match; a copy captured outside the window is rejected (see
        // `same_value_operand`).
        let covered_window = CoveredWindow {
            guard_block: db,
            guard_compare: guard.cmp_pos,
            check_block: bb,
            check_compare: check.cmp_pos,
        };
        let Some(lhs) = same_value_operand(
            &single,
            func,
            guard.op0,
            check.op0,
            covered_window,
            pointer_reload,
        ) else {
            decline!(
                bb,
                "lhs not same-value: guard {:?} vs check {:?}",
                guard.op0,
                check.op0
            );
        };
        // Right operand: register/register (same-value) or identical immediate.
        // Register-vs-immediate and immediate mismatch never match.
        let rhs = match (check.rhs, guard.rhs) {
            (CmpRhs::Reg(rc), CmpRhs::Reg(rg)) => {
                match same_value_operand(&single, func, rg, rc, covered_window, pointer_reload) {
                    Some(r) => Some(r),
                    None => decline!(bb, "rhs not same-value: guard {rg:?} vs check {rc:?}"),
                }
            }
            (CmpRhs::Imm(ic), CmpRhs::Imm(ig)) => {
                if ic != ig {
                    continue;
                }
                None
            }
            _ => continue,
        };
        if guard_cc != safe_cc {
            decline!(bb, "guard_cc {guard_cc:?} != safe_cc {safe_cc:?}");
        }

        // (4) Neither operand's shared root vreg redefined between the guard and
        // the check (the covered window: `db`'s tail + `bb`'s head, `db` being
        // `bb`'s unique predecessor). This scan is what makes a multi-def root —
        // both the directly-used loop `iv` and the value snapshotted by any
        // window-captured copy — provably stable across the two compares. Collect
        // the roots involved (the left root, and the right root when the rhs is a
        // register).
        // A SINGLE-DEF root is excluded: the scan is vacuous for it, and
        // including it produces a FALSE positive.
        //
        // The scan exists to catch a MULTI-def root being redefined between the
        // guard's read and the check's read. A vreg with exactly one definition
        // in the whole function cannot change value between two reads — there is
        // no second definition to change it — and its one definition must
        // dominate the guard's read, since the guard reads it.
        //
        // Including such a root is not merely redundant, it is WRONG in one
        // reachable combination: `operand_redefined_between` is positional, so it
        // reports the root's OWN defining instruction when that instruction falls
        // inside the scanned range. That happens exactly when case 3b has lowered
        // `scan_from` below the definition — which is h1_vec_push_sum's shape,
        // where the index is admitted by case 3b (`scan_from` = 0) and the length
        // root is the guard block's own load at index 1. Cases 1/2, 4 and 5 all
        // return single-def roots, and case 4's doc already states the intent
        // ("both vregs are single-def here, so ... the scan is a trivially-passing
        // no-op") — which only held while `scan_from` stayed at the guard compare.
        let mut roots: Vec<VReg> = Vec::new();
        if !single.contains_key(&lhs.root) {
            roots.push(lhs.root);
        }
        // The scan starts at the EARLIEST position any admitted operand needs. A
        // lower start means a WIDER scan, which is the conservative direction:
        // case 3b is sound precisely because the root is checked for redefinition
        // all the way back to the guard-side copy's definition, and applying that
        // wider scan to the other operand's root too can only reject more.
        let scan_from = match rhs {
            Some(r) => lhs.guard_scan_from.min(r.guard_scan_from),
            None => lhs.guard_scan_from,
        };
        if let Some(r) = rhs
            && !single.contains_key(&r.root)
        {
            roots.push(r.root);
        }
        if !roots.is_empty()
            && operand_redefined_between(func, db, scan_from, bb, check.cmp_pos, &roots)
        {
            decline!(
                bb,
                "a root {roots:?} is redefined in the covered window (guard {db:?}@{scan_from} .. check {bb:?}@{})",
                check.cmp_pos
            );
        }

        let remove_compare = compare_flags_dead_after(func, safe_target);

        if dbg {
            eprintln!(
                "[bce] {}:{bb:?} ACCEPT: trap {trap_block:?} unreachable, safe {safe_target:?}",
                func.name
            );
        }
        elims.push(Elimination {
            block: bb,
            cmp_pos: check.cmp_pos,
            safe_target,
            trap_block,
            remove_compare,
        });
    }

    elims
}

/// Rewrite one bounds-check terminator into an unconditional jump to `cont`.
fn apply_elimination(func: &mut X86ISelFunction, elim: &Elimination) {
    let Some(block) = func.blocks.get_mut(&elim.block) else {
        return;
    };
    // The compare + Jcc (+ Jmp) are the trailing instructions from `cmp_pos`.
    // Drop the compare too when its flags are dead; otherwise keep it (still
    // correct, flags merely unused) and drop only the branch pair.
    let keep_upto = if elim.remove_compare {
        elim.cmp_pos
    } else {
        elim.cmp_pos + 1
    };
    block.insts.truncate(keep_upto);
    block.insts.push(X86ISelInst::new(
        X86Opcode::Jmp,
        vec![X86ISelOperand::Block(elim.safe_target)],
    ));
    block.successors = vec![elim.safe_target];
}

/// Delete trap blocks orphaned by the rewrites, then restore the contiguous
/// block-id range. Only a block with ZERO predecessors (recomputed after the
/// rewrites) and the pure-trap shape is removed, so a trap shared by a
/// still-live check is preserved.
fn cleanup_orphan_traps(func: &mut X86ISelFunction, elims: &[Elimination]) {
    let preds = predecessor_map(func);
    let mut candidates: Vec<Block> = elims.iter().map(|e| e.trap_block).collect();
    candidates.sort_by_key(|b| b.0);
    candidates.dedup();

    let mut removed_any = false;
    for tb in candidates {
        let has_pred = preds.get(&tb).is_some_and(|p| !p.is_empty());
        if !has_pred && is_pure_trap_block(func, tb) {
            func.blocks.remove(&tb);
            func.block_order.retain(|b| *b != tb);
            removed_any = true;
        }
    }
    if removed_any {
        renumber_blocks_contiguous(func);
    }
}

/// Renumber every block to a gap-free `0..n` range following `block_order`,
/// rewriting block-map keys, `block_order`, per-block successors, and every
/// `X86ISelOperand::Block` operand. Restores the contiguous-id invariant the
/// x86 regalloc replay requires after a block is deleted. `block_order[0]` (the
/// entry) maps to `Block(0)`. Mirrors `x86_if_convert::renumber_blocks_contiguous`.
fn renumber_blocks_contiguous(func: &mut X86ISelFunction) {
    let len = func.block_order.len();
    let remap: crate::fast_hash::FxHashMap<Block, Block> = func
        .block_order
        .iter()
        .enumerate()
        .map(|(i, &b)| (b, Block(i as u32)))
        .collect();

    let order = std::mem::take(&mut func.block_order);
    let mut new_blocks: crate::fast_hash::FxHashMap<Block, X86ISelBlock> =
        crate::fast_hash::FxHashMap::with_capacity_and_hasher(len, Default::default());
    for old_id in &order {
        let Some(mut blk) = func.blocks.remove(old_id) else {
            continue;
        };
        for s in &mut blk.successors {
            if let Some(&n) = remap.get(s) {
                *s = n;
            }
        }
        for inst in &mut blk.insts {
            for op in &mut inst.operands {
                if let X86ISelOperand::Block(b) = op
                    && let Some(&n) = remap.get(b)
                {
                    *b = n;
                }
            }
        }
        if let Some(&new_id) = remap.get(old_id) {
            new_blocks.insert(new_id, blk);
        }
    }
    func.blocks = new_blocks;
    func.block_order = (0..len as u32).map(Block).collect();
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_cg_ir::regs::RegClass;
    use trust_cg_lower::function::Signature;
    use trust_cg_lower::types::Type;

    fn vreg(id: u32) -> VReg {
        VReg::new(id, RegClass::Gpr64)
    }

    fn cmp_rr(a: VReg, b: VReg) -> X86ISelInst {
        X86ISelInst::new(
            X86Opcode::CmpRR,
            vec![X86ISelOperand::VReg(a), X86ISelOperand::VReg(b)],
        )
    }

    fn jcc(cc: X86CondCode, t: Block) -> X86ISelInst {
        X86ISelInst::new(
            X86Opcode::Jcc,
            vec![X86ISelOperand::CondCode(cc), X86ISelOperand::Block(t)],
        )
    }

    fn jmp(t: Block) -> X86ISelInst {
        X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(t)])
    }

    fn mov_ri(d: VReg, imm: i64) -> X86ISelInst {
        X86ISelInst::new(
            X86Opcode::MovRI,
            vec![X86ISelOperand::VReg(d), X86ISelOperand::Imm(imm)],
        )
    }

    fn mov_rr(d: VReg, s: VReg) -> X86ISelInst {
        X86ISelInst::new(
            X86Opcode::MovRR,
            vec![X86ISelOperand::VReg(d), X86ISelOperand::VReg(s)],
        )
    }

    fn add_rr(d: VReg, s: VReg) -> X86ISelInst {
        X86ISelInst::new(
            X86Opcode::AddRR,
            vec![X86ISelOperand::VReg(d), X86ISelOperand::VReg(s)],
        )
    }

    fn add_ri(d: VReg, imm: i64) -> X86ISelInst {
        X86ISelInst::new(
            X86Opcode::AddRI,
            vec![X86ISelOperand::VReg(d), X86ISelOperand::Imm(imm)],
        )
    }

    fn ret() -> X86ISelInst {
        X86ISelInst::new(X86Opcode::Ret, vec![])
    }

    fn ud2() -> X86ISelInst {
        X86ISelInst::new(X86Opcode::Ud2, vec![])
    }

    fn call(symbol: &str) -> X86ISelInst {
        X86ISelInst::new(
            X86Opcode::Call,
            vec![X86ISelOperand::Symbol(symbol.to_string())],
        )
    }

    fn count_opcode(func: &X86ISelFunction, op: X86Opcode) -> usize {
        func.blocks
            .values()
            .flat_map(|b| b.insts.iter())
            .filter(|i| i.opcode == op)
            .count()
    }

    fn set_succ(func: &mut X86ISelFunction, b: Block, succs: Vec<Block>) {
        func.blocks.get_mut(&b).unwrap().successors = succs;
    }

    /// Base CFG:
    /// ```text
    ///   b0: iv=0; len=100; jmp b1
    ///   b1 (guard): cmp iv,len; jb b2; jmp b4
    ///   b2 (check): <head>;    cmp <c0>,<c1>; jb b3; jmp b5(trap)
    ///   b3 (cont):  add acc,iv; ret          (add clobbers flags -> compare dead)
    ///   b4 (exit):  ret
    ///   b5 (trap):  ud2
    /// ```
    /// `check_ops` supplies the bounds-check compare operands and any extra head
    /// instructions (e.g. an index redefinition).
    fn build_diamond(head: Vec<X86ISelInst>, c0: VReg, c1: VReg) -> X86ISelFunction {
        let sig = Signature {
            params: vec![],
            returns: vec![Type::I64],
        };
        let mut f = X86ISelFunction::new("bce_test".to_string(), sig);
        let (b0, b1, b2, b3, b4, b5) = (Block(0), Block(1), Block(2), Block(3), Block(4), Block(5));
        for b in [b0, b1, b2, b3, b4, b5] {
            f.ensure_block(b);
        }
        let iv = vreg(0);
        let len = vreg(1);
        let acc = vreg(2);
        f.next_vreg = 100;

        // b0
        f.push_inst(b0, mov_ri(iv, 0));
        f.push_inst(b0, mov_ri(len, 100));
        f.push_inst(b0, jmp(b1));
        // b1 guard
        f.push_inst(b1, cmp_rr(iv, len));
        f.push_inst(b1, jcc(X86CondCode::B, b2));
        f.push_inst(b1, jmp(b4));
        // b2 check
        for inst in head {
            f.push_inst(b2, inst);
        }
        f.push_inst(b2, cmp_rr(c0, c1));
        f.push_inst(b2, jcc(X86CondCode::B, b3));
        f.push_inst(b2, jmp(b5));
        // b3 cont
        f.push_inst(b3, add_rr(acc, iv));
        f.push_inst(b3, ret());
        // b4 exit
        f.push_inst(b4, ret());
        // b5 trap
        f.push_inst(b5, ud2());

        set_succ(&mut f, b0, vec![b1]);
        set_succ(&mut f, b1, vec![b2, b4]);
        set_succ(&mut f, b2, vec![b3, b5]);
        set_succ(&mut f, b3, vec![]);
        set_succ(&mut f, b4, vec![]);
        set_succ(&mut f, b5, vec![]);
        f
    }

    #[test]
    fn bounds_check_preserves_flags_across_partial_writes() {
        let mut f = build_diamond(vec![], vreg(0), vreg(1));
        f.blocks.get_mut(&Block(3)).unwrap().insts = vec![
            X86ISelInst::new(X86Opcode::Inc, vec![X86ISelOperand::VReg(vreg(2))]),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![
                    X86ISelOperand::VReg(VReg::new(3, RegClass::Gpr32)),
                    X86ISelOperand::CondCode(X86CondCode::B),
                ],
            ),
            ret(),
        ];
        assert!(!compare_flags_dead_after(&f, Block(3)));
        X86BoundsCheckElimination::new().run_on_function(&mut f);
        assert_eq!(count_opcode(&f, X86Opcode::CmpRR), 2);
    }

    #[test]
    fn eliminates_diamond_into_abort_call_trap() {
        // The bridge's shared panic=abort assert block `[Call abort, Ud2]` is
        // a pure trap: the redundant check's edge into it is eliminated and
        // the orphaned block removed, exactly as for a bare `Ud2`.
        let iv = vreg(0);
        let len = vreg(1);
        let mut f = build_diamond(vec![], iv, len);
        f.blocks.get_mut(&Block(5)).unwrap().insts = vec![call("abort"), ud2()];

        let mut pass = X86BoundsCheckElimination::new();
        assert!(pass.run_on_function(&mut f));
        assert_eq!(pass.last_run_eliminations, 1);
        assert_eq!(count_opcode(&f, X86Opcode::Ud2), 0, "trap block removed");
        assert_eq!(
            count_opcode(&f, X86Opcode::Call),
            0,
            "abort call removed with it"
        );
        assert_eq!(count_opcode(&f, X86Opcode::CmpRR), 1);
    }

    #[test]
    fn keeps_diamond_into_other_call_trap() {
        // `[Call exit, Ud2]` is not a pure trap (a call to any other symbol
        // is observable work): the check is kept.
        let iv = vreg(0);
        let len = vreg(1);
        let mut f = build_diamond(vec![], iv, len);
        f.blocks.get_mut(&Block(5)).unwrap().insts = vec![call("exit"), ud2()];

        let mut pass = X86BoundsCheckElimination::new();
        assert!(!pass.run_on_function(&mut f));
        assert_eq!(pass.last_run_eliminations, 0);
        assert_eq!(count_opcode(&f, X86Opcode::Ud2), 1, "trap kept");
        assert_eq!(count_opcode(&f, X86Opcode::Call), 1);
        assert_eq!(count_opcode(&f, X86Opcode::CmpRR), 2);
    }

    #[test]
    fn eliminates_own_length_redundant_diamond() {
        let iv = vreg(0);
        let len = vreg(1);
        // Harmless copy in the head (must not block elimination).
        let mut f = build_diamond(vec![mov_rr(vreg(10), iv)], iv, len);

        assert_eq!(count_opcode(&f, X86Opcode::Ud2), 1);
        assert_eq!(count_opcode(&f, X86Opcode::CmpRR), 2);

        let mut pass = X86BoundsCheckElimination::new();
        let changed = pass.run_on_function(&mut f);

        assert!(changed);
        assert_eq!(pass.last_run_eliminations, 1);
        // The trap block is gone, the redundant compare (flags dead) is gone,
        // and only the guard's compare + branch remain.
        assert_eq!(count_opcode(&f, X86Opcode::Ud2), 0, "trap block removed");
        assert_eq!(
            count_opcode(&f, X86Opcode::CmpRR),
            1,
            "only the guard compare remains"
        );
        assert_eq!(
            count_opcode(&f, X86Opcode::Jcc),
            1,
            "only the guard branch remains"
        );
        // Block ids stay contiguous after the trap deletion.
        assert_eq!(
            f.block_order,
            vec![Block(0), Block(1), Block(2), Block(3), Block(4)]
        );
    }

    #[test]
    fn keeps_cross_length_check() {
        // Guard compares iv,len(vreg1); the bounds check compares iv against a
        // DIFFERENT length vreg (vreg3) -> operands differ -> kept.
        let iv = vreg(0);
        let other_len = vreg(3);
        let mut f = build_diamond(vec![mov_ri(other_len, 200)], iv, other_len);

        let mut pass = X86BoundsCheckElimination::new();
        let changed = pass.run_on_function(&mut f);

        assert!(!changed);
        assert_eq!(pass.last_run_eliminations, 0);
        assert_eq!(count_opcode(&f, X86Opcode::Ud2), 1, "trap kept");
        assert_eq!(count_opcode(&f, X86Opcode::CmpRR), 2, "both compares kept");
    }

    #[test]
    fn keeps_redefined_index_check() {
        // The index `iv` is redefined (iv += 1) in the check block's head before
        // the bounds compare -> the value at the check differs from the guard ->
        // kept.
        let iv = vreg(0);
        let len = vreg(1);
        let mut f = build_diamond(vec![add_ri(iv, 1)], iv, len);

        let mut pass = X86BoundsCheckElimination::new();
        let changed = pass.run_on_function(&mut f);

        assert!(!changed);
        assert_eq!(pass.last_run_eliminations, 0);
        assert_eq!(count_opcode(&f, X86Opcode::Ud2), 1, "trap kept");
        assert_eq!(count_opcode(&f, X86Opcode::CmpRR), 2, "both compares kept");
    }

    #[test]
    fn keeps_check_without_dominating_guard() {
        // Give the check block a second predecessor so it has no unique
        // dominating guard edge -> kept.
        let iv = vreg(0);
        let len = vreg(1);
        let mut f = build_diamond(vec![], iv, len);
        // Add an extra edge b4 -> b2 (b4 currently just returns; repoint it).
        let b4 = Block(4);
        let b2 = Block(2);
        f.blocks.get_mut(&b4).unwrap().insts.clear();
        f.push_inst(b4, jmp(b2));
        set_succ(&mut f, b4, vec![b2]);
        // Now b2's predecessors are {b1, b4}.

        let mut pass = X86BoundsCheckElimination::new();
        let changed = pass.run_on_function(&mut f);

        assert!(!changed);
        assert_eq!(pass.last_run_eliminations, 0);
        assert_eq!(count_opcode(&f, X86Opcode::Ud2), 1, "trap kept");
        assert_eq!(count_opcode(&f, X86Opcode::CmpRR), 2, "both compares kept");
    }

    /// Build the real own-length loop shape: a MULTI-DEF loop `iv` (defined in
    /// the entry and again on a later block, as the phi-eliminated merge vreg is)
    /// compared DIRECTLY by the guard, while the bounds check compares a fresh
    /// single-def COPY of `iv` (`v_copy = mov iv`) materialised in the check
    /// block's head — inside the covered window. `copy_place` chooses whether the
    /// copy is placed in the check block head (inside the window) or in the entry
    /// block (outside the window).
    fn build_multidef_iv_copy(copy_in_window: bool) -> X86ISelFunction {
        let sig = Signature {
            params: vec![],
            returns: vec![Type::I64],
        };
        let mut f = X86ISelFunction::new("bce_multidef".to_string(), sig);
        let (b0, b1, b2, b3, b4, b5) = (Block(0), Block(1), Block(2), Block(3), Block(4), Block(5));
        for b in [b0, b1, b2, b3, b4, b5] {
            f.ensure_block(b);
        }
        let iv = vreg(0);
        let len = vreg(1);
        let acc = vreg(2);
        let v_copy = vreg(10);
        f.next_vreg = 100;

        // b0 entry
        f.push_inst(b0, mov_ri(iv, 0));
        f.push_inst(b0, mov_ri(len, 100));
        if !copy_in_window {
            // Copy captured OUTSIDE the covered window (in the entry block).
            f.push_inst(b0, mov_rr(v_copy, iv));
        }
        f.push_inst(b0, jmp(b1));
        // b1 guard/header: compares `iv` DIRECTLY.
        f.push_inst(b1, cmp_rr(iv, len));
        f.push_inst(b1, jcc(X86CondCode::B, b2));
        f.push_inst(b1, jmp(b4));
        // b2 check: compares a COPY of `iv`.
        if copy_in_window {
            // Copy captured INSIDE the covered window (check block head).
            f.push_inst(b2, mov_rr(v_copy, iv));
        }
        f.push_inst(b2, cmp_rr(v_copy, len));
        f.push_inst(b2, jcc(X86CondCode::B, b3));
        f.push_inst(b2, jmp(b5));
        // b3 cont
        f.push_inst(b3, add_rr(acc, iv));
        f.push_inst(b3, ret());
        // b4 exit: a SECOND definition of `iv` makes it multi-def (the merge-vreg
        // shape). It is outside the covered window, so it must not affect the
        // guard->check equality.
        f.push_inst(b4, add_ri(iv, 1));
        f.push_inst(b4, ret());
        // b5 trap
        f.push_inst(b5, ud2());

        set_succ(&mut f, b0, vec![b1]);
        set_succ(&mut f, b1, vec![b2, b4]);
        set_succ(&mut f, b2, vec![b3, b5]);
        set_succ(&mut f, b3, vec![]);
        set_succ(&mut f, b4, vec![]);
        set_succ(&mut f, b5, vec![]);
        f
    }

    #[test]
    fn eliminates_check_using_window_captured_copy_of_multidef_iv() {
        // The genuine own-length loop shape (the case a naive identical-vreg-only
        // match would miss): guard compares the multi-def `iv` directly; the check
        // compares a copy of it captured inside the loop body (the covered
        // window). Sound because `iv` is not redefined between the two compares.
        let mut f = build_multidef_iv_copy(true);
        assert_eq!(count_opcode(&f, X86Opcode::Ud2), 1);
        assert_eq!(count_opcode(&f, X86Opcode::CmpRR), 2);

        let mut pass = X86BoundsCheckElimination::new();
        let changed = pass.run_on_function(&mut f);

        assert!(changed, "own-length copy-of-iv diamond must be eliminated");
        assert_eq!(pass.last_run_eliminations, 1);
        assert_eq!(count_opcode(&f, X86Opcode::Ud2), 0, "trap block removed");
        assert_eq!(
            count_opcode(&f, X86Opcode::CmpRR),
            1,
            "only the guard compare remains"
        );
    }

    #[test]
    fn keeps_check_using_copy_captured_outside_window() {
        // A copy of the multi-def `iv` captured OUTSIDE the covered window (in the
        // entry block) may hold a stale value the between-window scan cannot see,
        // so the check is KEPT (fail-safe) — this is the divergent-capture hole
        // the window check closes.
        let mut f = build_multidef_iv_copy(false);

        let mut pass = X86BoundsCheckElimination::new();
        let changed = pass.run_on_function(&mut f);

        assert!(!changed, "copy captured outside the window must not match");
        assert_eq!(pass.last_run_eliminations, 0);
        assert_eq!(count_opcode(&f, X86Opcode::Ud2), 1, "trap kept");
        assert_eq!(count_opcode(&f, X86Opcode::CmpRR), 2, "both compares kept");
    }

    // ---- Case 4: `len` RELOADED from the same frame slot (the Vec shape) ----

    fn lea_slot(dst: VReg, slot: u32, disp: i32) -> X86ISelInst {
        X86ISelInst::new(
            X86Opcode::Lea,
            vec![
                X86ISelOperand::VReg(dst),
                X86ISelOperand::MemAddr {
                    base: Box::new(X86ISelOperand::StackSlot(slot)),
                    disp,
                },
            ],
        )
    }

    fn load_at(op: X86Opcode, dst: VReg, base: VReg, disp: i32) -> X86ISelInst {
        X86ISelInst::new(
            op,
            vec![
                X86ISelOperand::VReg(dst),
                X86ISelOperand::MemAddr {
                    base: Box::new(X86ISelOperand::VReg(base)),
                    disp,
                },
            ],
        )
    }

    fn store_at(op: X86Opcode, base: VReg, disp: i32, src: VReg) -> X86ISelInst {
        X86ISelInst::new(
            op,
            vec![
                X86ISelOperand::MemAddr {
                    base: Box::new(X86ISelOperand::VReg(base)),
                    disp,
                },
                X86ISelOperand::VReg(src),
            ],
        )
    }

    /// `while k < v.len() { .. v[k] .. }` over an OWNING container: the guard
    /// and the bounds check each RELOAD `len` from the container's header, so
    /// they compare two textually distinct load results.
    ///
    /// The slot/displacement/opcode fields let a test make the second load read
    /// a different location. `between` is spliced into the check block BEFORE
    /// its load, which is exactly the region the pass must scan: the guard
    /// block's tail after the first load plus the check block's head before the
    /// second.
    struct ReloadShape {
        guard_slot: u32,
        guard_disp: i32,
        guard_op: X86Opcode,
        check_slot: u32,
        check_disp: i32,
        check_op: X86Opcode,
        between: Vec<X86ISelInst>,
    }

    impl Default for ReloadShape {
        fn default() -> Self {
            Self {
                guard_slot: 0,
                guard_disp: 16,
                guard_op: X86Opcode::MovRM,
                check_slot: 0,
                check_disp: 16,
                check_op: X86Opcode::MovRM,
                between: vec![],
            }
        }
    }

    fn build_reload_diamond(shape: ReloadShape) -> X86ISelFunction {
        let sig = Signature {
            params: vec![],
            returns: vec![Type::I64],
        };
        let mut f = X86ISelFunction::new("bce_reload_test".to_string(), sig);
        let (b0, b1, b2, b3, b4, b5) = (Block(0), Block(1), Block(2), Block(3), Block(4), Block(5));
        for b in [b0, b1, b2, b3, b4, b5] {
            f.ensure_block(b);
        }
        f.stack_slots = vec![
            trust_cg_lower::function::StackSlotInfo::new(24, 8),
            trust_cg_lower::function::StackSlotInfo::new(24, 8),
        ];
        let iv = vreg(0);
        let acc = vreg(2);
        let p_guard = vreg(3);
        let p_check = vreg(4);
        let len_g = vreg(5);
        let len_c = vreg(6);
        f.next_vreg = 100;

        // b0: iv = 0, and one `lea` root per slot the shape names.
        f.push_inst(b0, mov_ri(iv, 0));
        f.push_inst(b0, lea_slot(p_guard, shape.guard_slot, 0));
        f.push_inst(b0, lea_slot(p_check, shape.check_slot, 0));
        f.push_inst(b0, jmp(b1));
        // b1 guard: reload len, compare, branch.
        f.push_inst(
            b1,
            load_at(shape.guard_op, len_g, p_guard, shape.guard_disp),
        );
        f.push_inst(b1, cmp_rr(iv, len_g));
        f.push_inst(b1, jcc(X86CondCode::B, b2));
        f.push_inst(b1, jmp(b4));
        // b2 check: first whatever the test puts BETWEEN the two loads, then the
        // second reload of len, then the redundant compare and the trap diamond.
        for inst in shape.between {
            f.push_inst(b2, inst);
        }
        f.push_inst(
            b2,
            load_at(shape.check_op, len_c, p_check, shape.check_disp),
        );
        f.push_inst(b2, cmp_rr(iv, len_c));
        f.push_inst(b2, jcc(X86CondCode::B, b3));
        f.push_inst(b2, jmp(b5));
        // b3 cont / b4 exit / b5 trap
        f.push_inst(b3, add_rr(acc, iv));
        f.push_inst(b3, ret());
        f.push_inst(b4, ret());
        f.push_inst(b5, ud2());

        set_succ(&mut f, b0, vec![b1]);
        set_succ(&mut f, b1, vec![b2, b4]);
        set_succ(&mut f, b2, vec![b3, b5]);
        set_succ(&mut f, b3, vec![]);
        set_succ(&mut f, b4, vec![]);
        set_succ(&mut f, b5, vec![]);
        f
    }

    fn run_reload(shape: ReloadShape) -> (bool, usize, X86ISelFunction) {
        let mut f = build_reload_diamond(shape);
        assert_eq!(
            count_opcode(&f, X86Opcode::Ud2),
            1,
            "shape starts with a trap"
        );
        let mut pass = X86BoundsCheckElimination::new();
        let changed = pass.run_on_function(&mut f);
        (changed, pass.last_run_eliminations, f)
    }

    #[test]
    fn eliminates_own_length_check_when_len_is_reloaded_from_the_same_slot() {
        // The case cases 1-3 could not reach: two DISTINCT load-defined vregs,
        // proved equal because they reload the same frame bytes.
        let (changed, elims, f) = run_reload(ReloadShape::default());
        assert!(changed);
        assert_eq!(elims, 1, "the reloaded-len check is eliminated");
        assert_eq!(count_opcode(&f, X86Opcode::Ud2), 0, "trap block removed");
    }

    #[test]
    fn keeps_reloaded_len_check_when_an_overlapping_store_intervenes() {
        // A store to the SAME bytes between the two loads: the second load may
        // legitimately differ, so the check must stay.
        let shape = ReloadShape {
            between: vec![store_at(X86Opcode::MovMR, vreg(3), 16, vreg(0))],
            ..Default::default()
        };
        let (changed, elims, f) = run_reload(shape);
        assert!(!changed, "an aliasing write must block the elimination");
        assert_eq!(elims, 0);
        assert_eq!(count_opcode(&f, X86Opcode::Ud2), 1, "trap block retained");
    }

    #[test]
    fn eliminates_reloaded_len_check_across_a_disjoint_store_in_the_same_slot() {
        // A store to the container's `ptr` field (offset 0, 8 bytes) cannot
        // change its `len` field (offset 16). This is the test that proves the
        // disambiguation is a real byte-range check and not "no stores at all".
        let shape = ReloadShape {
            between: vec![store_at(X86Opcode::MovMR, vreg(3), 0, vreg(0))],
            ..Default::default()
        };
        let (changed, elims, _f) = run_reload(shape);
        assert!(changed, "a disjoint field store must not block it");
        assert_eq!(elims, 1);
    }

    #[test]
    fn keeps_reloaded_len_check_when_a_store_partially_overlaps() {
        // A 8-byte store at offset 12 covers bytes 12..20 and so overlaps the
        // 8-byte len at 16..24. Partial overlap must be treated as aliasing.
        let shape = ReloadShape {
            between: vec![store_at(X86Opcode::MovMR, vreg(3), 12, vreg(0))],
            ..Default::default()
        };
        let (changed, elims, _f) = run_reload(shape);
        assert!(!changed, "a partially overlapping store must block it");
        assert_eq!(elims, 0);
    }

    #[test]
    fn keeps_reloaded_len_check_when_a_call_intervenes() {
        let shape = ReloadShape {
            between: vec![call("opaque")],
            ..Default::default()
        };
        let (changed, elims, _f) = run_reload(shape);
        assert!(!changed, "a call may write any frame slot");
        assert_eq!(elims, 0);
    }

    #[test]
    fn keeps_reloaded_len_check_when_a_store_address_does_not_resolve() {
        // Store through a vreg that is NOT a slot `lea` root: it could hold any
        // pointer, so it may alias and the check must stay.
        let shape = ReloadShape {
            between: vec![store_at(X86Opcode::MovMR, vreg(77), 16, vreg(0))],
            ..Default::default()
        };
        let (changed, elims, _f) = run_reload(shape);
        assert!(!changed, "an unresolvable store address may alias");
        assert_eq!(elims, 0);
    }

    #[test]
    fn keeps_reloaded_len_check_across_two_different_slots() {
        // `x[i]` guarded by `y.len()` -- the cross-container analogue of
        // `keeps_cross_length_check`, now through reloads.
        let shape = ReloadShape {
            check_slot: 1,
            ..Default::default()
        };
        let (changed, elims, _f) = run_reload(shape);
        assert!(!changed, "two different slots are two different lengths");
        assert_eq!(elims, 0);
    }

    #[test]
    fn keeps_reloaded_len_check_when_the_two_loads_read_different_offsets() {
        let shape = ReloadShape {
            check_disp: 8,
            ..Default::default()
        };
        let (changed, elims, _f) = run_reload(shape);
        assert!(
            !changed,
            "different fields of one slot are different values"
        );
        assert_eq!(elims, 0);
    }

    #[test]
    fn keeps_reloaded_len_check_when_the_two_loads_have_different_widths() {
        // A 4-byte reload does not prove an 8-byte guard value.
        let shape = ReloadShape {
            check_op: X86Opcode::MovRM32,
            ..Default::default()
        };
        let (changed, elims, _f) = run_reload(shape);
        assert!(!changed, "differing access widths must not unify");
        assert_eq!(elims, 0);
    }

    /// The shape that motivated case 4 and that a ONE-`Lea` resolver missed: the
    /// length is reached by a CHAIN — `lea vec, [StackSlot(0)+0]` then
    /// `lea len_addr, [vec+16]` — which is how the selector spells the address of
    /// a field of a frame local. Both loads go through the chained address.
    fn build_chained_lea_reload_diamond(second_chain_disp: i32) -> X86ISelFunction {
        let sig = Signature {
            params: vec![],
            returns: vec![Type::I64],
        };
        let mut f = X86ISelFunction::new("bce_chain_test".to_string(), sig);
        let (b0, b1, b2, b3, b4, b5) = (Block(0), Block(1), Block(2), Block(3), Block(4), Block(5));
        for b in [b0, b1, b2, b3, b4, b5] {
            f.ensure_block(b);
        }
        f.stack_slots = vec![trust_cg_lower::function::StackSlotInfo::new(24, 8)];
        let iv = vreg(0);
        let acc = vreg(2);
        let vec_ptr = vreg(3);
        let len_addr_g = vreg(4);
        let len_addr_c = vreg(5);
        let len_g = vreg(6);
        let len_c = vreg(7);
        f.next_vreg = 100;

        // b0: the base slot `lea`, then one field `lea` per side.
        f.push_inst(b0, mov_ri(iv, 0));
        f.push_inst(b0, lea_slot(vec_ptr, 0, 0));
        f.push_inst(b0, lea_reg(len_addr_g, vec_ptr, 16));
        f.push_inst(b0, lea_reg(len_addr_c, vec_ptr, second_chain_disp));
        f.push_inst(b0, jmp(b1));
        // b1 guard
        f.push_inst(b1, load_at(X86Opcode::MovRM, len_g, len_addr_g, 0));
        f.push_inst(b1, cmp_rr(iv, len_g));
        f.push_inst(b1, jcc(X86CondCode::B, b2));
        f.push_inst(b1, jmp(b4));
        // b2 check
        f.push_inst(b2, load_at(X86Opcode::MovRM, len_c, len_addr_c, 0));
        f.push_inst(b2, cmp_rr(iv, len_c));
        f.push_inst(b2, jcc(X86CondCode::B, b3));
        f.push_inst(b2, jmp(b5));
        f.push_inst(b3, add_rr(acc, iv));
        f.push_inst(b3, ret());
        f.push_inst(b4, ret());
        f.push_inst(b5, ud2());

        set_succ(&mut f, b0, vec![b1]);
        set_succ(&mut f, b1, vec![b2, b4]);
        set_succ(&mut f, b2, vec![b3, b5]);
        set_succ(&mut f, b3, vec![]);
        set_succ(&mut f, b4, vec![]);
        set_succ(&mut f, b5, vec![]);
        f
    }

    fn lea_reg(dst: VReg, base: VReg, disp: i32) -> X86ISelInst {
        X86ISelInst::new(
            X86Opcode::Lea,
            vec![
                X86ISelOperand::VReg(dst),
                X86ISelOperand::MemAddr {
                    base: Box::new(X86ISelOperand::VReg(base)),
                    disp,
                },
            ],
        )
    }

    #[test]
    fn eliminates_reloaded_len_check_through_a_chained_field_lea() {
        let mut f = build_chained_lea_reload_diamond(16);
        let mut pass = X86BoundsCheckElimination::new();
        assert!(pass.run_on_function(&mut f));
        assert_eq!(
            pass.last_run_eliminations, 1,
            "a chained `lea` field address must resolve to its slot"
        );
        assert_eq!(count_opcode(&f, X86Opcode::Ud2), 0);
    }

    #[test]
    fn keeps_reloaded_len_check_when_the_chained_leas_reach_different_fields() {
        // Same base slot, chains ending at different offsets: different values.
        let mut f = build_chained_lea_reload_diamond(8);
        let mut pass = X86BoundsCheckElimination::new();
        let changed = pass.run_on_function(&mut f);
        assert!(!changed, "different fields are different lengths");
        assert_eq!(pass.last_run_eliminations, 0);
        assert_eq!(count_opcode(&f, X86Opcode::Ud2), 1);
    }

    /// h1_vec_push_sum's ACTUAL shape: a length address computed into a register
    /// from a pointer that is NOT slot-rooted (so case 4 cannot resolve it), and
    /// the check side reads through a plain `MovRR` COPY of that same register.
    /// `between` is spliced into the check block BEFORE the second load.
    fn build_pointer_reload_diamond(check_disp: i32, between: Vec<X86ISelInst>) -> X86ISelFunction {
        let mut f = build_chained_lea_reload_diamond(16);
        let b0 = Block(0);
        // Root the chain in an arbitrary (non-slot) pointer, as h1's `Vec` header
        // address is: `mov r10, [slot] ; lea rdi, [r10 + 16]`.
        f.blocks.get_mut(&b0).unwrap().insts[1] = lea_reg(vreg(3), vreg(88), 0);
        // The check-side address is a COPY of the guard-side address, not a second
        // `lea`. This is what makes `canon` reach one shared base.
        f.blocks.get_mut(&b0).unwrap().insts[3] = X86ISelInst::new(
            X86Opcode::MovRR,
            vec![X86ISelOperand::VReg(vreg(5)), X86ISelOperand::VReg(vreg(4))],
        );
        // Re-point the check load's displacement if the test wants them to differ.
        let b2 = Block(2);
        if check_disp != 0 {
            f.blocks.get_mut(&b2).unwrap().insts[0] =
                load_at(X86Opcode::MovRM, vreg(7), vreg(5), check_disp);
        }
        for (k, inst) in between.into_iter().enumerate() {
            f.blocks.get_mut(&b2).unwrap().insts.insert(k, inst);
        }
        f
    }

    fn run_pointer_reload(f: &mut X86ISelFunction, arm: bool) -> (bool, usize) {
        let mut pass = X86BoundsCheckElimination::new().with_pointer_reload(arm);
        let changed = pass.run_on_function(f);
        (changed, pass.last_run_eliminations)
    }

    #[test]
    fn case5_eliminates_when_the_check_address_is_a_copy_of_the_guard_address() {
        // Same pointer, same displacement, no store between: one value, so the
        // second compare is redundant and its trap is unreachable.
        let mut f = build_pointer_reload_diamond(0, vec![]);
        let (changed, n) = run_pointer_reload(&mut f, true);
        assert!(
            changed,
            "a same-pointer reload with no store between must elide"
        );
        assert_eq!(n, 1);
        assert_eq!(count_opcode(&f, X86Opcode::Ud2), 0);
    }

    #[test]
    fn case5_with_a_case3b_guard_copy_is_not_defeated_by_the_redefinition_scan() {
        // THE INTERACTION THAT BLOCKED h1. When the guard's INDEX is a copy
        // defined in the guard block before its compare, case 3b lowers the
        // redefinition scan's start to that copy's index. The widened window then
        // CONTAINS the length root's own defining load, and a positional scan
        // reports that definition as a "redefinition" — declining a candidate
        // whose every real condition holds.
        //
        // The fix excludes SINGLE-DEF roots from the scan (a vreg with one
        // definition cannot change value between two reads, and its definition
        // dominates the guard's read). This pins it: the same fixture, with the
        // guard comparing a guard-block copy of the index, must still eliminate.
        let mut f = build_pointer_reload_diamond(0, vec![]);
        let b1 = Block(1);
        // Guard block becomes: MovRR ivc <- iv ; MovRM len_g ; CmpRR ivc,len_g ; ...
        let ivc = vreg(60);
        {
            let blk = f.blocks.get_mut(&b1).unwrap();
            blk.insts.insert(
                0,
                X86ISelInst::new(
                    X86Opcode::MovRR,
                    vec![X86ISelOperand::VReg(ivc), X86ISelOperand::VReg(vreg(0))],
                ),
            );
            // Re-point the guard compare at the copy (it is now at index 2).
            blk.insts[2] = cmp_rr(ivc, vreg(6));
        }
        let (changed, n) = run_pointer_reload(&mut f, true);
        assert!(
            changed,
            "a case-3b guard copy must not make the length root's own load look like a redefinition"
        );
        assert_eq!(n, 1);
        assert_eq!(count_opcode(&f, X86Opcode::Ud2), 0);
    }

    #[test]
    fn a_multi_def_root_is_still_scanned_for_redefinition() {
        // The exclusion must NOT weaken the scan for what it is actually for: a
        // MULTI-def root really redefined between the two compares. Give the
        // index a second definition inside the covered window.
        let mut f = build_pointer_reload_diamond(0, vec![]);
        let b2 = Block(2);
        f.blocks
            .get_mut(&b2)
            .unwrap()
            .insts
            .insert(0, mov_ri(vreg(0), 7));
        let (changed, n) = run_pointer_reload(&mut f, true);
        assert!(
            !changed,
            "a multi-def index redefined in the window must still decline"
        );
        assert_eq!(n, 0);
        assert_eq!(count_opcode(&f, X86Opcode::Ud2), 1);
    }

    #[test]
    fn case5_is_off_by_default() {
        // FALSIFIABILITY, and it also preserves
        // `keeps_reloaded_len_check_when_the_address_chain_is_not_slot_rooted`:
        // the identical fixture with only the opt-in changed must KEEP the check.
        let mut f = build_pointer_reload_diamond(0, vec![]);
        let (changed, n) = run_pointer_reload(&mut f, false);
        assert!(!changed, "case 5 must be OFF by default");
        assert_eq!(n, 0);
        assert_eq!(count_opcode(&f, X86Opcode::Ud2), 1);
    }

    #[test]
    fn case5_refuses_any_store_between_the_loads() {
        // The arm cannot compare a store's target against its own address, so it
        // refuses on ANY store -- stricter than case 4's aliasing test. This is
        // the premise upstream named as missing ("a store may separate the
        // trip-bound load from the element guard's reload").
        let store = X86ISelInst::new(
            X86Opcode::MovMR,
            vec![
                X86ISelOperand::MemAddr {
                    base: Box::new(X86ISelOperand::StackSlot(0)),
                    disp: 0,
                },
                X86ISelOperand::VReg(vreg(0)),
            ],
        );
        let mut f = build_pointer_reload_diamond(0, vec![store]);
        let (changed, n) = run_pointer_reload(&mut f, true);
        assert!(!changed, "a store between the loads must decline");
        assert_eq!(n, 0);
        assert_eq!(count_opcode(&f, X86Opcode::Ud2), 1);
    }

    #[test]
    fn case5_refuses_a_call_between_the_loads() {
        let call = X86ISelInst::new(
            X86Opcode::Call,
            vec![X86ISelOperand::ExactModuleSymbol("opaque".into())],
        );
        let mut f = build_pointer_reload_diamond(0, vec![call]);
        let (changed, n) = run_pointer_reload(&mut f, true);
        assert!(!changed, "a call between the loads may write the location");
        assert_eq!(n, 0);
        assert_eq!(count_opcode(&f, X86Opcode::Ud2), 1);
    }

    #[test]
    fn case5_refuses_different_displacements() {
        // Same base register, DIFFERENT offset: two locations, two values.
        let mut f = build_pointer_reload_diamond(8, vec![]);
        let (changed, n) = run_pointer_reload(&mut f, true);
        assert!(!changed, "different displacements are different addresses");
        assert_eq!(n, 0);
        assert_eq!(count_opcode(&f, X86Opcode::Ud2), 1);
    }

    #[test]
    fn case5_refuses_a_multi_def_address_register() {
        // The shared base must be unique-def function-wide, so nothing can move
        // the address between the loads. Give it a second definition.
        let mut f = build_pointer_reload_diamond(0, vec![]);
        let b3 = Block(3);
        f.blocks
            .get_mut(&b3)
            .unwrap()
            .insts
            .insert(0, lea_reg(vreg(4), vreg(88), 32));
        let (changed, n) = run_pointer_reload(&mut f, true);
        assert!(!changed, "a multi-def address register must decline");
        assert_eq!(n, 0);
        assert_eq!(count_opcode(&f, X86Opcode::Ud2), 1);
    }

    #[test]
    fn keeps_reloaded_len_check_when_the_address_chain_is_not_slot_rooted() {
        // The chain's root `lea` is over a register that is NOT a slot (an
        // arbitrary pointer, e.g. into the heap): unresolvable, so decline.
        let mut f = build_chained_lea_reload_diamond(16);
        // Rewrite the root `lea` so its base is an unrelated vreg, not a slot.
        let b0 = Block(0);
        f.blocks.get_mut(&b0).unwrap().insts[1] = lea_reg(vreg(3), vreg(88), 0);
        let mut pass = X86BoundsCheckElimination::new();
        assert!(
            !pass.run_on_function(&mut f),
            "a chain not rooted in a stack slot may alias anything"
        );
        assert_eq!(count_opcode(&f, X86Opcode::Ud2), 1);
    }

    // ---- Case 3b: the GUARD side is a copy made before the guard compare ----

    /// `while k < v.len() { .. v[k] .. }` after the cleanup cluster: BOTH compares
    /// read a copy of the multi-def loop IV, the guard's made in the guard block
    /// before its compare and the check's in the check block before its own.
    ///
    /// `redefine_root_in_guard_block` inserts a redefinition of the IV BETWEEN the
    /// guard's copy and the guard compare. That makes the two copies hold
    /// genuinely different values, and it is the case the widened redefinition
    /// scan exists to catch — a scan starting at the compare cannot see it.
    fn build_guard_side_copy(redefine_root_in_guard_block: bool) -> X86ISelFunction {
        let sig = Signature {
            params: vec![],
            returns: vec![Type::I64],
        };
        let mut f = X86ISelFunction::new("bce_guard_copy".to_string(), sig);
        let (b0, b1, b2, b3, b4, b5) = (Block(0), Block(1), Block(2), Block(3), Block(4), Block(5));
        for b in [b0, b1, b2, b3, b4, b5] {
            f.ensure_block(b);
        }
        let iv = vreg(0);
        let len = vreg(1);
        let acc = vreg(2);
        let g_copy = vreg(10);
        let c_copy = vreg(11);
        f.next_vreg = 100;

        f.push_inst(b0, mov_ri(iv, 0));
        f.push_inst(b0, mov_ri(len, 100));
        f.push_inst(b0, jmp(b1));
        // b1 guard: copy the IV, then (optionally) redefine the IV, then compare.
        f.push_inst(b1, mov_rr(g_copy, iv));
        if redefine_root_in_guard_block {
            f.push_inst(b1, add_ri(iv, 1));
        }
        f.push_inst(b1, cmp_rr(g_copy, len));
        f.push_inst(b1, jcc(X86CondCode::B, b2));
        f.push_inst(b1, jmp(b4));
        // b2 check: a copy captured inside the covered window.
        f.push_inst(b2, mov_rr(c_copy, iv));
        f.push_inst(b2, cmp_rr(c_copy, len));
        f.push_inst(b2, jcc(X86CondCode::B, b3));
        f.push_inst(b2, jmp(b5));
        f.push_inst(b3, add_rr(acc, iv));
        f.push_inst(b3, ret());
        // A second IV definition makes it the multi-def merge shape.
        f.push_inst(b4, add_ri(iv, 1));
        f.push_inst(b4, ret());
        f.push_inst(b5, ud2());

        set_succ(&mut f, b0, vec![b1]);
        set_succ(&mut f, b1, vec![b2, b4]);
        set_succ(&mut f, b2, vec![b3, b5]);
        set_succ(&mut f, b3, vec![]);
        set_succ(&mut f, b4, vec![]);
        set_succ(&mut f, b5, vec![]);
        f
    }

    #[test]
    fn eliminates_check_when_both_sides_use_copies_of_the_multidef_iv() {
        let mut f = build_guard_side_copy(false);
        let mut pass = X86BoundsCheckElimination::new();
        assert!(pass.run_on_function(&mut f));
        assert_eq!(pass.last_run_eliminations, 1);
        assert_eq!(count_opcode(&f, X86Opcode::Ud2), 0, "trap block removed");
    }

    #[test]
    fn keeps_check_when_the_root_is_redefined_between_the_guard_copy_and_its_compare() {
        // THE test for the widened scan. The guard's copy holds the OLD iv and
        // the check's copy the NEW one, so the guard's predicate does not imply
        // the check's. Only a scan reaching BACK to the copy's definition sees
        // the redefinition; one starting at the compare does not.
        let mut f = build_guard_side_copy(true);
        let mut pass = X86BoundsCheckElimination::new();
        let changed = pass.run_on_function(&mut f);
        assert!(
            !changed,
            "a stale guard-side capture must block the elimination"
        );
        assert_eq!(pass.last_run_eliminations, 0);
        assert_eq!(count_opcode(&f, X86Opcode::Ud2), 1, "trap block retained");
    }

    #[test]
    fn keeps_check_when_the_guard_copy_is_made_outside_the_guard_block() {
        // Case 3b admits a guard-side copy only from the GUARD BLOCK, because
        // "not redefined" along an arbitrary dominator path is not proved here.
        let mut f = build_guard_side_copy(false);
        // Move the guard's copy from the guard block into the entry block.
        let copy = f.blocks.get_mut(&Block(1)).unwrap().insts.remove(0);
        let entry = f.blocks.get_mut(&Block(0)).unwrap();
        entry.insts.insert(2, copy);
        let mut pass = X86BoundsCheckElimination::new();
        assert!(
            !pass.run_on_function(&mut f),
            "a guard-side copy from another block is not admitted"
        );
        assert_eq!(count_opcode(&f, X86Opcode::Ud2), 1);
    }
}
