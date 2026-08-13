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
//!    block whose only instruction is `Ud2` (an
//!    `emit_synthetic_trap_block`-shaped dead end). That is the trap edge; the
//!    other successor is the fall-through (`cont`).
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
//! Kill switch: `TCG_NO_X86_BCE` (any value) disables the pass. Default ON at
//! O2/O3, mirroring `TCG_NO_VECTORIZE` / `TCG_NO_X86_SROA`.

use std::collections::{HashMap, HashSet, VecDeque};

use trust_cg_ir::regs::VReg;
use trust_cg_ir::x86_64_ops::{X86CondCode, X86Opcode};
use trust_cg_lower::instructions::Block;
use trust_cg_lower::{X86ISelBlock, X86ISelFunction, X86ISelInst, X86ISelOperand};

use crate::effects::{x86_produces_value, x86_reads_flags, x86_writes_flags};
use crate::mach_view::{CfgAnalysis, predecessor_map};
use crate::x86_pass_manager::X86MachinePass;

/// Kill switch: set `TCG_NO_X86_BCE` (any value) to disable the pass.
/// Default ON at O2/O3 (mirrors `TCG_NO_VECTORIZE` / `TCG_NO_X86_SROA`).
fn bce_enabled() -> bool {
    std::env::var_os("TCG_NO_X86_BCE").is_none()
}

/// x86-64 dominated-identical-compare bounds-check elimination pass.
#[derive(Default)]
pub struct X86BoundsCheckElimination {
    /// Number of bounds checks eliminated by the most recent [`run`]
    /// invocation (diagnostics / tests only).
    ///
    /// [`run`]: X86MachinePass::run
    pub last_run_eliminations: usize,
}

impl X86BoundsCheckElimination {
    /// Create the pass.
    pub fn new() -> Self {
        Self {
            last_run_eliminations: 0,
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
                let mut by_block: HashMap<Block, Vec<usize>> = HashMap::new();
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
        let elims = find_eliminations(func);
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
fn bce_carrier_enabled() -> bool {
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
    let mut fwd: HashSet<Block> = HashSet::new();
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
    let mut bwd: HashSet<Block> = HashSet::new();
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
            if std::env::var_os("TCG_X86_BCE_CARRIER_DUMP").is_some() {
                eprintln!(
                    "[bce-carrier-dump] declined carrier {c_blk:?}[{p}] idx={idx:?} root={root:?}"
                );
                // Full single-def MovRR chain from idx with def sites.
                let mut v = idx;
                for hop in 0..8 {
                    match single_def.get(&v) {
                        None => {
                            eprintln!("    chain[{hop}] {v:?} MULTI-DEF/param — defs:");
                            for &b in &func.block_order {
                                if let Some(blk) = func.blocks.get(&b) {
                                    for (i, m) in blk.insts.iter().enumerate() {
                                        if inst_def_vreg(m) == Some(v) {
                                            eprintln!(
                                                "        {b:?}[{i}] {:?} {:?}",
                                                m.opcode, m.operands
                                            );
                                        }
                                    }
                                }
                            }
                            break;
                        }
                        Some(&(b, i)) => {
                            let m = &func.blocks[&b].insts[i];
                            eprintln!(
                                "    chain[{hop}] {v:?} def at {b:?}[{i}] {:?} {:?}",
                                m.opcode, m.operands
                            );
                            if m.opcode == X86Opcode::MovRR
                                && let Some(X86ISelOperand::VReg(s)) = m.operands.get(1)
                            {
                                v = *s;
                                continue;
                            }
                            break;
                        }
                    }
                }
            }
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

/// True iff `block` is a pure trap: a dead end whose only instruction is `Ud2`
/// (the `emit_synthetic_trap_block` shape and the panic=abort bounds-fail
/// block). Conservative: `Nop` padding is ignored, but any other instruction or
/// any successor edge disqualifies it.
fn is_pure_trap_block(func: &X86ISelFunction, block: Block) -> bool {
    let Some(b) = func.blocks.get(&block) else {
        return false;
    };
    if !b.successors.is_empty() {
        return false;
    }
    let mut saw_ud2 = false;
    for inst in &b.insts {
        match inst.opcode {
            X86Opcode::Nop => {}
            X86Opcode::Ud2 => saw_ud2 = true,
            _ => return false,
        }
    }
    saw_ud2
}

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
) -> Option<VReg> {
    let r = canon(single, func, guard_v);
    if r != canon(single, func, check_v) {
        return None;
    }
    // Cases 1 & 2: identical vregs, or a single-def (globally-fixed) root.
    if guard_v == check_v || single.contains_key(&r) {
        return Some(r);
    }
    // Case 3: multi-def root. Every copy on BOTH chains to `r` must have been
    // captured inside the covered window (so the caller's redefinition scan on
    // `r` proves each snapshot equals `r` at both compares). Note a guard-side
    // copy would have to be defined before `db_cmp_pos` (it is USED at the guard
    // compare) and so can never be "in window" — this admits exactly the
    // guard-uses-root-directly / check-uses-window-copy shape and rejects the
    // rest.
    let guard_ok = copy_chain_captured_in_window(single, func, guard_v, r, window);
    let check_ok = copy_chain_captured_in_window(single, func, check_v, r, window);
    if guard_ok && check_ok { Some(r) } else { None }
}

/// Build the single-def index (vregs with EXACTLY one definition in the
/// function). A hit means "this vreg has a unique, globally-fixed value".
fn build_single_def_index(func: &X86ISelFunction) -> HashMap<VReg, (Block, usize)> {
    let mut counts: HashMap<VReg, u32> = HashMap::new();
    let mut single: HashMap<VReg, (Block, usize)> = HashMap::new();
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
/// (before any flag-writer) means the flags are live -> not dead (keep the
/// compare); the first flag-WRITER clobbers them -> dead on that path (stop). A
/// block that neither reads nor fully clobbers before its terminator lets the
/// flags flow to its successors, which are then checked. A `visited` set bounds
/// the walk (loops terminate because a loop guard's own compare clobbers).
/// Reads are checked before writes so a read-modify-writes flag op (ADC/SBB)
/// counts as a reader.
fn compare_flags_dead_after(func: &X86ISelFunction, start: Block) -> bool {
    let mut visited: HashSet<Block> = HashSet::new();
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
            if x86_writes_flags(inst.opcode) {
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
fn find_eliminations(func: &X86ISelFunction) -> Vec<Elimination> {
    let single = build_single_def_index(func);
    let cfg = CfgAnalysis::compute(func);

    let mut elims: Vec<Elimination> = Vec::new();

    for &bb in &func.block_order {
        // (1) The bounds-check block ends in a CmpRR-driven conditional branch.
        let Some(check) = parse_cond_branch(func, bb) else {
            continue;
        };
        let Some(block) = func.blocks.get(&bb) else {
            continue;
        };
        if block.successors.len() != 2 {
            continue;
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
            continue; // malformed / self-loop successor set
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
            (false, false) => continue,
            (true, true) => continue,
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
            continue; // not a unique predecessor
        };
        let db = *db;
        if db == bb || !cfg.dominates(db, bb) {
            continue;
        }
        let Some(guard) = parse_cond_branch(func, db) else {
            continue;
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
            continue;
        };

        // (3) Identical comparison: same compare opcode, same left operand
        // (through window-captured copies), same right operand (register through
        // window-captured copies, or an identical immediate), and the guard-taken
        // predicate is the SAME unsigned relation the check needs. Guard-taken
        // then implies bounds-safe.
        if check.cmp_opcode != guard.cmp_opcode {
            continue;
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
        let Some(b0) = same_value_operand(&single, func, guard.op0, check.op0, covered_window)
        else {
            continue;
        };
        // Right operand: register/register (same-value) or identical immediate.
        // Register-vs-immediate and immediate mismatch never match.
        let rhs_root = match (check.rhs, guard.rhs) {
            (CmpRhs::Reg(rc), CmpRhs::Reg(rg)) => {
                match same_value_operand(&single, func, rg, rc, covered_window) {
                    Some(r) => Some(r),
                    None => continue,
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
            continue;
        }

        // (4) Neither operand's shared root vreg redefined between the guard and
        // the check (the covered window: `db`'s tail + `bb`'s head, `db` being
        // `bb`'s unique predecessor). This scan is what makes a multi-def root —
        // both the directly-used loop `iv` and the value snapshotted by any
        // window-captured copy — provably stable across the two compares. Collect
        // the roots involved (the left root, and the right root when the rhs is a
        // register).
        let mut roots: Vec<VReg> = vec![b0];
        if let Some(r) = rhs_root {
            roots.push(r);
        }
        if operand_redefined_between(func, db, guard.cmp_pos, bb, check.cmp_pos, &roots) {
            continue;
        }

        let remove_compare = compare_flags_dead_after(func, safe_target);

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
    let remap: HashMap<Block, Block> = func
        .block_order
        .iter()
        .enumerate()
        .map(|(i, &b)| (b, Block(i as u32)))
        .collect();

    let order = std::mem::take(&mut func.block_order);
    let mut new_blocks: HashMap<Block, X86ISelBlock> = HashMap::with_capacity(len);
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
}
