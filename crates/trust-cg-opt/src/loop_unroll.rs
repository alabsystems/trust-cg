// trust-cg-opt - Loop unrolling
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Loop unrolling pass for small, bounded loops.
//!
//! Fully unrolls loops with known constant trip count <= `TCG_MAX_UNROLL_TRIP_COUNT`
//! and body size <= `MAX_BODY_INSTS`. With profile-use data, hot loop headers
//! may use the slightly larger `HOT_MAX_TRIP_COUNT`. This eliminates loop
//! overhead (branch, compare) and exposes more optimization opportunities
//! (constant folding, CSE) for subsequent passes.
//!
//! # Algorithm
//!
//! 1. Compute dominator tree and loop analysis.
//! 2. For each loop (innermost first), detect constant trip counts, replicate
//!    small loop bodies, rewrite the back-edge to fall through after the last
//!    iteration, and remove the original loop structure.
//! 3. Return whether any loop was unrolled.
//!
//! # Constraints
//!
//! - Only single-latch, single-exit loops are candidates.
//! - The trip count must be statically determinable from the loop header.
//! - Nested loops are not unrolled (only innermost loops).
//!
//! Besides the 2-block copy-dialect full unroll, two multi-block full
//! unrollers live here: the bounded-early-exit unroll (Queens' trial loop,
//! `TCG_NO_BOUNDED_EARLY_EXIT_UNROLL`) and the diamond-body constant-trip
//! unroll (ReedSolomon's encode shift-register loop,
//! `TCG_NO_DIAMOND_CONST_TRIP_UNROLL`).
//!
//! Reference: LLVM `LoopUnrollPass.cpp`

use std::collections::{HashMap, HashSet};

use trust_cg_ir::{
    AArch64Opcode, AArch64Target, BlockId, CondCode, InstId, MachFunction, MachInst, MachOperand,
    PassId, ProvenanceMap, SourceLoc, TargetInfo, VReg,
};

use crate::addr_mode::is_encodable_offset;
use crate::dom::DomTree;
use crate::effects::{
    aarch64_for_each_def_position, aarch64_for_each_use_position, inst_produces_value,
};
use crate::loop_iv::analyze_trip_count;
use crate::loops::{LoopAnalysis, NaturalLoop};
use crate::pass_manager::{AnalysisCache, MachinePass};
use crate::pgo::ProfileHotness;

/// Maximum trip count for full unrolling.
const TCG_MAX_UNROLL_TRIP_COUNT: u64 = 4;

/// Maximum trip count for full unrolling when profile-use marks the loop
/// header block hot.
const HOT_MAX_TRIP_COUNT: u64 = 6;

/// Maximum number of non-terminator instructions in the loop body
/// (across all body blocks) for unrolling eligibility.
const MAX_BODY_INSTS: usize = 8;

/// Bounded-early-exit unroll: the largest compile-time loop limit `K` we will
/// fully unroll (Queens' trial loop is `j != 8`).
const BEE_MAX_TRIP_COUNT: u64 = 16;

/// Bounded-early-exit unroll: cap on total cloned instructions (code growth).
const BEE_MAX_CLONED_INSTS: usize = 500;

/// Const-addr full unroll (the SROA-enabling unroll): largest constant trip
/// count we fully unroll when the loop indexes a stack-slot array through
/// `Madd(iv, #elem_size, base)` address arithmetic that the unroller can
/// rewrite into per-iteration constant `AddRI base, #offset` addresses
/// (salsa20's `out[i] = x[i] + in[i]` tail loop, trip 16).
const CONST_ADDR_UNROLL_MAX_TRIP: u64 = 16;

/// Const-addr full unroll: body-size cap (the copy-loop bodies carry three
/// `Madd`+access pairs plus the IV update, slightly above `MAX_BODY_INSTS`).
const CONST_ADDR_UNROLL_MAX_BODY_INSTS: usize = 12;

/// Diamond-body constant-trip full unroll: the largest constant trip count we
/// fully unroll (ReedSolomon's encode shift-register loop is 15 trips).
const DIAMOND_UNROLL_MAX_TRIP: u64 = 16;

/// Diamond-body unroll: maximum number of loop body BLOCKS (header + up to two
/// arms + join/test block + latch = 5 for a full diamond; 6 leaves headroom
/// for one split arm).
const DIAMOND_UNROLL_MAX_BLOCKS: usize = 6;

/// Diamond-body unroll: maximum non-terminator instructions across the body.
const DIAMOND_UNROLL_MAX_BODY_INSTS: usize = 64;

/// Diamond-body unroll: cap on total cloned instructions (code growth).
const DIAMOND_UNROLL_MAX_CLONED_INSTS: usize = 640;

/// Compile-time kill switch for the bounded-early-exit full unroll: set
/// `TCG_NO_BOUNDED_EARLY_EXIT_UNROLL` (any value) to disable it.
fn bounded_early_exit_unroll_enabled() -> bool {
    std::env::var_os("TCG_NO_BOUNDED_EARLY_EXIT_UNROLL").is_none()
}

/// Compile-time kill switch for the const-addr full unroll: set
/// `TCG_NO_CONST_ADDR_UNROLL` (any value) to disable it.
fn const_addr_unroll_enabled() -> bool {
    std::env::var_os("TCG_NO_CONST_ADDR_UNROLL").is_none()
}

/// Compile-time kill switch for the diamond-body constant-trip full unroll:
/// set `TCG_NO_DIAMOND_CONST_TRIP_UNROLL` (any value) to disable it.
fn diamond_unroll_enabled() -> bool {
    std::env::var_os("TCG_NO_DIAMOND_CONST_TRIP_UNROLL").is_none()
}

/// Compile-time kill switch for per-clone vreg renaming inside the
/// bounded-early-exit full unroll: set `TCG_NO_BEE_UNROLL_RENAME` (any value) to
/// fall back to the old vreg-reusing clone (for A/B and object-identity checks).
fn bee_unroll_rename_enabled() -> bool {
    std::env::var_os("TCG_NO_BEE_UNROLL_RENAME").is_none()
}

/// Kill switch for the profile-hotness trip-count bump: set
/// `TCG_PGO_NO_HOT_UNROLL` (any value) to keep the static
/// `TCG_MAX_UNROLL_TRIP_COUNT` cap even when a profile marks the loop header
/// hot (for PGO effect attribution A/B runs). Inert without a profile.
fn pgo_hot_unroll_enabled() -> bool {
    std::env::var_os("TCG_PGO_NO_HOT_UNROLL").is_none()
}

/// Loop unrolling pass.
#[derive(Debug, Clone, Default)]
pub struct LoopUnroll {
    profile_hotness: Option<ProfileHotness>,
}

impl MachinePass for LoopUnroll {
    fn name(&self) -> &str {
        "loop-unroll"
    }

    fn run(&mut self, func: &mut MachFunction) -> bool {
        let dom = DomTree::compute(func);
        let loop_analysis = LoopAnalysis::compute(func, &dom);
        Self::run_with_loop_analysis(func, &loop_analysis, self.profile_hotness.as_ref(), None)
    }

    fn run_with_analyses(&mut self, func: &mut MachFunction, analyses: &mut AnalysisCache) -> bool {
        let loop_analysis = analyses.loop_analysis(func).clone();
        Self::run_with_loop_analysis(func, &loop_analysis, self.profile_hotness.as_ref(), None)
    }

    fn run_with_provenance(
        &mut self,
        func: &mut MachFunction,
        provenance: &mut ProvenanceMap,
    ) -> bool {
        let dom = DomTree::compute(func);
        let loop_analysis = LoopAnalysis::compute(func, &dom);
        Self::run_with_loop_analysis(
            func,
            &loop_analysis,
            self.profile_hotness.as_ref(),
            Some(provenance),
        )
    }

    fn run_with_analyses_and_provenance(
        &mut self,
        func: &mut MachFunction,
        analyses: &mut AnalysisCache,
        provenance: &mut ProvenanceMap,
    ) -> bool {
        let loop_analysis = analyses.loop_analysis(func).clone();
        Self::run_with_loop_analysis(
            func,
            &loop_analysis,
            self.profile_hotness.as_ref(),
            Some(provenance),
        )
    }
}

impl LoopUnroll {
    /// Create a loop-unroll pass with optional profile-use hotness.
    pub fn new(profile_hotness: Option<ProfileHotness>) -> Self {
        Self { profile_hotness }
    }

    fn run_with_loop_analysis(
        func: &mut MachFunction,
        loop_analysis: &LoopAnalysis,
        profile_hotness: Option<&ProfileHotness>,
        mut provenance: Option<&mut ProvenanceMap>,
    ) -> bool {
        if loop_analysis.is_empty() {
            return false;
        }

        let mut changed = false;

        // Collect innermost loops only (no children).
        let all_loops: Vec<NaturalLoop> = loop_analysis.all_loops().cloned().collect();

        let innermost: Vec<&NaturalLoop> = all_loops
            .iter()
            .filter(|lp| {
                // A loop is innermost if no other loop's parent is this loop.
                !all_loops
                    .iter()
                    .any(|other| other.parent == Some(lp.header))
            })
            .collect();

        // Def map for the whole function: vreg -> the instructions that define
        // it (operand 0 of a value-producing inst). The importer's SSA-destructed
        // MIR is NOT SSA (loop-carried vregs are defined by copies in both the
        // preheader and the latch), so a vreg may have several defs.
        let def_map = build_def_map(func);

        // Trip-count simulation cap: with the const-addr unroll enabled the
        // copy-counted recognizer must be able to PROVE trip counts up to
        // `CONST_ADDR_UNROLL_MAX_TRIP`; with its kill switch set, keep the
        // historical bound so behavior is bit-identical.
        let sim_cap = if const_addr_unroll_enabled() {
            HOT_MAX_TRIP_COUNT.max(CONST_ADDR_UNROLL_MAX_TRIP) + 1
        } else {
            HOT_MAX_TRIP_COUNT + 1
        };

        for lp in &innermost {
            let max_trip_count = max_trip_count_for_loop(func, lp, profile_hotness);

            // Primary path: the real importer dialect (copy-based / rotated /
            // CmpRR+CSet+CmpRI+BCond+B, with LICM-hoisted bounds), including the
            // exactly-constant floating-point IV variant. See
            // `analyze_copy_counted_loop`.
            if let Some(cl) = analyze_copy_counted_loop(func, lp, &def_map, sim_cap) {
                if cl.trip_count > 0
                    && cl.trip_count <= max_trip_count
                    && cl.cloned_body_len() <= MAX_BODY_INSTS
                    && unroll_copy_based(func, lp, &cl, None, provenance.as_deref_mut())
                {
                    changed = true;
                } else if const_addr_unroll_enabled()
                    && cl.trip_count > max_trip_count
                    && cl.trip_count <= CONST_ADDR_UNROLL_MAX_TRIP
                    && cl.cloned_body_len() <= CONST_ADDR_UNROLL_MAX_BODY_INSTS
                    && let Some(plan) = plan_const_addr_unroll(func, lp, &cl, &def_map)
                    && unroll_copy_based(func, lp, &cl, Some(&plan), provenance.as_deref_mut())
                {
                    changed = true;
                }
                // A recognized copy-based loop never matches the legacy Phi
                // recognizer; do not double-process.
                continue;
            }

            // Bounded-max-trip FULL unroll that RETAINS early exits: the
            // multi-block trial-loop shape whose backedge is guarded by
            // `AndRR(CSet(iv_next != K), CSet(dynamic))` with a compile-time
            // constant limit K and constant step (Queens' `Try`). See
            // `analyze_bounded_early_exit_loop`. Kill switch:
            // `TCG_NO_BOUNDED_EARLY_EXIT_UNROLL`.
            if bounded_early_exit_unroll_enabled()
                && let Some(bel) = analyze_bounded_early_exit_loop(func, lp, &def_map)
            {
                if unroll_bounded_early_exit(func, lp, &bel, provenance.as_deref_mut()) {
                    changed = true;
                }
                continue;
            }

            // Diamond-body constant-trip FULL unroll: the multi-block loop whose
            // body carries internal if/else control flow (diamond/triangle) but
            // whose single exit test is a pure compile-time-provable IV trip
            // test (ReedSolomon's encode shift-register loop). See
            // `analyze_diamond_const_trip_loop`. Kill switch:
            // `TCG_NO_DIAMOND_CONST_TRIP_UNROLL`.
            if diamond_unroll_enabled()
                && let Some(dcl) = analyze_diamond_const_trip_loop(func, lp, &def_map)
            {
                if unroll_diamond_const_trip(func, lp, &dcl, provenance.as_deref_mut()) {
                    changed = true;
                }
                continue;
            }

            // Legacy path: the synthetic SSA/Phi + CmpRI shape (kept working for
            // regression coverage; the importer never emits it).
            if let Some(trip_count) = analyze_trip_count(func, lp)
                && trip_count <= max_trip_count
                && trip_count > 0
            {
                let body_inst_count = count_body_insts(func, lp);
                if body_inst_count <= MAX_BODY_INSTS
                    && unroll_loop(func, lp, trip_count as usize, provenance.as_deref_mut())
                {
                    changed = true;
                }
            }
        }

        changed
    }
}

fn loop_unroll_pass_id() -> PassId {
    PassId::new("loop-unroll")
}

// ===========================================================================
// Copy-based (real importer dialect) counted-loop recognizer + full unroller.
//
// The trust-ir importer lowers `for`/`do-while` counted loops to a rotated,
// SSA-destructed MIR that the legacy Phi/CmpRI recognizer above never matches:
//
//   preheader:                      ; single unconditional entry to header
//     v_init  = Movz #c   (or v_init = base+c chain; may be LICM-hoisted)
//     v_iv    = MovR v_init          ; phi-copy for the IV (init edge)
//     v_lim   = ...bound...          ; LICM-hoisted loop bound (const or affine)
//     B header
//   header:
//     ...body work using v_iv...
//     v_next  = AddRI v_iv, #step    ; IV increment lives in the HEADER (rotated)
//     [v_cmp  = MovR/trunc v_next]   ; optional narrowing for the compare
//     CmpRR   v_cmp, v_lim           ; the icmp (or CmpRI v_cmp, #imm)
//     CSet    v_cond, <cc_set>       ; materialize the boolean
//     CmpRI   v_cond, #0             ; br_if's own compare (v_cond is NOT the IV)
//     BCond   [NE, T]                ; br_if true-edge
//     B       F                      ; br_if false-edge  <-- header's LAST inst
//   latch:
//     v_iv    = MovR v_next          ; phi-copy for the IV (back edge)
//     B header
//
// The whole loop-carried state is threaded through the shared IV register via
// the preheader/latch phi-copies. Full unrolling therefore only has to REPLICATE
// the body blocks verbatim (NO renaming — the copies already thread values) and
// strip the loop-control terminators. This is provably value-preserving for a
// straight-line unroll because every loop-carried value flows through a phi-copy
// and every other value is recomputed each iteration.
//
// SOUNDNESS of the trip count:
//   * Integer, constant init & bound: simulated exactly with W-bit wraparound.
//   * Integer, symbolic init & bound sharing a base (e.g. `IntLoc..IntLoc+1`):
//     only EQ/NE exit tests are accepted, where the shared base cancels mod 2^W
//     so the difference `bound-init` is exact for every runtime base value.
//   * Floating-point: ONLY exactly-representable integer-valued constant
//     init/step/bound with a tiny trip count. A symbolic FP init is REFUSED
//     (e.g. `init+1.0` may round for large init, so the trip count is not
//     statically provable — clang does not unroll it either).
// Anything outside these fails closed (no unroll).
// ===========================================================================

/// A recognized copy-based counted loop, ready to fully unroll.
struct CopyCountedLoop {
    /// Statically-proven number of body executions.
    trip_count: u64,
    /// The loop-control instructions in the header to delete on unroll:
    /// the flag-setting compare, the `CSet`, and the `CmpRI cond, #0`.
    control_insts: Vec<InstId>,
    /// The header's conditional branch (`BCond`) — removed on unroll.
    bcond: InstId,
    /// The header's trailing unconditional branch (`B F`) — removed on unroll.
    header_uncond_b: InstId,
    /// The in-loop successor of the header (the block the body continues into;
    /// the latch for the clean two-block loop shape we require).
    in_loop_succ: BlockId,
    /// The exit block (the header successor outside the loop body).
    exit_block: BlockId,
    /// The instructions (in body order) that will be cloned per extra iteration.
    body_insts: Vec<InstId>,
    /// The loop-carried IV `(iv_vreg, init, step)` when init and bound are
    /// ABSOLUTE constants (integer path only). Enables the const-addr unroll.
    const_iv: Option<(VReg, i128, i128)>,
    /// The header's IV-increment instruction (`AddRI`/`SubRI`) and its
    /// destination vreg, when `const_iv` is set.
    iv_inc: Option<(InstId, VReg)>,
}

impl CopyCountedLoop {
    fn cloned_body_len(&self) -> usize {
        self.body_insts.len()
    }
}

/// A value expressed as `base + offset` (base `None` => a pure constant).
#[derive(Clone, Copy, PartialEq, Eq)]
struct Affine {
    base: Option<VReg>,
    offset: i128,
}

/// Normalized loop-exit comparison of the IV expression `X` against the bound
/// `L`: the loop exits when `X REL L` holds.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Rel {
    Eq,
    Ne,
    SLt,
    SLe,
    SGt,
    SGe,
    ULt,
    ULe,
    UGt,
    UGe,
}

/// Build a def map: vreg -> the instructions defining it (operand 0 of a
/// value-producing instruction). Non-SSA MIR may map a vreg to several defs.
fn build_def_map(func: &MachFunction) -> HashMap<VReg, Vec<InstId>> {
    let mut map: HashMap<VReg, Vec<InstId>> = HashMap::new();
    for &block_id in &func.block_order {
        for &inst_id in &func.block(block_id).insts {
            let inst = func.inst(inst_id);
            if inst_produces_value(inst)
                && let Some(v) = inst.operands.first().and_then(|op| op.as_vreg())
            {
                map.entry(v).or_default().push(inst_id);
            }
        }
    }
    map
}

/// The single defining instruction of `v`, or `None` if it has zero or several
/// defs (a multiply-defined vreg is not a loop-invariant we can trace).
fn unique_def<'a>(
    func: &'a MachFunction,
    def_map: &HashMap<VReg, Vec<InstId>>,
    v: VReg,
) -> Option<&'a MachInst> {
    let defs = def_map.get(&v)?;
    if defs.len() != 1 {
        return None;
    }
    Some(func.inst(defs[0]))
}

/// Express `v` as `base + offset`, walking single-def copy/extend/add chains.
///
/// Transparent ops (copies, truncations via `MovR`, sign/zero extensions) keep
/// the low bits, so the resulting affine form is exact modulo the comparison
/// width — which is all the EQ/NE difference reasoning relies on (the shared
/// base cancels). A vreg whose unique def is not one of these becomes the base
/// itself (an opaque symbol); a multiply-defined vreg stops the walk as a base.
fn affine_of(func: &MachFunction, def_map: &HashMap<VReg, Vec<InstId>>, v: VReg) -> Affine {
    // Guard against pathological cycles in malformed MIR.
    let mut cur = v;
    let mut offset: i128 = 0;
    for _ in 0..64 {
        let Some(inst) = unique_def(func, def_map, cur) else {
            return Affine {
                base: Some(cur),
                offset,
            };
        };
        match inst.opcode {
            AArch64Opcode::Movz => {
                if let Some((dst, value)) = crate::reaching_const::movz_value(inst)
                    && dst == cur
                {
                    return Affine {
                        base: None,
                        offset: offset + i128::from(value),
                    };
                }
                return Affine {
                    base: Some(cur),
                    offset,
                };
            }
            AArch64Opcode::MovI => {
                if let Some(imm) = inst.operands.get(1).and_then(|op| op.as_imm())
                    && inst.operands.len() == 2
                {
                    return Affine {
                        base: None,
                        offset: offset + imm as i128,
                    };
                }
                return Affine {
                    base: Some(cur),
                    offset,
                };
            }
            AArch64Opcode::AddRI => {
                if let (Some(src), Some(imm)) = (
                    inst.operands.get(1).and_then(|op| op.as_vreg()),
                    inst.operands.get(2).and_then(|op| op.as_imm()),
                ) {
                    offset += imm as i128;
                    cur = src;
                    continue;
                }
                return Affine {
                    base: Some(cur),
                    offset,
                };
            }
            AArch64Opcode::SubRI => {
                if let (Some(src), Some(imm)) = (
                    inst.operands.get(1).and_then(|op| op.as_vreg()),
                    inst.operands.get(2).and_then(|op| op.as_imm()),
                ) {
                    offset -= imm as i128;
                    cur = src;
                    continue;
                }
                return Affine {
                    base: Some(cur),
                    offset,
                };
            }
            AArch64Opcode::MovR
            | AArch64Opcode::Copy
            | AArch64Opcode::Sxtw
            | AArch64Opcode::Uxtw
            | AArch64Opcode::Sxth
            | AArch64Opcode::Uxth
            | AArch64Opcode::Sxtb
            | AArch64Opcode::Uxtb => {
                if let Some(src) = inst.operands.get(1).and_then(|op| op.as_vreg()) {
                    cur = src;
                    continue;
                }
                return Affine {
                    base: Some(cur),
                    offset,
                };
            }
            _ => {
                return Affine {
                    base: Some(cur),
                    offset,
                };
            }
        }
    }
    Affine {
        base: Some(cur),
        offset,
    }
}

/// Resolve `v` through single-def transparent copies/extends to the underlying
/// value-defining vreg (used to find the IV increment behind a narrowing copy).
fn resolve_through_copies(
    func: &MachFunction,
    def_map: &HashMap<VReg, Vec<InstId>>,
    v: VReg,
) -> VReg {
    let mut cur = v;
    for _ in 0..64 {
        let Some(inst) = unique_def(func, def_map, cur) else {
            return cur;
        };
        match inst.opcode {
            AArch64Opcode::MovR
            | AArch64Opcode::Copy
            | AArch64Opcode::Sxtw
            | AArch64Opcode::Uxtw
            | AArch64Opcode::Sxth
            | AArch64Opcode::Uxth
            | AArch64Opcode::Sxtb
            | AArch64Opcode::Uxtb => {
                if let Some(src) = inst.operands.get(1).and_then(|op| op.as_vreg()) {
                    cur = src;
                    continue;
                }
                return cur;
            }
            _ => return cur,
        }
    }
    cur
}

/// Decode a condition-code immediate operand into a [`CondCode`].
fn cc_from_operand(op: &MachOperand) -> Option<CondCode> {
    let raw = op.as_imm()? as u8;
    match raw {
        0b0000 => Some(CondCode::EQ),
        0b0001 => Some(CondCode::NE),
        0b0010 => Some(CondCode::HS),
        0b0011 => Some(CondCode::LO),
        0b0100 => Some(CondCode::MI),
        0b0101 => Some(CondCode::PL),
        0b0110 => Some(CondCode::VS),
        0b0111 => Some(CondCode::VC),
        0b1000 => Some(CondCode::HI),
        0b1001 => Some(CondCode::LS),
        0b1010 => Some(CondCode::GE),
        0b1011 => Some(CondCode::LT),
        0b1100 => Some(CondCode::GT),
        0b1101 => Some(CondCode::LE),
        _ => None,
    }
}

/// Relation `a REL b` that a `CSet cc` materializes from an INTEGER `CMP a, b`.
fn rel_from_int_cc(cc: CondCode) -> Option<Rel> {
    match cc {
        CondCode::EQ => Some(Rel::Eq),
        CondCode::NE => Some(Rel::Ne),
        CondCode::HS => Some(Rel::UGe),
        CondCode::LO => Some(Rel::ULt),
        CondCode::HI => Some(Rel::UGt),
        CondCode::LS => Some(Rel::ULe),
        CondCode::GE => Some(Rel::SGe),
        CondCode::LT => Some(Rel::SLt),
        CondCode::GT => Some(Rel::SGt),
        CondCode::LE => Some(Rel::SLe),
        // MI/PL/VS/VC are not clean a-vs-b relations.
        _ => None,
    }
}

/// Relation `a REL b` that a `CSet cc` materializes from an `FCMP a, b`.
///
/// Operands are guaranteed exact non-NaN integers on the FP path, so ordered
/// and unordered variants coincide; we model them as signed real relations.
fn rel_from_fp_cc(cc: CondCode) -> Option<Rel> {
    match cc {
        CondCode::EQ => Some(Rel::Eq),
        CondCode::NE => Some(Rel::Ne),
        CondCode::GT | CondCode::HI => Some(Rel::SGt),
        CondCode::GE | CondCode::HS => Some(Rel::SGe),
        CondCode::MI | CondCode::LO => Some(Rel::SLt),
        CondCode::LE | CondCode::LS => Some(Rel::SLe),
        _ => None,
    }
}

/// Swap the operands of a relation: `a REL b` -> `b REL' a`.
fn swap_rel(r: Rel) -> Rel {
    match r {
        Rel::Eq => Rel::Eq,
        Rel::Ne => Rel::Ne,
        Rel::SLt => Rel::SGt,
        Rel::SGt => Rel::SLt,
        Rel::SLe => Rel::SGe,
        Rel::SGe => Rel::SLe,
        Rel::ULt => Rel::UGt,
        Rel::UGt => Rel::ULt,
        Rel::ULe => Rel::UGe,
        Rel::UGe => Rel::ULe,
    }
}

/// Logical negation of a relation.
fn negate_rel(r: Rel) -> Rel {
    match r {
        Rel::Eq => Rel::Ne,
        Rel::Ne => Rel::Eq,
        Rel::SLt => Rel::SGe,
        Rel::SGe => Rel::SLt,
        Rel::SGt => Rel::SLe,
        Rel::SLe => Rel::SGt,
        Rel::ULt => Rel::UGe,
        Rel::UGe => Rel::ULt,
        Rel::UGt => Rel::ULe,
        Rel::ULe => Rel::UGt,
    }
}

/// Sign/zero-wrap `v` to `width` bits, returning (signed, unsigned) values.
///
/// For `width >= 127` (the exact-FP path, where values are small integers)
/// no wrapping is applied — avoiding an i128 shift overflow.
fn wrap_width(v: i128, width: u32) -> (i128, i128) {
    if width == 0 || width >= 127 {
        return (v, v);
    }
    let mask: i128 = (1i128 << width) - 1;
    let u = v & mask;
    let s = if (u >> (width - 1)) & 1 == 1 {
        u - (1i128 << width)
    } else {
        u
    };
    (s, u)
}

/// Evaluate `x REL l` at a given register width (absolute values known).
fn eval_rel(r: Rel, x: i128, l: i128, width: u32) -> bool {
    let (xs, xu) = wrap_width(x, width);
    let (ls, lu) = wrap_width(l, width);
    match r {
        Rel::Eq => xu == lu,
        Rel::Ne => xu != lu,
        Rel::SLt => xs < ls,
        Rel::SLe => xs <= ls,
        Rel::SGt => xs > ls,
        Rel::SGe => xs >= ls,
        Rel::ULt => xu < lu,
        Rel::ULe => xu <= lu,
        Rel::UGt => xu > lu,
        Rel::UGe => xu >= lu,
    }
}

/// Compute the number of body executions of a rotated counted loop whose IV
/// expression `X = init + m*step` (evaluated after the m-th body) triggers exit
/// when `X exit_rel bound` first holds. Returns `None` (fail closed) when the
/// trip count cannot be proven within a small bound.
fn simulate_trip(
    init: Affine,
    bound: Affine,
    step: i128,
    exit_rel: Rel,
    width: u32,
    sim_cap: u64,
) -> Option<u64> {
    if init.base != bound.base || step == 0 {
        return None;
    }
    // Simulate up to one past the largest count we would ever unroll.
    let sim_bound = sim_cap;

    if init.base.is_none() {
        // Absolute init & bound: exact W-bit simulation, all relations sound.
        let init_v = init.offset;
        let bound_v = bound.offset;
        for m in 1..=sim_bound {
            let x = init_v + (m as i128) * step;
            if eval_rel(exit_rel, x, bound_v, width) {
                return Some(m);
            }
        }
        None
    } else {
        // Symbolic shared base: only EQ/NE cancel the base soundly.
        let d = bound.offset - init.offset; // (bound - init), base cancels
        for m in 1..=sim_bound {
            let g = (m as i128) * step - d; // (X - bound)
            let holds = match exit_rel {
                Rel::Eq => g == 0,
                Rel::Ne => g != 0,
                _ => return None,
            };
            if holds {
                return Some(m);
            }
        }
        None
    }
}

/// The nearest flag-writing instruction preceding position `pos` in `insts`.
fn nearest_flag_setter(func: &MachFunction, insts: &[InstId], pos: usize) -> Option<InstId> {
    for i in (0..pos).rev() {
        let inst = func.inst(insts[i]);
        if AArch64Target::writes_flags(inst.opcode) {
            return Some(insts[i]);
        }
    }
    None
}

/// Recognize the real importer's copy-based / rotated counted loop and prove a
/// constant trip count. Fails closed on anything it cannot prove exactly.
fn analyze_copy_counted_loop(
    func: &MachFunction,
    lp: &NaturalLoop,
    def_map: &HashMap<VReg, Vec<InstId>>,
    sim_cap: u64,
) -> Option<CopyCountedLoop> {
    let preheader = lp.preheader?;
    let header = lp.header;
    let latch = lp.latch;

    // Require the clean two-block natural loop the importer emits: a header and
    // a distinct latch whose only job (besides the back edge) is the phi-copies.
    if header == latch || lp.body.len() != 2 || !lp.body.contains(&latch) {
        return None;
    }
    // header preds == {preheader, latch}; latch is header's back-edge pred.
    let hpreds = &func.block(header).preds;
    if hpreds.len() != 2 || !hpreds.contains(&preheader) || !hpreds.contains(&latch) {
        return None;
    }
    // latch -> header only.
    let lsuccs = &func.block(latch).succs;
    if lsuccs.len() != 1 || lsuccs[0] != header {
        return None;
    }
    // latch's only predecessor is the header: the unroller appends clones into
    // the latch, so no other path may enter it.
    let lpreds = &func.block(latch).preds;
    if lpreds.len() != 1 || lpreds[0] != header {
        return None;
    }
    // header -> {exit, latch}.
    let hsuccs = &func.block(header).succs;
    if hsuccs.len() != 2 || !hsuccs.contains(&latch) {
        return None;
    }
    let exit_block = *hsuccs.iter().find(|&&s| s != latch)?;
    if lp.body.contains(&exit_block) {
        return None;
    }

    // ---- Header terminator pattern: ... CmpRI cond,#0 ; BCond [cc,T] ; B F ----
    let hinsts = func.block(header).insts.clone();
    if hinsts.len() < 4 {
        return None;
    }
    let b_last = *hinsts.last()?;
    let bcond = hinsts[hinsts.len() - 2];
    let brif_cmp = hinsts[hinsts.len() - 3];

    let b_inst = func.inst(b_last);
    if b_inst.opcode != AArch64Opcode::B {
        return None;
    }
    let bcond_inst = func.inst(bcond);
    if bcond_inst.opcode != AArch64Opcode::BCond {
        return None;
    }
    // BCond operands: [Imm(cc), Block(T)].
    let cc_br = cc_from_operand(bcond_inst.operands.first()?)?;
    let t_target = match bcond_inst.operands.get(1)? {
        MachOperand::Block(b) => *b,
        _ => return None,
    };
    // br_if lowering only ever emits B.NE (branch when cond != 0). Accept EQ too
    // (cond == 0) for completeness; reject other codes.
    let taken_when_cond_true = match cc_br {
        CondCode::NE => true,
        CondCode::EQ => false,
        _ => return None,
    };

    // CmpRI cond, #0.
    let brif_inst = func.inst(brif_cmp);
    if brif_inst.opcode != AArch64Opcode::CmpRI
        || brif_inst.operands.get(1).and_then(|op| op.as_imm()) != Some(0)
    {
        return None;
    }
    let cond_vreg = brif_inst.operands.first()?.as_vreg()?;

    // CSet cond_vreg, cc_set — the unique def of cond in the header.
    let cset_id = *def_map.get(&cond_vreg)?.iter().find(|&&id| {
        func.inst(id).opcode == AArch64Opcode::CSet && func.block(header).insts.contains(&id)
    })?;
    let cset_inst = func.inst(cset_id);
    if cset_inst.operands.first()?.as_vreg()? != cond_vreg {
        return None;
    }
    let cc_set = cc_from_operand(cset_inst.operands.get(1)?)?;

    // The compare feeding the CSet: the nearest flag-setter before it.
    let cset_pos = hinsts.iter().position(|&id| id == cset_id)?;
    let flag_cmp = nearest_flag_setter(func, &hinsts, cset_pos)?;
    let flag_inst = func.inst(flag_cmp);
    let is_fp = flag_inst.opcode == AArch64Opcode::Fcmp;

    // Extract the two compared operands (a, b) and whether it is a CmpRI.
    let (op_a, op_b_vreg, op_b_imm) = match flag_inst.opcode {
        AArch64Opcode::CmpRR | AArch64Opcode::Fcmp => (
            flag_inst.operands.first()?.as_vreg()?,
            Some(flag_inst.operands.get(1)?.as_vreg()?),
            None,
        ),
        AArch64Opcode::CmpRI => (
            flag_inst.operands.first()?.as_vreg()?,
            None,
            Some(flag_inst.operands.get(1)?.as_imm()?),
        ),
        _ => return None,
    };

    // ---- Identify the IV increment among the compare operands ----
    // For each candidate compare operand, resolve copies and check whether its
    // unique def is `AddRI/SubRI(iv, #step)` (integer) or `FaddRR/FsubRR iv, k`
    // (float) whose source `iv` is loop-carried (a phi-copy in the latch).
    let candidates: Vec<(VReg, bool)> = match (op_b_vreg, op_b_imm) {
        (Some(b), None) => vec![(op_a, true), (b, false)],
        (None, Some(_)) => vec![(op_a, true)],
        _ => return None,
    };

    let mut found: Option<IvInc> = None;
    for (cand, is_a) in candidates {
        if let Some(inc) = try_iv_increment(func, def_map, lp, cand, is_fp) {
            if found.is_some() {
                // Ambiguous: both operands look like an IV — bail.
                return None;
            }
            found = Some(IvInc { is_a, ..inc });
        }
    }
    let iv = found?;

    // ---- The bound is the OTHER compare operand ----
    // Determine init and bound as affines (integer) or exact FP constants.
    let (init_aff, bound_aff, width) = if is_fp {
        // FP: init/step/bound must be exactly-representable integer constants.
        let init = fp_int_const(func, def_map, iv.init_src)?;
        let step = iv.fp_step?;
        let bound_val = if iv.is_a {
            // bound is op_b_vreg
            fp_int_const(func, def_map, op_b_vreg?)?
        } else {
            fp_int_const(func, def_map, op_a)?
        };
        return finish_fp(
            func,
            lp,
            header,
            latch,
            exit_block,
            &hinsts,
            flag_cmp,
            cset_id,
            brif_cmp,
            bcond,
            b_last,
            init,
            step,
            bound_val,
            iv.is_a,
            cc_set,
            t_target,
            exit_block,
            taken_when_cond_true,
        );
    } else {
        let init = affine_of(func, def_map, iv.init_src);
        let bound = if let Some(imm) = op_b_imm {
            Affine {
                base: None,
                offset: imm as i128,
            }
        } else if iv.is_a {
            affine_of(func, def_map, op_b_vreg?)
        } else {
            affine_of(func, def_map, op_a)
        };
        // Use the COMPARE width (operand `a`), not the IV register width: the IV
        // may be compared at a narrower width via a truncating copy, and the
        // exact wraparound simulation must model the width the flags see.
        let w = width_of(op_a);
        (init, bound, w)
    };

    // Normalize the relation onto (X = iv_next, L = bound).
    let p = rel_from_int_cc(cc_set)?;
    // If the IV expr is operand `a`, keep P; else swap so it reads X-vs-L.
    let rel_xl = if iv.is_a { p } else { swap_rel(p) };
    // Exit when we branch to the exit block.
    let goes_to_exit_when_taken = t_target == exit_block;
    let exit_when_cond_true = goes_to_exit_when_taken == taken_when_cond_true;
    let exit_rel = if exit_when_cond_true {
        rel_xl
    } else {
        negate_rel(rel_xl)
    };

    let trip_count = simulate_trip(init_aff, bound_aff, iv.int_step, exit_rel, width, sim_cap)?;

    let control_insts = vec![flag_cmp, cset_id, brif_cmp];
    let body_insts = collect_copy_body_insts(func, lp, &control_insts, bcond, b_last);

    // Absolute-constant init: expose the IV for the const-addr unroll path.
    let const_iv = (init_aff.base.is_none()).then_some((iv.iv_vreg, init_aff.offset, iv.int_step));
    let iv_inc = const_iv.map(|_| (iv.inc_inst, iv.inc_dst));

    Some(CopyCountedLoop {
        trip_count,
        control_insts,
        bcond,
        header_uncond_b: b_last,
        in_loop_succ: latch,
        exit_block,
        body_insts,
        const_iv,
        iv_inc,
    })
}

/// Details of a recognized IV-increment.
struct IvInc {
    /// The preheader source of the IV (its init value).
    init_src: VReg,
    /// Integer step (signed); meaningless when `fp_step` is set.
    int_step: i128,
    /// FP step, if this is a float IV.
    fp_step: Option<i128>,
    /// Whether the IV expression was compare operand `a` (set later).
    is_a: bool,
    /// The loop-carried IV vreg (phi-copied through preheader + latch).
    iv_vreg: VReg,
    /// The increment instruction (`AddRI`/`SubRI`/`FaddRR`/`FsubRR`).
    inc_inst: InstId,
    /// The increment's destination vreg.
    inc_dst: VReg,
}

/// Try to interpret `cand` (a compare operand) as the incremented IV: resolve
/// copies to `AddRI/SubRI(iv,#k)` (or `FaddRR/FsubRR iv, kconst`) whose source
/// `iv` is loop-carried via preheader+latch phi-copies.
fn try_iv_increment(
    func: &MachFunction,
    def_map: &HashMap<VReg, Vec<InstId>>,
    lp: &NaturalLoop,
    cand: VReg,
    is_fp: bool,
) -> Option<IvInc> {
    let resolved = resolve_through_copies(func, def_map, cand);
    let inc_defs = def_map.get(&resolved)?;
    if inc_defs.len() != 1 {
        return None;
    }
    let inc_id = inc_defs[0];
    let inc_inst = func.inst(inc_id);

    let (iv, int_step, fp_step) = if is_fp {
        match inc_inst.opcode {
            AArch64Opcode::FaddRR | AArch64Opcode::FsubRR => {
                let iv = inc_inst.operands.get(1)?.as_vreg()?;
                let kv = inc_inst.operands.get(2)?.as_vreg()?;
                let k = fp_int_const(func, def_map, kv)?;
                let step = if inc_inst.opcode == AArch64Opcode::FaddRR {
                    k
                } else {
                    -k
                };
                (iv, 0i128, Some(step))
            }
            _ => return None,
        }
    } else {
        match inc_inst.opcode {
            AArch64Opcode::AddRI => {
                let iv = inc_inst.operands.get(1)?.as_vreg()?;
                let k = inc_inst.operands.get(2)?.as_imm()? as i128;
                (iv, k, None)
            }
            AArch64Opcode::SubRI => {
                let iv = inc_inst.operands.get(1)?.as_vreg()?;
                let k = inc_inst.operands.get(2)?.as_imm()? as i128;
                (iv, -k, None)
            }
            _ => return None,
        }
    };

    // `iv` must be loop-carried: defined in both the preheader and the latch,
    // with the latch def being the phi-copy `MovR iv, <back-edge value>`.
    let preheader = lp.preheader?;
    let iv_defs = def_map.get(&iv)?;
    let ph_def = iv_defs
        .iter()
        .find(|&&id| func.block(preheader).insts.contains(&id))?;
    let latch_def = iv_defs
        .iter()
        .find(|&&id| func.block(lp.latch).insts.contains(&id))?;
    // The latch def must be a copy that threads EXACTLY the incremented value
    // (`resolved` == the AddRI/FaddRR result) back into the IV. Otherwise the IV
    // advances by something other than `step` each iteration and the modeled
    // trip count would be wrong — fail closed.
    let latch_inst = func.inst(*latch_def);
    if !latch_inst.opcode.is_move() {
        return None;
    }
    let latch_src = latch_inst.operands.get(1)?.as_vreg()?;
    if resolve_through_copies(func, def_map, latch_src) != resolved {
        return None;
    }
    // Preheader def source is the init value.
    let ph_inst = func.inst(*ph_def);
    let init_src = if ph_inst.opcode.is_move() {
        ph_inst.operands.get(1)?.as_vreg().unwrap_or(iv)
    } else {
        // init materialized directly into the IV register (e.g. Movz iv, #c).
        iv
    };

    Some(IvInc {
        init_src,
        int_step,
        fp_step,
        is_a: false,
        iv_vreg: iv,
        inc_inst: inc_id,
        inc_dst: resolved,
    })
}

/// The register width (in bits) of a vreg's class, defaulting to 64.
fn width_of(v: VReg) -> u32 {
    use trust_cg_ir::RegClass::*;
    match v.class {
        Gpr32 => 32,
        _ => 64,
    }
}

/// If `v`'s value is an exactly-representable integer-valued `f64` constant
/// (materialized via `FmovImm`), return it as an integer; else `None`.
fn fp_int_const(
    func: &MachFunction,
    def_map: &HashMap<VReg, Vec<InstId>>,
    v: VReg,
) -> Option<i128> {
    let resolved = resolve_through_copies(func, def_map, v);
    let inst = unique_def(func, def_map, resolved)?;
    let fv = match inst.opcode {
        AArch64Opcode::FmovImm => match inst.operands.get(1)? {
            MachOperand::FImm(f) => *f,
            _ => return None,
        },
        _ => return None,
    };
    // Exactness gate: finite, integer-valued, and small enough that every value
    // in the (tiny) simulated range is exactly representable.
    if !fv.is_finite() || fv.fract() != 0.0 || fv.abs() > (1i64 << 40) as f64 {
        return None;
    }
    Some(fv as i128)
}

/// Finalize a float-IV loop once init/step/bound are known exact integers.
#[allow(clippy::too_many_arguments)]
fn finish_fp(
    func: &MachFunction,
    lp: &NaturalLoop,
    _header: BlockId,
    latch: BlockId,
    exit_block: BlockId,
    _hinsts: &[InstId],
    flag_cmp: InstId,
    cset_id: InstId,
    brif_cmp: InstId,
    bcond: InstId,
    b_last: InstId,
    init: i128,
    step: i128,
    bound: i128,
    iv_is_a: bool,
    cc_set: CondCode,
    t_target: BlockId,
    exit_blk: BlockId,
    taken_when_cond_true: bool,
) -> Option<CopyCountedLoop> {
    let p = rel_from_fp_cc(cc_set)?;
    let rel_xl = if iv_is_a { p } else { swap_rel(p) };
    let goes_to_exit_when_taken = t_target == exit_blk;
    let exit_when_cond_true = goes_to_exit_when_taken == taken_when_cond_true;
    let exit_rel = if exit_when_cond_true {
        rel_xl
    } else {
        negate_rel(rel_xl)
    };
    let init_aff = Affine {
        base: None,
        offset: init,
    };
    let bound_aff = Affine {
        base: None,
        offset: bound,
    };
    // FP values are exact integers; simulate at full 128-bit precision. The
    // FP path keeps the historical simulation cap: it is never eligible for
    // the const-addr unroll.
    let trip_count = simulate_trip(
        init_aff,
        bound_aff,
        step,
        exit_rel,
        127,
        HOT_MAX_TRIP_COUNT + 1,
    )?;
    let control_insts = vec![flag_cmp, cset_id, brif_cmp];
    let body_insts = collect_copy_body_insts(func, lp, &control_insts, bcond, b_last);
    Some(CopyCountedLoop {
        trip_count,
        control_insts,
        bcond,
        header_uncond_b: b_last,
        in_loop_succ: latch,
        exit_block,
        body_insts,
        const_iv: None,
        iv_inc: None,
    })
}

/// The body instructions to replicate per extra iteration: everything in the
/// loop body blocks except the branch terminators and the identified control
/// instructions. No renaming is performed on clone (see module note).
fn collect_copy_body_insts(
    func: &MachFunction,
    lp: &NaturalLoop,
    control_insts: &[InstId],
    bcond: InstId,
    header_uncond_b: InstId,
) -> Vec<InstId> {
    let mut out = Vec::new();
    for &block_id in &func.block_order {
        if !lp.body.contains(&block_id) {
            continue;
        }
        for &inst_id in &func.block(block_id).insts {
            if inst_id == bcond || inst_id == header_uncond_b || control_insts.contains(&inst_id) {
                continue;
            }
            let inst = func.inst(inst_id);
            if inst.flags.is_branch() || inst.flags.is_terminator() {
                continue;
            }
            out.push(inst_id);
        }
    }
    out
}

// ===========================================================================
// Const-addr full unroll (the SROA-enabling unroll).
//
// The importer lowers `a[i]` on a counted loop to per-iteration address
// arithmetic `addr = Madd(iv, #elem_size, base)` followed by `LdrRI/StrRI
// [addr, #0]`. A stack-slot array accessed this way can never be scalar-
// replaced (the offset is not a compile-time constant), so the array
// round-trips through memory (salsa20's `x[16]`).
//
// When the trip count, IV init and step are ALL compile-time constants, the
// IV value of iteration `m` is exactly `init + m*step`, so each iteration's
// `Madd` computes `base + (init + m*step)*k` — a CONSTANT offset from an
// invariant base. This path fully unrolls such loops (trip counts up to
// `CONST_ADDR_UNROLL_MAX_TRIP`) and rewrites, per cloned iteration:
//
//   * `Madd dst, iv, k, base`  ->  `AddRI dst_m, base, #((init+m*step)*k)`
//     with a FRESH `dst_m` per clone (keeping derived slot addresses
//     single-def, which the SROA address tracer requires), renaming `dst`'s
//     in-iteration uses to `dst_m`;
//   * the IV increment            ->  `Movz iv_next, #(init+(m+1)*step)`
//     (its exact value; this breaks the otherwise-circular dead `iv` copy
//     chain so DCE can strip it once the addresses no longer read the IV).
//
// SOUNDNESS: the base and the multiplier `k` are proven loop-invariant
// (every def outside the loop body), the rewritten `dst` is proven single-def
// and used only inside the loop after its def, and the materialized constants
// are exact IV values (absolute init/step, no wraparound: every value must
// fit 0..=0xffff and every offset 0..=4095). Any check failing on ANY `Madd`
// in the body fails the whole plan closed (no unroll — status quo). The
// verbatim-replication argument of `unroll_copy_based` covers everything
// else: values not rewritten still thread through the phi-copies.
//
// Eligibility further requires at least one rewritten `Madd` whose base is a
// stack-slot address (`AddPCRel SP, slot` chain): the unroll exists to feed
// SROA, and the targeted gate keeps the raised trip-count cap from inflating
// unrelated loops. Kill switch: `TCG_NO_CONST_ADDR_UNROLL`.
// ===========================================================================

/// A single `Madd dst, iv, #k, base` scheduled for constant-offset rewrite.
struct MaddRewrite {
    inst_id: InstId,
    dst: VReg,
    base: VReg,
    k: i128,
}

/// A validated const-addr unroll plan for one copy-counted loop.
struct ConstAddrPlan {
    madds: Vec<MaddRewrite>,
    init: i128,
    step: i128,
    inc_inst: InstId,
    inc_dst: VReg,
}

/// Every def of `v` lies outside the loop body (loop-invariant for the copy
/// dialect, where all in-loop defs live in the body blocks).
fn all_defs_outside_body(
    func: &MachFunction,
    lp: &NaturalLoop,
    def_map: &HashMap<VReg, Vec<InstId>>,
    v: VReg,
) -> bool {
    let Some(defs) = def_map.get(&v) else {
        // No defs at all (e.g. an ABI-copy-in vreg would still have one; a
        // truly def-less vreg is malformed) — fail closed.
        return false;
    };
    defs.iter()
        .all(|&id| !lp.body.iter().any(|&b| func.block(b).insts.contains(&id)))
}

/// Walk `v`'s unique-def chain through `AddRI`/`MovR`/`Copy` and report
/// whether it bottoms out at a stack-slot address root (`AddPCRel _, SP,
/// StackSlot`).
fn traces_to_stack_slot(
    func: &MachFunction,
    def_map: &HashMap<VReg, Vec<InstId>>,
    v: VReg,
) -> bool {
    let mut cur = v;
    for _ in 0..64 {
        let Some(inst) = unique_def(func, def_map, cur) else {
            return false;
        };
        match inst.opcode {
            AArch64Opcode::AddPCRel => {
                return matches!(inst.operands.get(2), Some(MachOperand::StackSlot(_)));
            }
            AArch64Opcode::AddRI | AArch64Opcode::MovR | AArch64Opcode::Copy => {
                match inst.operands.get(1).and_then(|op| op.as_vreg()) {
                    Some(src) => cur = src,
                    None => return false,
                }
            }
            _ => return false,
        }
    }
    false
}

/// Build the const-addr rewrite plan for `cl`, or fail closed (`None`).
fn plan_const_addr_unroll(
    func: &MachFunction,
    lp: &NaturalLoop,
    cl: &CopyCountedLoop,
    def_map: &HashMap<VReg, Vec<InstId>>,
) -> Option<ConstAddrPlan> {
    let (iv_vreg, init, step) = cl.const_iv?;
    let (inc_inst, inc_dst) = cl.iv_inc?;
    let trip = cl.trip_count as i128;

    // Every materialized IV value (`init + m*step` for m in 0..=trip) must be
    // an exact small non-negative constant: no register-width wraparound, and
    // encodable as a single `Movz`.
    for m in 0..=trip {
        let v = init + m * step;
        if !(0..=0xffff).contains(&v) {
            return None;
        }
    }

    let mut madds: Vec<MaddRewrite> = Vec::new();
    let mut any_slot_based = false;

    for (pos, &iid) in cl.body_insts.iter().enumerate() {
        let inst = func.inst(iid);
        if inst.opcode != AArch64Opcode::Madd {
            continue;
        }
        // Madd operands: [dst, mul_a, mul_b, addend] (dst = a*b + addend).
        if inst.operands.len() != 4 {
            return None;
        }
        let dst = inst.operands.first()?.as_vreg()?;
        let a = inst.operands.get(1)?.as_vreg()?;
        let b = inst.operands.get(2)?.as_vreg()?;
        let base = inst.operands.get(3)?.as_vreg()?;

        // Address arithmetic only (64-bit).
        if dst.class != trust_cg_ir::RegClass::Gpr64 {
            return None;
        }
        // Exactly one multiplier operand is the IV; the other is a constant.
        let k_reg = match (a == iv_vreg, b == iv_vreg) {
            (true, false) => b,
            (false, true) => a,
            _ => return None,
        };
        let k_def = unique_def(func, def_map, k_reg)?;
        let k = match k_def.opcode {
            AArch64Opcode::Movz => {
                let (dst, value) = crate::reaching_const::movz_value(k_def)?;
                if dst != k_reg {
                    return None;
                }
                i128::from(value)
            }
            AArch64Opcode::MovI if k_def.operands.len() == 2 => {
                k_def.operands.get(1)?.as_imm()? as i128
            }
            _ => return None,
        };
        if k <= 0 || !all_defs_outside_body(func, lp, def_map, k_reg) {
            return None;
        }
        // The base must be loop-invariant and distinct from the values we
        // rewrite around.
        if base == iv_vreg || base == dst || !all_defs_outside_body(func, lp, def_map, base) {
            return None;
        }
        // `dst` must be single-def (this Madd), never used before its def
        // within the body, and never used outside the loop: the final clone
        // defines a FRESH vreg, so an outside reader would see a stale value.
        let dst_defs = def_map.get(&dst)?;
        if dst_defs.len() != 1 || dst_defs[0] != iid {
            return None;
        }
        for (other_pos, &other_id) in cl.body_insts.iter().enumerate() {
            if other_pos >= pos {
                break;
            }
            if inst_uses_vreg(func.inst(other_id), dst) {
                return None;
            }
        }
        if vreg_used_outside_loop(func, lp, dst) {
            return None;
        }
        // Every per-iteration offset must be AddRI-encodable (imm12).
        for m in 0..trip {
            let offset = (init + m * step) * k;
            if !(0..=4095).contains(&offset) {
                return None;
            }
        }
        any_slot_based |= traces_to_stack_slot(func, def_map, base);
        madds.push(MaddRewrite {
            inst_id: iid,
            dst,
            base,
            k,
        });
    }

    if madds.is_empty() || !any_slot_based {
        return None;
    }
    // The increment's destination must be a plain GPR (the `Movz` rewrite
    // materializes into the full register; values are wrap-free per above).
    if !matches!(
        inc_dst.class,
        trust_cg_ir::RegClass::Gpr32 | trust_cg_ir::RegClass::Gpr64
    ) {
        return None;
    }

    Some(ConstAddrPlan {
        madds,
        init,
        step,
        inc_inst,
        inc_dst,
    })
}

/// Does `inst` read `v` (any source operand)?
fn inst_uses_vreg(inst: &MachInst, v: VReg) -> bool {
    let start = usize::from(inst_produces_value(inst));
    inst.operands[start..]
        .iter()
        .any(|op| matches!(op, MachOperand::VReg(u) if *u == v))
}

/// Is `v` read by any instruction outside the loop body?
fn vreg_used_outside_loop(func: &MachFunction, lp: &NaturalLoop, v: VReg) -> bool {
    for &block_id in &func.block_order {
        if lp.body.contains(&block_id) {
            continue;
        }
        for &inst_id in &func.block(block_id).insts {
            if inst_uses_vreg(func.inst(inst_id), v) {
                return true;
            }
        }
    }
    false
}

/// Fully unroll a recognized copy-based counted loop by verbatim replication
/// (no renaming). See the module note for the soundness argument.
///
/// The clones are appended directly into the latch block (before its
/// terminator) rather than into fresh blocks: iteration 0's body lives in the
/// header, its phi-copies plus iterations `1..trip_count` live in the latch,
/// and the latch then falls through to the exit. This creates NO new blocks,
/// keeping the CFG a clean header->latch->exit chain.
///
/// With `const_addr` set (the const-addr unroll), each cloned iteration
/// additionally rewrites the planned `Madd` address computations into fresh
/// constant-offset `AddRI`s and the IV increment into its exact `Movz`
/// constant; iteration 0's originals are rewritten in place after cloning.
fn unroll_copy_based(
    func: &mut MachFunction,
    lp: &NaturalLoop,
    cl: &CopyCountedLoop,
    const_addr: Option<&ConstAddrPlan>,
    mut provenance: Option<&mut ProvenanceMap>,
) -> bool {
    let header = lp.header;
    let latch = cl.in_loop_succ;
    let exit_block = cl.exit_block;
    let trip_count = cl.trip_count as usize;

    // The latch's terminator is the back edge (B header). Remove it; we will
    // re-terminate with a branch to the exit after appending the clones.
    let latch_term_id = match func.block(latch).insts.last().copied() {
        Some(id) => id,
        None => return false,
    };
    let latch_term_loc = func.inst(latch_term_id).source_loc;
    func.block_mut(latch).insts.pop();

    // Append (trip_count - 1) verbatim clones of the loop body into the latch,
    // after iteration 0's phi-copies (which already sit at the latch head).
    // With a const-addr plan, iteration `iter`'s clone rewrites the planned
    // `Madd`s into fresh constant-offset `AddRI`s (renaming their dst uses
    // within the clone) and the IV increment into its exact constant.
    for iter in 1..trip_count {
        let mut rename: HashMap<VReg, VReg> = HashMap::new();
        for &iid in &cl.body_insts {
            let (opcode, operands, source_loc) = {
                let inst = func.inst(iid);
                (inst.opcode, inst.operands.clone(), inst.source_loc)
            };
            let new_inst = if let Some(plan) = const_addr {
                if iid == plan.inc_inst {
                    // iv_next of iteration `iter` is init + (iter+1)*step.
                    let value = plan.init + (iter as i128 + 1) * plan.step;
                    movz_inst(plan.inc_dst, value, source_loc)
                } else if let Some(mr) = plan.madds.iter().find(|mr| mr.inst_id == iid) {
                    let offset = (plan.init + iter as i128 * plan.step) * mr.k;
                    let fresh = VReg::new(func.next_vreg, mr.dst.class);
                    func.next_vreg += 1;
                    rename.insert(mr.dst, fresh);
                    let mut addri = MachInst::new(
                        AArch64Opcode::AddRI,
                        vec![
                            MachOperand::VReg(fresh),
                            MachOperand::VReg(mr.base),
                            MachOperand::Imm(offset as i64),
                        ],
                    );
                    addri.source_loc = source_loc;
                    addri
                } else {
                    // Verbatim clone, with any renamed dst substituted in the
                    // clone's source operands (defs are never renamed: plan
                    // validation proved the renamed vregs are single-def).
                    let mut c = MachInst::new(opcode, operands);
                    c.source_loc = source_loc;
                    let start = usize::from(inst_produces_value(&c));
                    for op in &mut c.operands[start..] {
                        if let MachOperand::VReg(v) = op
                            && let Some(&fresh) = rename.get(v)
                        {
                            *v = fresh;
                        }
                    }
                    c
                }
            } else {
                let mut c = MachInst::new(opcode, operands);
                c.source_loc = source_loc;
                c
            };
            let new_inst_id = func.push_inst(new_inst);
            func.append_inst(latch, new_inst_id);
            if let Some(provenance) = provenance.as_deref_mut() {
                provenance.record_clone(iid, new_inst_id, loop_unroll_pass_id());
            }
        }
    }

    // Iteration 0 (the original header body): rewrite the planned `Madd`s and
    // the IV increment in place, AFTER cloning (clones read the originals).
    if let Some(plan) = const_addr {
        for mr in &plan.madds {
            let loc = func.inst(mr.inst_id).source_loc;
            let mut addri = MachInst::new(
                AArch64Opcode::AddRI,
                vec![
                    MachOperand::VReg(mr.dst),
                    MachOperand::VReg(mr.base),
                    MachOperand::Imm((plan.init * mr.k) as i64),
                ],
            );
            addri.source_loc = loc;
            *func.inst_mut(mr.inst_id) = addri;
            if let Some(p) = provenance.as_deref_mut() {
                p.record_in_place_transform(mr.inst_id, loop_unroll_pass_id());
            }
        }
        let loc = func.inst(plan.inc_inst).source_loc;
        *func.inst_mut(plan.inc_inst) = movz_inst(plan.inc_dst, plan.init + plan.step, loc);
        if let Some(p) = provenance.as_deref_mut() {
            p.record_in_place_transform(plan.inc_inst, loop_unroll_pass_id());
        }
    }

    // Re-terminate the latch: fall through to the exit block.
    let mut latch_b = MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(exit_block)]);
    latch_b.source_loc = latch_term_loc;
    let latch_b_id = func.push_inst(latch_b);
    func.append_inst(latch, latch_b_id);
    if let Some(provenance) = provenance.as_deref_mut() {
        provenance.record_clone(latch_term_id, latch_b_id, loop_unroll_pass_id());
    }
    // Rewire latch edges: drop the back edge, add the exit edge.
    func.block_mut(latch).succs.retain(|&s| s != header);
    func.block_mut(header).preds.retain(|&p| p != latch);
    if !func.block(latch).succs.contains(&exit_block) {
        func.add_edge(latch, exit_block);
    }

    // --- Strip the header's loop control; make it fall through to the latch ---
    func.block_mut(header).succs.retain(|&s| s == latch);
    func.block_mut(exit_block).preds.retain(|&p| p != header);

    let mut to_remove: Vec<InstId> = cl.control_insts.clone();
    to_remove.push(cl.bcond);
    to_remove.push(cl.header_uncond_b);
    if let Some(provenance) = provenance.as_deref_mut() {
        for &id in &cl.control_insts {
            provenance.record_deletion(
                id,
                loop_unroll_pass_id(),
                "loop-unroll removed trip-count control after full unroll",
            );
        }
    }
    let header_b_loc = func.inst(cl.header_uncond_b).source_loc;
    func.block_mut(header)
        .insts
        .retain(|iid| !to_remove.contains(iid));
    let mut new_b = MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(latch)]);
    new_b.source_loc = header_b_loc;
    let new_b_id = func.push_inst(new_b);
    func.append_inst(header, new_b_id);
    if let Some(provenance) = provenance {
        provenance.record_clone(cl.header_uncond_b, new_b_id, loop_unroll_pass_id());
    }

    true
}

// ===========================================================================
// Bounded-max-trip FULL unroll that RETAINS early exits.
//
// Recognizes the multi-block trial loop whose back-edge condition is
// `AndRR(CSet(iv_next != K), CSet(dynamic))` with a compile-time constant limit
// `K` and constant step (Stanford `Queens.c`'s `Try`):
//
//   header:                                  ; iv_next = iv + step (rotated)
//     iv_next = AddRI iv, #step
//     ...trial work; b[j] guard...           ; early exits branch to T
//     BCond -> T ; B -> next                  (all early exits funnel into T)
//   ...more guard blocks, the placement body, the recursive call...
//   T (exit-test block):
//     ...dynamic-condition compute -> dyn...  ; dyn = CSet(...)   (kept verbatim)
//     CmpRI iv_next, #K ; CSet vt, NE         ; the trip-limit test  (dropped)
//     AndRR vcond, vt, dyn                     ; continue = trip && dyn (dropped)
//     CmpRI vcond, #0 ; BCond[NE] -> latch ; B -> X
//   latch:
//     iv = MovR iv_next                        ; the IV phi-copy (back-edge)
//     B header
//   X: (out of loop)
//
// The IV value on iteration `m` (1-indexed) is provably `init + m*step`, because
// the IV advances by exactly `step` each iteration UNCONDITIONALLY — the dynamic
// early-exit only cuts the iteration chain short, it never changes the IV. So we
// FULLY unroll into `M = (K-init)/step` straight-line iterations, materializing
// the per-iteration constant IV in each clone (which turns the `b[j]`/`a[i+j]`
// index arithmetic into constant offsets), and DROP only the `iv_next != K`
// limit test — retaining the dynamic `dyn` early exit as an ordinary branch
// between iterations. The trailing iteration (`iv_next == K`) always exits.
//
// SOUNDNESS: every loop-carried value except the IV flows through memory (the
// stores/loads are cloned verbatim, preserving program order); the IV is
// replaced by its exact per-iteration constant; nothing the loop computes is
// live out of the single exit block. Fails closed on any shape deviation.
// ===========================================================================

/// A recognized bounded early-exit loop, ready for full unroll.
struct BoundedEarlyExitLoop {
    /// Number of body executions (iterations) `M = (K - init) / step` (>= 2).
    trip_count: u64,
    /// The IV-increment result vreg (compared against the limit `K`).
    iv_next: VReg,
    /// The header instruction defining `iv_next` (`AddRI`/`SubRI`), replaced by
    /// a materialized constant per iteration.
    iv_inc_inst: InstId,
    /// Constant IV init (preheader value).
    iv_init: i128,
    /// Constant IV step.
    iv_step: i128,
    /// The exit-test block `T` (the only body block with an out-of-loop edge).
    test_block: BlockId,
    /// The exit block `X` (out of the loop).
    exit_block: BlockId,
    /// The dynamic continue-condition vreg (a `CSet` result in `T`); the loop
    /// continues while this is nonzero AND `iv_next != K`.
    dyn_cond: VReg,
    /// `T`'s trip-limit compare `CmpRI iv_next, #K` (dropped on unroll).
    trip_cmp: InstId,
    /// `T`'s trip-limit `CSet vt, NE` (dropped on unroll).
    trip_cset: InstId,
    /// `T`'s `AndRR vcond, vt, dyn` (dropped on unroll).
    andrr: InstId,
    /// `T`'s `CmpRI vcond, #0` (re-pointed at `dyn_cond` for non-final copies).
    vcond_cmp: InstId,
    /// `T`'s `BCond[NE] -> latch` (the continue branch).
    bcond: InstId,
    /// `T`'s `B -> X` (the exit branch).
    b_term: InstId,
    /// All loop body blocks, in `block_order`.
    body_blocks: Vec<BlockId>,
}

/// Recognize the bounded early-exit trial loop and prove a constant trip count.
/// Fails closed on anything it cannot prove exactly.
fn analyze_bounded_early_exit_loop(
    func: &MachFunction,
    lp: &NaturalLoop,
    def_map: &HashMap<VReg, Vec<InstId>>,
) -> Option<BoundedEarlyExitLoop> {
    let _preheader = lp.preheader?;
    let header = lp.header;
    let latch = lp.latch;

    // Multi-block loop only (the clean 2-block shape is handled by
    // `analyze_copy_counted_loop`).
    if lp.body.len() < 3 || latch == header || !lp.body.contains(&latch) {
        return None;
    }

    // The loop must have EXACTLY ONE exit edge (body -> non-body). Its source is
    // the exit-test block `T`, its target the exit block `X`. Every "early exit"
    // inside the trial stays in the loop (branches to `T`).
    let mut exit_edge: Option<(BlockId, BlockId)> = None;
    for &b in &lp.body {
        for &s in &func.block(b).succs {
            if !lp.body.contains(&s) {
                if exit_edge.is_some() {
                    return None;
                }
                exit_edge = Some((b, s));
            }
        }
    }
    let (t, x) = exit_edge?;
    if t == header || t == latch {
        return None;
    }

    // Latch must be the clean back-edge block: single pred == `T` (its continue
    // successor), single succ == header, reached only from `T`. The unroller
    // redirects the latch per iteration, so nothing else may enter it.
    let lsuccs = &func.block(latch).succs;
    if lsuccs.len() != 1 || lsuccs[0] != header {
        return None;
    }
    let lpreds = &func.block(latch).preds;
    if lpreds.len() != 1 || lpreds[0] != t {
        return None;
    }
    // `T`'s successors are exactly {latch (continue), X (exit)}.
    let tsuccs = &func.block(t).succs;
    if tsuccs.len() != 2 || !tsuccs.contains(&latch) || !tsuccs.contains(&x) {
        return None;
    }

    // ---- `T` terminator: ... CmpRI vcond,#0 ; BCond[NE]->latch ; B->X ----
    let tinsts = func.block(t).insts.clone();
    if tinsts.len() < 4 {
        return None;
    }
    let b_term = *tinsts.last()?;
    let bcond = tinsts[tinsts.len() - 2];
    let vcond_cmp = tinsts[tinsts.len() - 3];

    let b_inst = func.inst(b_term);
    if b_inst.opcode != AArch64Opcode::B || b_inst.operands.first() != Some(&MachOperand::Block(x))
    {
        return None;
    }
    let bcond_inst = func.inst(bcond);
    if bcond_inst.opcode != AArch64Opcode::BCond {
        return None;
    }
    // Canonical br_if lowering: BCond[NE] taken (cond != 0) to the in-loop
    // continue target (the latch); the fall-through `B` goes to the exit.
    if cc_from_operand(bcond_inst.operands.first()?)? != CondCode::NE {
        return None;
    }
    match bcond_inst.operands.get(1)? {
        MachOperand::Block(bt) if *bt == latch => {}
        _ => return None,
    }

    let vcmp_inst = func.inst(vcond_cmp);
    if vcmp_inst.opcode != AArch64Opcode::CmpRI
        || vcmp_inst.operands.get(1).and_then(|op| op.as_imm()) != Some(0)
    {
        return None;
    }
    let vcond = vcmp_inst.operands.first()?.as_vreg()?;

    // vcond = AndRR(a, b), defined in `T`.
    let andrr = *def_map.get(&vcond)?.iter().find(|&&id| {
        func.inst(id).opcode == AArch64Opcode::AndRR && func.block(t).insts.contains(&id)
    })?;
    let andrr_inst = func.inst(andrr);
    let a = andrr_inst.operands.get(1)?.as_vreg()?;
    let b = andrr_inst.operands.get(2)?.as_vreg()?;

    // Identify which AndRR operand is the trip-limit test and which is the
    // dynamic condition. Exactly one must be the trip test.
    let mut trip: Option<TripMatch> = None;
    let mut dyn_cond: Option<VReg> = None;
    for cand in [a, b] {
        if let Some(m) = match_trip_cset(func, def_map, lp, t, header, cand) {
            if trip.is_some() {
                return None; // ambiguous: both look like the trip test
            }
            trip = Some(m);
        } else {
            if dyn_cond.is_some() {
                return None; // neither is a trip test
            }
            dyn_cond = Some(cand);
        }
    }
    let trip = trip?;
    let dyn_cond = dyn_cond?;

    // SOUNDNESS: the non-final copies test `dyn_cond != 0` in place of the
    // original `AndRR(trip_bool, dyn) != 0`. With the trip test compile-time
    // TRUE, `AndRR(1, dyn) = dyn & 1`, so `dyn != 0` matches the original only
    // when `dyn` is a 0/1 boolean. Require `dyn_cond` to be produced by a
    // `CSet` (always 0 or 1) — else fail closed.
    let dyn_is_bool = def_map.get(&dyn_cond).is_some_and(|defs| {
        defs.iter()
            .all(|&id| func.inst(id).opcode == AArch64Opcode::CSet)
    });
    if !dyn_is_bool {
        return None;
    }

    // ---- Prove the constant trip count `M`. The loop continues while
    //      `iv_next != K`, so the body runs for m = 1..M where init+M*step == K.
    let step = trip.iv_step;
    let init = trip.iv_init;
    let k = trip.k;
    if step == 0 {
        return None;
    }
    let diff = k - init;
    if diff % step != 0 {
        return None;
    }
    let m = diff / step;
    if m < 2 || m > BEE_MAX_TRIP_COUNT as i128 {
        return None;
    }
    // Every materialized IV value must fit a 16-bit Movz, and none before the
    // last may already equal K (a linear IV hits K exactly once, at m — this is
    // a defensive check against a pathological negative-step form).
    for j in 1..=m {
        let v = init + j * step;
        if !(0..=0xffff).contains(&v) {
            return None;
        }
        if j < m && v == k {
            return None;
        }
    }

    let body_blocks: Vec<BlockId> = func
        .block_order
        .iter()
        .copied()
        .filter(|b| lp.body.contains(b))
        .collect();

    // Code-growth cap on total cloned instructions.
    let body_inst_total: usize = body_blocks.iter().map(|b| func.block(*b).insts.len()).sum();
    if body_inst_total.saturating_mul(m as usize - 1) > BEE_MAX_CLONED_INSTS {
        return None;
    }

    Some(BoundedEarlyExitLoop {
        trip_count: m as u64,
        iv_next: trip.iv_next,
        iv_inc_inst: trip.iv_inc_inst,
        iv_init: init,
        iv_step: step,
        test_block: t,
        exit_block: x,
        dyn_cond,
        trip_cmp: trip.cmp_id,
        trip_cset: trip.cset_id,
        andrr,
        vcond_cmp,
        bcond,
        b_term,
        body_blocks,
    })
}

/// A matched trip-limit CSet: `CSet cset, NE` fed by `CmpRI iv_next, #K`, where
/// `iv_next` is the header's loop-IV increment (constant init & step).
struct TripMatch {
    cset_id: InstId,
    cmp_id: InstId,
    k: i128,
    iv_next: VReg,
    iv_inc_inst: InstId,
    iv_init: i128,
    iv_step: i128,
}

/// If `cand`'s `CSet` in `T` realizes `iv_next != K` for the header loop-IV,
/// return the trip match; else `None`.
fn match_trip_cset(
    func: &MachFunction,
    def_map: &HashMap<VReg, Vec<InstId>>,
    lp: &NaturalLoop,
    t: BlockId,
    header: BlockId,
    cand: VReg,
) -> Option<TripMatch> {
    // `cand` = CSet(cc) in `T`.
    let cset_id = *def_map.get(&cand)?.iter().find(|&&id| {
        func.inst(id).opcode == AArch64Opcode::CSet && func.block(t).insts.contains(&id)
    })?;
    let cset_inst = func.inst(cset_id);
    if cset_inst.operands.first()?.as_vreg()? != cand {
        return None;
    }
    // The limit test keeps the loop live while `iv_next != K`: CSet realizes NE.
    // `CmpRI iv_next, #K` has `iv_next` as operand 0, so no operand swap.
    if cc_from_operand(cset_inst.operands.get(1)?)? != CondCode::NE {
        return None;
    }
    // Nearest flag-setter before the CSet in `T` must be `CmpRI z, #K`.
    let tinsts = &func.block(t).insts;
    let cset_pos = tinsts.iter().position(|&id| id == cset_id)?;
    let cmp_id = nearest_flag_setter(func, tinsts, cset_pos)?;
    let cmp = func.inst(cmp_id);
    if cmp.opcode != AArch64Opcode::CmpRI {
        return None;
    }
    let z = cmp.operands.first()?.as_vreg()?;
    let k = cmp.operands.get(1)?.as_imm()? as i128;

    // `z` must resolve (through copies) to the loop-IV increment, defined by a
    // single `AddRI`/`SubRI` in the header.
    let iv_next = resolve_through_copies(func, def_map, z);
    let iv_defs = def_map.get(&iv_next)?;
    if iv_defs.len() != 1 {
        return None;
    }
    let iv_inc_inst = iv_defs[0];
    let inc_inst = func.inst(iv_inc_inst);
    if !matches!(inc_inst.opcode, AArch64Opcode::AddRI | AArch64Opcode::SubRI)
        || !func.block(header).insts.contains(&iv_inc_inst)
    {
        return None;
    }
    // Validate loop-carried threading and recover the constant init & step.
    let iv = try_iv_increment(func, def_map, lp, iv_next, false)?;
    let init_aff = affine_of(func, def_map, iv.init_src);
    if init_aff.base.is_some() {
        return None; // symbolic init: cannot materialize a constant IV
    }
    Some(TripMatch {
        cset_id,
        cmp_id,
        k,
        iv_next,
        iv_inc_inst,
        iv_init: init_aff.offset,
        iv_step: iv.int_step,
    })
}

/// Compute the set of loop-body vregs that are SAFE to rename to fresh ids in
/// each unrolled clone (restoring the single-def/single-use invariant that
/// downstream single-def passes — e.g. `cmp_branch_fusion`'s cmp;cset;cbnz ->
/// cbz collapse — rely on).
///
/// A body-defined vreg `v` is safe iff:
///   1. `v != iv_next` (the induction result is materialized as a per-clone
///      `Movz` under its fixed name, so its users must keep that name), AND
///   2. every USE of `v` anywhere in the function is inside a loop-body block
///      (not live-out of the loop), AND
///   3. every such use is DOMINATED by a DEF of `v` inside the body (same block:
///      def precedes use; cross block: def-block dominates use-block).
///
/// Condition (3) is exactly "`v` is not live-in to the loop header" (not
/// loop-carried in a register). For such a `v`, each clone's uses bind to that
/// clone's own dominating def, so renaming to fresh per-clone ids is
/// SEMANTICALLY IDENTICAL to reusing the original id — while restoring
/// single-def form. Loop-carried registers (the IV, and — per the transform's
/// soundness note — nothing else, since every other loop-carried value flows
/// through memory) fail (3) and are conservatively kept under their original id
/// (the pre-existing vreg-reuse behavior). Returns a deterministically sorted
/// list.
fn renamable_body_vregs(func: &MachFunction, body: &[BlockId], iv_next: VReg) -> Vec<VReg> {
    let body_set: HashSet<BlockId> = body.iter().copied().collect();

    // Def sites of each vreg inside the body: (block, position-within-block).
    let mut defs: HashMap<VReg, Vec<(BlockId, usize)>> = HashMap::new();
    for &b in body {
        for (pos, &iid) in func.block(b).insts.iter().enumerate() {
            let inst = func.inst(iid);
            aarch64_for_each_def_position(inst.opcode, inst.operands.len(), |dp| {
                if let Some(MachOperand::VReg(v)) = inst.operands.get(dp) {
                    defs.entry(*v).or_default().push((b, pos));
                }
            });
        }
    }

    let dom = DomTree::compute(func);

    // A use at (ub, upos) is covered iff some def of `v` dominates it.
    let use_covered = |v: VReg, ub: BlockId, upos: usize| -> bool {
        let Some(sites) = defs.get(&v) else {
            return false;
        };
        sites.iter().any(|&(db, dpos)| {
            if db == ub {
                dpos < upos
            } else {
                dom.dominates(db, ub)
            }
        })
    };

    // A vreg is unsafe if ANY of its uses (whole function) is out-of-body or is
    // not dominated by an in-body def.
    let mut unsafe_vregs: HashSet<VReg> = HashSet::new();
    for &b in &func.block_order {
        let in_body = body_set.contains(&b);
        for (pos, &iid) in func.block(b).insts.iter().enumerate() {
            let inst = func.inst(iid);
            aarch64_for_each_use_position(inst.opcode, inst.operands.len(), |up| {
                if let Some(MachOperand::VReg(v)) = inst.operands.get(up)
                    && defs.contains_key(v)
                    && (!in_body || !use_covered(*v, b, pos))
                {
                    unsafe_vregs.insert(*v);
                }
            });
        }
    }

    let mut out: Vec<VReg> = defs
        .keys()
        .copied()
        .filter(|v| *v != iv_next && !unsafe_vregs.contains(v))
        .collect();
    out.sort();
    out
}

/// Fully unroll a recognized bounded early-exit loop, retaining the dynamic
/// early exit and materializing the per-iteration constant IV. See the section
/// note for the soundness argument.
fn unroll_bounded_early_exit(
    func: &mut MachFunction,
    lp: &NaturalLoop,
    bel: &BoundedEarlyExitLoop,
    mut provenance: Option<&mut ProvenanceMap>,
) -> bool {
    let header = lp.header;
    let latch = lp.latch;
    let t = bel.test_block;
    let x = bel.exit_block;
    let m = bel.trip_count as usize;
    let body = bel.body_blocks.clone();

    // Vregs safe to rename to fresh per-clone ids (see `renamable_body_vregs`).
    // Computed on the ORIGINAL (pre-mutation) function so dominance is exact.
    // Empty when the kill switch is set -> byte-identical to the old clone.
    let renamable: Vec<VReg> = if bee_unroll_rename_enabled() {
        renamable_body_vregs(func, &body, bel.iv_next)
    } else {
        Vec::new()
    };

    // `T`'s kept (verbatim) instructions: everything except the trip-limit
    // control and both branch terminators (the terminator is rebuilt per copy).
    let drop_all = [
        bel.trip_cmp,
        bel.trip_cset,
        bel.andrr,
        bel.vcond_cmp,
        bel.bcond,
        bel.b_term,
    ];
    let t_kept: Vec<InstId> = func
        .block(t)
        .insts
        .iter()
        .copied()
        .filter(|id| !drop_all.contains(id))
        .collect();

    // The latch's phi-copies (everything but its back-edge terminator).
    let latch_body: Vec<InstId> = {
        let insts = &func.block(latch).insts;
        insts[..insts.len().saturating_sub(1)].to_vec()
    };

    // ---- Pre-create clone blocks for iterations 2..=m. `maps[k-2]` maps each
    //      body block to its iteration-k clone. The final iteration skips the
    //      latch (its back-edge never fires). ----
    let mut maps: Vec<HashMap<BlockId, BlockId>> = Vec::new();
    for k in 2..=m {
        let is_last = k == m;
        let mut map = HashMap::new();
        for &bo in &body {
            if is_last && bo == latch {
                continue;
            }
            let nb = func.create_block();
            map.insert(bo, nb);
        }
        maps.push(map);
    }
    let header_of = |k: usize| -> BlockId { if k == 1 { header } else { maps[k - 2][&header] } };

    // ---- Iteration 1: rewrite the ORIGINAL blocks in place. ----
    // (a) materialize the constant IV for iteration 1 (init + 1*step).
    let loc1 = func.inst(bel.iv_inc_inst).source_loc;
    *func.inst_mut(bel.iv_inc_inst) = movz_inst(bel.iv_next, bel.iv_init + bel.iv_step, loc1);
    if let Some(p) = provenance.as_deref_mut() {
        p.record_in_place_transform(bel.iv_inc_inst, loop_unroll_pass_id());
    }
    // (b) exit-test block: drop the trip control, re-point the branch compare at
    //     the dynamic condition; keep BCond[NE]->latch ; B->X unchanged.
    func.inst_mut(bel.vcond_cmp).operands[0] = MachOperand::VReg(bel.dyn_cond);
    if let Some(p) = provenance.as_deref_mut() {
        p.record_in_place_transform(bel.vcond_cmp, loop_unroll_pass_id());
        for &id in &[bel.trip_cmp, bel.trip_cset, bel.andrr] {
            p.record_deletion(
                id,
                loop_unroll_pass_id(),
                "loop-unroll dropped bounded trip-limit test (retaining early exit)",
            );
        }
    }
    let drop_trip = [bel.trip_cmp, bel.trip_cset, bel.andrr];
    func.block_mut(t).insts.retain(|id| !drop_trip.contains(id));
    // (c) redirect the original latch back-edge: header -> iteration-2 header.
    redirect_branch_and_edge(func, latch, header, header_of(2));
    if let Some(p) = provenance.as_deref_mut()
        && let Some(&last) = func.block(latch).insts.last()
    {
        p.record_in_place_transform(last, loop_unroll_pass_id());
    }

    // ---- Iterations 2..=m: populate the clones. ----
    for k in 2..=m {
        let is_last = k == m;
        let map = maps[k - 2].clone();
        let iv_k = bel.iv_init + (k as i128) * bel.iv_step;
        let next_header = if is_last { x } else { header_of(k + 1) };

        // Fresh per-clone rename for every safe vreg (deterministic order).
        let vmap: HashMap<VReg, VReg> = renamable
            .iter()
            .map(|&v| (v, VReg::new(func.alloc_vreg(), v.class)))
            .collect();

        for &bo in &body {
            if is_last && bo == latch {
                continue;
            }
            let nb = map[&bo];

            if bo == t {
                // Dynamic prefix (verbatim) + rebuilt terminator.
                for &iid in &t_kept {
                    let ni = clone_inst_remap(func, iid, &map, &vmap);
                    let nid = func.push_inst(ni);
                    func.append_inst(nb, nid);
                    if let Some(p) = provenance.as_deref_mut() {
                        p.record_clone(iid, nid, loop_unroll_pass_id());
                    }
                }
                if is_last {
                    // `iv_next == K`: this copy always exits.
                    push_branch(func, nb, x, provenance.as_deref_mut(), bel.b_term);
                } else {
                    // Continue when the dynamic condition != 0, else exit. The
                    // trip test is a compile-time TRUE here, so `AndRR(trip,dyn)`
                    // reduces to `dyn`; re-point the branch compare at `dyn`,
                    // clone the (NE, ->latch) BCond and (->X) B verbatim.
                    let mut vc = clone_inst_remap(func, bel.vcond_cmp, &map, &vmap);
                    // Re-point at `dyn`, honoring this clone's rename of `dyn`
                    // (its defining `CSet` in `t_kept` was renamed to match).
                    let dyn_k = vmap.get(&bel.dyn_cond).copied().unwrap_or(bel.dyn_cond);
                    vc.operands[0] = MachOperand::VReg(dyn_k);
                    let cid = func.push_inst(vc);
                    func.append_inst(nb, cid);
                    if let Some(p) = provenance.as_deref_mut() {
                        p.record_clone(bel.vcond_cmp, cid, loop_unroll_pass_id());
                    }
                    let bc = clone_inst_remap(func, bel.bcond, &map, &vmap);
                    let bcid = func.push_inst(bc);
                    func.append_inst(nb, bcid);
                    if let Some(p) = provenance.as_deref_mut() {
                        p.record_clone(bel.bcond, bcid, loop_unroll_pass_id());
                    }
                    let bt = clone_inst_remap(func, bel.b_term, &map, &vmap);
                    let btid = func.push_inst(bt);
                    func.append_inst(nb, btid);
                    if let Some(p) = provenance.as_deref_mut() {
                        p.record_clone(bel.b_term, btid, loop_unroll_pass_id());
                    }
                }
            } else if bo == latch {
                for &iid in &latch_body {
                    let ni = clone_inst_remap(func, iid, &map, &vmap);
                    let nid = func.push_inst(ni);
                    func.append_inst(nb, nid);
                    if let Some(p) = provenance.as_deref_mut() {
                        p.record_clone(iid, nid, loop_unroll_pass_id());
                    }
                }
                push_branch(func, nb, next_header, provenance.as_deref_mut(), bel.b_term);
            } else {
                for &iid in &func.block(bo).insts.clone() {
                    if bo == header && iid == bel.iv_inc_inst {
                        let loc = func.inst(iid).source_loc;
                        let mov = movz_inst(bel.iv_next, iv_k, loc);
                        let nid = func.push_inst(mov);
                        func.append_inst(nb, nid);
                        if let Some(p) = provenance.as_deref_mut() {
                            p.record_clone(iid, nid, loop_unroll_pass_id());
                        }
                    } else {
                        let ni = clone_inst_remap(func, iid, &map, &vmap);
                        let nid = func.push_inst(ni);
                        func.append_inst(nb, nid);
                        if let Some(p) = provenance.as_deref_mut() {
                            p.record_clone(iid, nid, loop_unroll_pass_id());
                        }
                    }
                }
            }
            wire_out_edges(func, nb);
        }
    }

    // ---- Fold now-constant index arithmetic into memory-operand offsets. ----
    // Each iteration's IV is a compile-time constant, so `Madd(iv, scale, base)`
    // computes `base + iv*scale`; when every user of that address is a
    // `LdrRI`/`StrRI` with an encodable resulting offset, rewrite them to
    // `[base, #iv*scale]` and drop the `Madd`. This matches clang's
    // constant-offset guard loads and removes the per-access address register +
    // shifted-add that otherwise spike register pressure across the unrolled
    // body.
    let consts = collect_single_def_movz_consts(func);
    let iv1 = bel.iv_init + bel.iv_step;
    fold_const_index_addresses(func, &body, bel.iv_next, iv1, &consts);
    for k in 2..=m {
        let iv_k = bel.iv_init + (k as i128) * bel.iv_step;
        let blocks: Vec<BlockId> = {
            let mut v: Vec<BlockId> = maps[k - 2].values().copied().collect();
            v.sort_unstable();
            v
        };
        fold_const_index_addresses(func, &blocks, bel.iv_next, iv_k, &consts);
    }

    true
}

// ===========================================================================
// Diamond-body constant-trip FULL unroll.
//
// Recognizes the multi-block copy-dialect counted loop whose body carries
// internal if/else control flow (a diamond or triangle) but whose SINGLE exit
// is a pure IV trip test with compile-time-constant init, step and bound
// (ReedSolomon's encode shift-register loop `for (j=15; j>0; j--) if (gg[j]
// != -1) bb[j] = bb[j-1]^alpha_to[(gg[j]+feedback)%nn]; else bb[j] =
// bb[j-1];`):
//
//   preheader:
//     iv = MovR init                      ; IV phi-copy (init edge, const init)
//     B header
//   header:                               ; body work, then the diamond branch
//     ...loads/addr work using iv...
//     BCond -> arm_a ; B -> arm_b
//   arm_a / arm_b:                        ; each ends B -> T (the join)
//     ...
//   T (join/exit-test block):
//     ...stores/work...
//     inc_dst = AddRI/SubRI iv, #step     ; IV increment (may also sit in the
//                                         ;  header — any block dominating T)
//     CmpRI iv|inc_dst, #K  (or CmpRR vs const)   ; the trip test   (dropped)
//     CSet vcond, cc                                              (dropped)
//     CmpRI vcond, #0 ; BCond -> {latch|X} ; B -> {X|latch}
//   latch:
//     iv = MovR inc_dst                   ; IV phi-copy (back edge)
//     [more phi-copies]
//     B header
//   X: (out of loop)
//
// The loop-carried IV advances by exactly `step` once per iteration (the
// increment's block dominates the latch, the body minus the back edge is
// acyclic, and the latch phi-copy threads exactly the increment result), so
// the IV value during iteration `m` (1-indexed) is provably `init +
// (m-1)*step` and the exit test's outcome is a compile-time constant per
// iteration. We fully unroll into `M` straight-line iterations: every body
// block is cloned per iteration (loop-carried values thread through the
// cloned phi-copies exactly as in `unroll_copy_based`; within-iteration
// values are recomputed by each clone), proven-safe body vregs are renamed to
// fresh per-clone ids (`renamable_body_vregs` — restoring single-def form for
// downstream passes), the IV increment is materialized as its exact per-clone
// constant, and the trip-test control is dropped (its outcome is proven by
// `simulate_trip`: `continue` for m < M, `exit` at m == M). Afterwards,
// constant-index `Madd` addresses (`gg[j]`, `bb[j-1]`) are folded into
// immediate-offset loads/stores per clone.
//
// SOUNDNESS: replication preserves the exact execution order of every cloned
// instruction (stores/loads verbatim); the only rewrites are (a) renaming of
// vregs proven clone-local, (b) the IV increment -> its exact constant, (c)
// dropping branch control whose outcome is proven per-clone, (d) address
// folds substituting exact IV constants. Anything unproven fails closed (no
// unroll). Kill switch: `TCG_NO_DIAMOND_CONST_TRIP_UNROLL`.
// ===========================================================================

/// A recognized diamond-body constant-trip loop, ready for full unroll.
struct DiamondConstTripLoop {
    /// Number of body executions `M` (>= 2).
    trip_count: u64,
    /// The loop-carried IV vreg (phi-copied through preheader + latch).
    iv_vreg: VReg,
    /// The IV-increment instruction (`AddRI`/`SubRI`) and its destination.
    inc_inst: InstId,
    inc_dst: VReg,
    /// Constant IV init (value on entry to iteration 1) and step.
    iv_init: i128,
    iv_step: i128,
    /// The exit-test block `T` (the only body block with an out-of-loop edge).
    test_block: BlockId,
    /// The exit block `X` (out of the loop).
    exit_block: BlockId,
    /// `T`'s trip-test control tail (all dropped on unroll):
    /// the flag-setting compare, the `CSet`, the `CmpRI vcond, #0`, the
    /// `BCond`, and the trailing `B`.
    flag_cmp: InstId,
    cset: InstId,
    vcond_cmp: InstId,
    bcond: InstId,
    b_term: InstId,
    /// All loop body blocks, in `block_order`.
    body_blocks: Vec<BlockId>,
}

/// Try to interpret `cand` (a compare operand) as the PRE-increment loop IV:
/// `cand` resolves through copies to the loop-carried IV vreg itself (defined
/// exactly twice: preheader init copy + latch back-edge copy), whose latch
/// copy threads a unique `AddRI/SubRI(iv, #step)` increment result. This is
/// the rotated shape whose exit test compares the OLD `iv` value (ReedSolomon
/// compares `j` — not `j-1` — against the bound).
fn try_pre_increment_iv(
    func: &MachFunction,
    def_map: &HashMap<VReg, Vec<InstId>>,
    lp: &NaturalLoop,
    cand: VReg,
) -> Option<IvInc> {
    let preheader = lp.preheader?;
    let iv = resolve_through_copies(func, def_map, cand);
    let iv_defs = def_map.get(&iv)?;
    // Exactly the two phi-copy defs: one in the preheader, one in the latch.
    if iv_defs.len() != 2 {
        return None;
    }
    let ph_def = *iv_defs
        .iter()
        .find(|&&id| func.block(preheader).insts.contains(&id))?;
    let latch_def = *iv_defs
        .iter()
        .find(|&&id| func.block(lp.latch).insts.contains(&id))?;
    if ph_def == latch_def {
        return None;
    }

    // The latch def must be a copy of the increment result.
    let latch_inst = func.inst(latch_def);
    if !latch_inst.opcode.is_move() {
        return None;
    }
    let latch_src = latch_inst.operands.get(1)?.as_vreg()?;
    let inc_res = resolve_through_copies(func, def_map, latch_src);
    let inc_defs = def_map.get(&inc_res)?;
    if inc_defs.len() != 1 {
        return None;
    }
    let inc_id = inc_defs[0];
    let inc_inst = func.inst(inc_id);
    let (src, step) = match inc_inst.opcode {
        AArch64Opcode::AddRI => (
            inc_inst.operands.get(1)?.as_vreg()?,
            inc_inst.operands.get(2)?.as_imm()? as i128,
        ),
        AArch64Opcode::SubRI => (
            inc_inst.operands.get(1)?.as_vreg()?,
            -(inc_inst.operands.get(2)?.as_imm()? as i128),
        ),
        _ => return None,
    };
    // The increment must advance the IV itself: src resolves to `iv`.
    if resolve_through_copies(func, def_map, src) != iv {
        return None;
    }

    // Preheader def source is the init value.
    let ph_inst = func.inst(ph_def);
    let init_src = if ph_inst.opcode.is_move() {
        ph_inst.operands.get(1)?.as_vreg().unwrap_or(iv)
    } else {
        iv
    };

    Some(IvInc {
        init_src,
        int_step: step,
        fp_step: None,
        is_a: false,
        iv_vreg: iv,
        inc_inst: inc_id,
        inc_dst: inc_res,
    })
}

/// `from` reaches `to` through a chain of PLAIN SAME-CLASS moves only
/// (`MovR`/`Copy` between equal register classes, each function-wide
/// single-def). Unlike `resolve_through_copies`, width-changing moves and
/// sign/zero extends are NOT admitted: they are only value-identities on
/// sub-range values, which nothing on this path proves at walk time. The
/// diamond unroll's exact IV value proof rides on these chains, so anything
/// else fails closed.
fn is_plain_move_chain(
    func: &MachFunction,
    def_map: &HashMap<VReg, Vec<InstId>>,
    from: VReg,
    to: VReg,
) -> bool {
    let mut cur = from;
    for _ in 0..64 {
        if cur == to {
            return true;
        }
        let Some(inst) = unique_def(func, def_map, cur) else {
            return false;
        };
        if !matches!(inst.opcode, AArch64Opcode::MovR | AArch64Opcode::Copy) {
            return false;
        }
        match inst.operands.get(1).and_then(|op| op.as_vreg()) {
            Some(src) if src.class == cur.class => cur = src,
            _ => return false,
        }
    }
    false
}

/// Strict absolute-constant resolution for the diamond unroll's IV init and
/// bound: a same-class `MovR`/`Copy`/`AddRI`/`SubRI` chain rooted at a
/// same-class `Movz`/`MovI`. All arithmetic is exact modulo the single shared
/// register width, and the caller's 0..=0xffff range gate collapses that to
/// true equality. Extends and width changes fail closed (`None`) — unlike
/// `affine_of`, which treats them as transparent.
fn strict_const_of(
    func: &MachFunction,
    def_map: &HashMap<VReg, Vec<InstId>>,
    v: VReg,
) -> Option<i128> {
    let mut cur = v;
    let mut offset: i128 = 0;
    for _ in 0..64 {
        let inst = unique_def(func, def_map, cur)?;
        match inst.opcode {
            AArch64Opcode::Movz => {
                let (dst, value) = crate::reaching_const::movz_value(inst)?;
                if dst != cur {
                    return None;
                }
                return Some(i128::from(value) + offset);
            }
            AArch64Opcode::MovI if inst.operands.len() == 2 => {
                return Some(inst.operands.get(1)?.as_imm()? as i128 + offset);
            }
            AArch64Opcode::AddRI => {
                let src = inst.operands.get(1)?.as_vreg()?;
                if src.class != cur.class {
                    return None;
                }
                offset += inst.operands.get(2)?.as_imm()? as i128;
                cur = src;
            }
            AArch64Opcode::SubRI => {
                let src = inst.operands.get(1)?.as_vreg()?;
                if src.class != cur.class {
                    return None;
                }
                offset -= inst.operands.get(2)?.as_imm()? as i128;
                cur = src;
            }
            AArch64Opcode::MovR | AArch64Opcode::Copy => {
                let src = inst.operands.get(1)?.as_vreg()?;
                if src.class != cur.class {
                    return None;
                }
                cur = src;
            }
            _ => return None,
        }
    }
    None
}

/// The body blocks minus the back edge form a DAG whose DFS from `header`
/// visits every body block (no inner cycle — each body block executes at most
/// once per iteration).
fn body_is_acyclic_dag(func: &MachFunction, lp: &NaturalLoop) -> bool {
    let header = lp.header;
    let mut state: HashMap<BlockId, u8> = HashMap::new(); // 1 = on stack, 2 = done
    let mut stack: Vec<(BlockId, usize)> = vec![(header, 0)];
    state.insert(header, 1);
    while let Some(&(b, idx)) = stack.last() {
        let succs = &func.block(b).succs;
        if idx < succs.len() {
            stack.last_mut().expect("nonempty").1 += 1;
            let s = succs[idx];
            // Skip the back edge and loop-exit edges.
            if s == header || !lp.body.contains(&s) {
                continue;
            }
            match state.get(&s) {
                Some(1) => return false, // cycle inside the body
                Some(_) => {}
                None => {
                    state.insert(s, 1);
                    stack.push((s, 0));
                }
            }
        } else {
            state.insert(b, 2);
            stack.pop();
        }
    }
    lp.body.iter().all(|b| state.contains_key(b))
}

/// Recognize the diamond-body constant-trip loop and prove its trip count.
/// Fails closed on anything it cannot prove exactly.
fn analyze_diamond_const_trip_loop(
    func: &MachFunction,
    lp: &NaturalLoop,
    def_map: &HashMap<VReg, Vec<InstId>>,
) -> Option<DiamondConstTripLoop> {
    let preheader = lp.preheader?;
    let header = lp.header;
    let latch = lp.latch;

    // Multi-block loop only (the clean 2-block shape is `analyze_copy_counted_
    // loop`'s; the AndRR early-exit shape is the BEE unroller's).
    if lp.body.len() < 3
        || lp.body.len() > DIAMOND_UNROLL_MAX_BLOCKS
        || latch == header
        || !lp.body.contains(&latch)
    {
        return None;
    }
    // header preds == {preheader, latch} (the latch edge is the ONLY back edge).
    let hpreds = &func.block(header).preds;
    if hpreds.len() != 2 || !hpreds.contains(&preheader) || !hpreds.contains(&latch) {
        return None;
    }

    // Exactly ONE exit edge (body -> non-body), from the test block `T`.
    let mut exit_edge: Option<(BlockId, BlockId)> = None;
    for &b in &lp.body {
        for &s in &func.block(b).succs {
            if !lp.body.contains(&s) {
                if exit_edge.is_some() {
                    return None;
                }
                exit_edge = Some((b, s));
            }
        }
    }
    let (t, x) = exit_edge?;
    if t == header || t == latch {
        return None;
    }

    // Latch: the clean back-edge block reached only from `T`.
    let lsuccs = &func.block(latch).succs;
    if lsuccs.len() != 1 || lsuccs[0] != header {
        return None;
    }
    let lpreds = &func.block(latch).preds;
    if lpreds.len() != 1 || lpreds[0] != t {
        return None;
    }
    // `T`'s successors are exactly {latch (continue), X (exit)}.
    let tsuccs = &func.block(t).succs;
    if tsuccs.len() != 2 || !tsuccs.contains(&latch) || !tsuccs.contains(&x) {
        return None;
    }

    // The body minus the back edge must be an acyclic DAG covering every body
    // block (each block executes at most once per iteration, and every
    // completed iteration funnels through `T` -> latch).
    if !body_is_acyclic_dag(func, lp) {
        return None;
    }

    // No calls anywhere in the body, and count body size.
    let body_blocks: Vec<BlockId> = func
        .block_order
        .iter()
        .copied()
        .filter(|b| lp.body.contains(b))
        .collect();
    if body_blocks.len() != lp.body.len() {
        return None;
    }
    let mut body_nonterm_insts = 0usize;
    let mut body_total_insts = 0usize;
    for &b in &body_blocks {
        for &iid in &func.block(b).insts {
            let inst = func.inst(iid);
            if inst.is_call() {
                return None;
            }
            body_total_insts += 1;
            if !inst.flags.is_branch() && !inst.flags.is_terminator() {
                body_nonterm_insts += 1;
            }
        }
    }
    if body_nonterm_insts > DIAMOND_UNROLL_MAX_BODY_INSTS {
        return None;
    }

    // ---- `T` tail: [flag_cmp, CSet, CmpRI vcond #0, BCond, B] contiguous ----
    let tinsts = func.block(t).insts.clone();
    if tinsts.len() < 5 {
        return None;
    }
    let b_term = *tinsts.last()?;
    let bcond = tinsts[tinsts.len() - 2];
    let vcond_cmp = tinsts[tinsts.len() - 3];
    let cset = tinsts[tinsts.len() - 4];
    let flag_cmp = tinsts[tinsts.len() - 5];

    let b_inst = func.inst(b_term);
    if b_inst.opcode != AArch64Opcode::B {
        return None;
    }
    let b_target = match b_inst.operands.first()? {
        MachOperand::Block(bb) => *bb,
        _ => return None,
    };
    let bcond_inst = func.inst(bcond);
    if bcond_inst.opcode != AArch64Opcode::BCond {
        return None;
    }
    let cc_br = cc_from_operand(bcond_inst.operands.first()?)?;
    let taken_when_cond_true = match cc_br {
        CondCode::NE => true,
        CondCode::EQ => false,
        _ => return None,
    };
    let bcond_target = match bcond_inst.operands.get(1)? {
        MachOperand::Block(bb) => *bb,
        _ => return None,
    };
    // The two branch targets must be exactly {latch, X}.
    if !((bcond_target == latch && b_target == x) || (bcond_target == x && b_target == latch)) {
        return None;
    }

    // CmpRI vcond, #0.
    let vcmp_inst = func.inst(vcond_cmp);
    if vcmp_inst.opcode != AArch64Opcode::CmpRI
        || vcmp_inst.operands.get(1).and_then(|op| op.as_imm()) != Some(0)
    {
        return None;
    }
    let vcond = vcmp_inst.operands.first()?.as_vreg()?;

    // CSet vcond, cc — and `vcond` must have NO other use anywhere (the whole
    // tail is dropped; a surviving reader would see a dead value).
    let cset_inst = func.inst(cset);
    if cset_inst.opcode != AArch64Opcode::CSet || cset_inst.operands.first()?.as_vreg()? != vcond {
        return None;
    }
    let cc_set = cc_from_operand(cset_inst.operands.get(1)?)?;
    for &blk in &func.block_order {
        for &iid in &func.block(blk).insts {
            if iid == vcond_cmp {
                continue;
            }
            if inst_uses_vreg(func.inst(iid), vcond) {
                return None;
            }
        }
    }

    // The flag-setting compare feeding the CSet: integer CmpRR/CmpRI only.
    let flag_inst = func.inst(flag_cmp);
    let (op_a, op_b_vreg, op_b_imm) = match flag_inst.opcode {
        AArch64Opcode::CmpRR => (
            flag_inst.operands.first()?.as_vreg()?,
            Some(flag_inst.operands.get(1)?.as_vreg()?),
            None,
        ),
        AArch64Opcode::CmpRI => (
            flag_inst.operands.first()?.as_vreg()?,
            None,
            Some(flag_inst.operands.get(1)?.as_imm()?),
        ),
        _ => return None,
    };

    // ---- Identify the IV among the compare operands: either the increment
    //      result (post-inc compare) or the loop-carried IV itself (pre-inc
    //      compare, ReedSolomon's shape). Ambiguity fails closed. ----
    let candidates: Vec<(VReg, bool)> = match (op_b_vreg, op_b_imm) {
        (Some(b), None) => vec![(op_a, true), (b, false)],
        (None, Some(_)) => vec![(op_a, true)],
        _ => return None,
    };
    let mut found: Option<(IvInc, bool, VReg)> = None; // (inc, pre_inc, cand)
    for (cand, is_a) in candidates {
        let m = if let Some(inc) = try_iv_increment(func, def_map, lp, cand, false) {
            Some((IvInc { is_a, ..inc }, false, cand))
        } else {
            try_pre_increment_iv(func, def_map, lp, cand)
                .map(|inc| (IvInc { is_a, ..inc }, true, cand))
        };
        if let Some(m) = m {
            if found.is_some() {
                return None;
            }
            found = Some(m);
        }
    }
    let (iv, pre_inc, cand) = found?;
    if iv.int_step == 0 {
        return None;
    }

    // ---- Exactness of every copy chain the IV value proof rides on. The
    //      `resolve_through_copies` walks above admit narrow extends and
    //      width-changing moves, which are only identities on sub-range
    //      values; require plain same-class move chains instead (fail closed
    //      on anything else). Chains checked: the compare operand -> the IV
    //      expression, the latch phi-copy source -> the increment result,
    //      and (pre-inc form) the increment's source -> the IV. ----
    let compare_target = if pre_inc { iv.iv_vreg } else { iv.inc_dst };
    if !is_plain_move_chain(func, def_map, cand, compare_target) {
        return None;
    }

    // The IV vreg must have EXACTLY the two phi-copy defs (preheader + latch):
    // any third def (e.g. a conditional re-assignment in an arm) breaks the
    // per-iteration `init + m*step` value proof.
    let iv_defs = def_map.get(&iv.iv_vreg)?;
    if iv_defs.len() != 2
        || !iv_defs
            .iter()
            .any(|&id| func.block(preheader).insts.contains(&id))
        || !iv_defs
            .iter()
            .any(|&id| func.block(latch).insts.contains(&id))
    {
        return None;
    }
    // The latch phi-copy must thread the increment result through plain
    // same-class moves, and (pre-inc form) the increment must read the IV
    // through plain moves as well.
    let latch_def = *iv_defs
        .iter()
        .find(|&&id| func.block(latch).insts.contains(&id))?;
    let latch_src = func.inst(latch_def).operands.get(1)?.as_vreg()?;
    if !is_plain_move_chain(func, def_map, latch_src, iv.inc_dst) {
        return None;
    }
    if pre_inc {
        let inc_src = func.inst(iv.inc_inst).operands.get(1)?.as_vreg()?;
        if !is_plain_move_chain(func, def_map, inc_src, iv.iv_vreg) {
            return None;
        }
    }

    // The increment must execute exactly once per iteration BEFORE the latch
    // copy: its block must dominate the latch and not BE the latch. (The
    // latch's sole pred is `T`, so this equals "dominates `T` or is `T`".)
    let inc_block = *body_blocks
        .iter()
        .find(|&&b| func.block(b).insts.contains(&iv.inc_inst))?;
    if inc_block == latch {
        return None;
    }
    let dom = DomTree::compute(func);
    if !dom.dominates(inc_block, latch) {
        return None;
    }
    // Materialization target must be a plain GPR.
    if !matches!(
        iv.inc_dst.class,
        trust_cg_ir::RegClass::Gpr32 | trust_cg_ir::RegClass::Gpr64
    ) {
        return None;
    }

    // ---- Constant init & bound (strict same-class chains only); prove the
    //      trip count exactly. ----
    let init = strict_const_of(func, def_map, iv.init_src)?;
    let bound = if let Some(imm) = op_b_imm {
        imm as i128
    } else if iv.is_a {
        strict_const_of(func, def_map, op_b_vreg?)?
    } else {
        strict_const_of(func, def_map, op_a)?
    };
    let bound_aff = Affine {
        base: None,
        offset: bound,
    };

    let p = rel_from_int_cc(cc_set)?;
    let rel_xl = if iv.is_a { p } else { swap_rel(p) };
    let goes_to_exit_when_taken = bcond_target == x;
    let exit_when_cond_true = goes_to_exit_when_taken == taken_when_cond_true;
    let exit_rel = if exit_when_cond_true {
        rel_xl
    } else {
        negate_rel(rel_xl)
    };
    // The compared IV expression on iteration m is `init + m*step` (post-inc)
    // or `init + (m-1)*step` (pre-inc); shift the simulated init for the
    // latter so `simulate_trip`'s `x = init' + m*step` models it exactly.
    let sim_init = Affine {
        base: None,
        offset: if pre_inc { init - iv.int_step } else { init },
    };
    let width = width_of(op_a);
    let trip_count = simulate_trip(
        sim_init,
        bound_aff,
        iv.int_step,
        exit_rel,
        width,
        DIAMOND_UNROLL_MAX_TRIP + 1,
    )?;
    if !(2..=DIAMOND_UNROLL_MAX_TRIP).contains(&trip_count) {
        return None;
    }

    // Every materialized IV value must fit a 16-bit `Movz` with no register
    // wraparound (this also bounds every folded address offset).
    for m in 0..=trip_count as i128 {
        let v = init + m * iv.int_step;
        if !(0..=0xffff).contains(&v) {
            return None;
        }
    }

    // Code-growth cap.
    if body_total_insts.saturating_mul(trip_count as usize - 1) > DIAMOND_UNROLL_MAX_CLONED_INSTS {
        return None;
    }

    // Quality gate: the unroll exists to convert IV-indexed `Madd` addresses
    // into immediate offsets. Require at least one body `Madd` whose index
    // operand is an affine expression of the IV with a constant multiplier.
    let mut any_iv_madd = false;
    'madd_scan: for &b in &body_blocks {
        for &iid in &func.block(b).insts {
            let inst = func.inst(iid);
            if inst.opcode != AArch64Opcode::Madd || inst.operands.len() != 4 {
                continue;
            }
            let (Some(a), Some(bb), Some(base)) = (
                inst.operands[1].as_vreg(),
                inst.operands[2].as_vreg(),
                inst.operands[3].as_vreg(),
            ) else {
                continue;
            };
            let aff_a = affine_of(func, def_map, a);
            let aff_b = affine_of(func, def_map, bb);
            let mult = if aff_a.base == Some(iv.iv_vreg) && aff_b.base.is_none() {
                aff_b.offset
            } else if aff_b.base == Some(iv.iv_vreg) && aff_a.base.is_none() {
                aff_a.offset
            } else {
                continue;
            };
            if mult > 0 && base != iv.iv_vreg {
                any_iv_madd = true;
                break 'madd_scan;
            }
        }
    }
    if !any_iv_madd {
        return None;
    }

    Some(DiamondConstTripLoop {
        trip_count,
        iv_vreg: iv.iv_vreg,
        inc_inst: iv.inc_inst,
        inc_dst: iv.inc_dst,
        iv_init: init,
        iv_step: iv.int_step,
        test_block: t,
        exit_block: x,
        flag_cmp,
        cset,
        vcond_cmp,
        bcond,
        b_term,
        body_blocks,
    })
}

/// Fully unroll a recognized diamond-body constant-trip loop. See the section
/// note for the soundness argument.
fn unroll_diamond_const_trip(
    func: &mut MachFunction,
    lp: &NaturalLoop,
    dcl: &DiamondConstTripLoop,
    mut provenance: Option<&mut ProvenanceMap>,
) -> bool {
    let header = lp.header;
    let latch = lp.latch;
    let t = dcl.test_block;
    let x = dcl.exit_block;
    let m = dcl.trip_count as usize;
    let body = dcl.body_blocks.clone();

    // Vregs safe to rename to fresh per-clone ids (computed on the ORIGINAL
    // function so dominance is exact). The increment destination keeps its
    // fixed name: it is re-materialized as a per-clone `Movz` and the cloned
    // latch phi-copies must keep reading it.
    let renamable: Vec<VReg> = renamable_body_vregs(func, &body, dcl.inc_dst);

    // `T`'s kept instructions: everything except the dropped trip-test tail.
    let drop_all = [dcl.flag_cmp, dcl.cset, dcl.vcond_cmp, dcl.bcond, dcl.b_term];
    let t_kept: Vec<InstId> = func
        .block(t)
        .insts
        .iter()
        .copied()
        .filter(|id| !drop_all.contains(id))
        .collect();

    // The latch's phi-copies (everything but its back-edge terminator).
    let latch_body: Vec<InstId> = {
        let insts = &func.block(latch).insts;
        insts[..insts.len().saturating_sub(1)].to_vec()
    };

    // ---- Pre-create clone blocks for iterations 2..=m (every body block,
    //      including the latch: its phi-copies keep live-out values exact). ----
    let mut maps: Vec<HashMap<BlockId, BlockId>> = Vec::new();
    for _k in 2..=m {
        let mut map = HashMap::new();
        for &bo in &body {
            let nb = func.create_block();
            map.insert(bo, nb);
        }
        maps.push(map);
    }
    let header_of = |k: usize| -> BlockId { if k == 1 { header } else { maps[k - 2][&header] } };

    // ---- Iteration 1: rewrite the ORIGINAL blocks in place. ----
    // (a) materialize the constant IV increment for iteration 1.
    let loc1 = func.inst(dcl.inc_inst).source_loc;
    *func.inst_mut(dcl.inc_inst) = movz_inst(dcl.inc_dst, dcl.iv_init + dcl.iv_step, loc1);
    if let Some(p) = provenance.as_deref_mut() {
        p.record_in_place_transform(dcl.inc_inst, loop_unroll_pass_id());
    }
    // (b) `T`: drop the trip-test tail, terminate with `B latch` (iteration 1
    //     always continues: trip_count >= 2).
    let drop_t = [dcl.flag_cmp, dcl.cset, dcl.vcond_cmp, dcl.bcond];
    if let Some(p) = provenance.as_deref_mut() {
        for &id in &drop_t {
            p.record_deletion(
                id,
                loop_unroll_pass_id(),
                "loop-unroll dropped diamond constant-trip test after full unroll",
            );
        }
    }
    func.block_mut(t).insts.retain(|id| !drop_t.contains(id));
    for op in &mut func.inst_mut(dcl.b_term).operands {
        if let MachOperand::Block(bb) = op {
            *bb = latch;
        }
    }
    if let Some(p) = provenance.as_deref_mut() {
        p.record_in_place_transform(dcl.b_term, loop_unroll_pass_id());
    }
    func.block_mut(t).succs.retain(|&s| s == latch);
    func.block_mut(x).preds.retain(|&p| p != t);
    // (c) redirect the original latch back edge: header -> iteration-2 header.
    redirect_branch_and_edge(func, latch, header, header_of(2));
    if let Some(p) = provenance.as_deref_mut()
        && let Some(&last) = func.block(latch).insts.last()
    {
        p.record_in_place_transform(last, loop_unroll_pass_id());
    }

    // ---- Iterations 2..=m: populate the clones. ----
    for k in 2..=m {
        let is_last = k == m;
        let map = maps[k - 2].clone();
        let iv_next_k = dcl.iv_init + (k as i128) * dcl.iv_step;

        // Fresh per-clone rename for every safe vreg (deterministic order).
        let vmap: HashMap<VReg, VReg> = renamable
            .iter()
            .map(|&v| (v, VReg::new(func.alloc_vreg(), v.class)))
            .collect();

        for &bo in &body {
            let nb = map[&bo];
            let kept: Vec<InstId> = if bo == t {
                t_kept.clone()
            } else if bo == latch {
                latch_body.clone()
            } else {
                func.block(bo).insts.clone()
            };
            for &iid in &kept {
                let ni = if iid == dcl.inc_inst {
                    let loc = func.inst(iid).source_loc;
                    movz_inst(dcl.inc_dst, iv_next_k, loc)
                } else {
                    clone_inst_remap(func, iid, &map, &vmap)
                };
                let nid = func.push_inst(ni);
                func.append_inst(nb, nid);
                if let Some(p) = provenance.as_deref_mut() {
                    p.record_clone(iid, nid, loop_unroll_pass_id());
                }
            }
            if bo == t {
                // Every clone's `T` continues into its own latch; the trip
                // test's outcome is compile-time proven.
                push_branch(func, nb, map[&latch], provenance.as_deref_mut(), dcl.b_term);
            } else if bo == latch {
                let next = if is_last { x } else { header_of(k + 1) };
                push_branch(func, nb, next, provenance.as_deref_mut(), dcl.b_term);
            }
            wire_out_edges(func, nb);
        }
    }

    // ---- Fold now-constant IV-indexed addresses into memory offsets. ----
    // Within iteration k the loop-carried IV holds exactly `init + (k-1)*step`
    // everywhere except the latch (whose phi-copy advances it for k+1), so
    // fold over each clone's NON-latch blocks only.
    let consts = collect_single_def_movz_consts(func);
    let post_def_map = build_def_map(func);
    let iter1_blocks: Vec<BlockId> = body.iter().copied().filter(|&b| b != latch).collect();
    fold_iv_affine_addresses(
        func,
        &iter1_blocks,
        dcl.iv_vreg,
        dcl.iv_init,
        &consts,
        &post_def_map,
    );
    for k in 2..=m {
        let iv_k = dcl.iv_init + (k as i128 - 1) * dcl.iv_step;
        let blocks: Vec<BlockId> = {
            let mut v: Vec<BlockId> = maps[k - 2]
                .iter()
                .filter(|entry| *entry.0 != latch)
                .map(|entry| *entry.1)
                .collect();
            v.sort_unstable();
            v
        };
        fold_iv_affine_addresses(func, &blocks, dcl.iv_vreg, iv_k, &consts, &post_def_map);
    }

    true
}

/// Constant-evaluate `v` within one unrolled iteration's `blocks`, where the
/// loop-carried `iv` vreg holds exactly `iv_val`: walks the unique-def chain
/// through `AddRI`/`SubRI`/`MovR`/`Copy` whose defs all lie INSIDE `blocks`
/// (clone-local, hence executed with this iteration's IV value), terminating
/// at `iv` itself, at a function-wide single-def `Movz` constant, or at a
/// constant-valued `Movz`/`MovI` inside `blocks`. Returns `None` (no fold) on
/// anything else.
fn clone_const_value(
    func: &MachFunction,
    blocks: &HashSet<BlockId>,
    iv: VReg,
    iv_val: i128,
    consts: &HashMap<VReg, i64>,
    def_map: &HashMap<VReg, Vec<InstId>>,
    v: VReg,
) -> Option<i128> {
    let mut cur = v;
    let mut offset: i128 = 0;
    for _ in 0..16 {
        if cur == iv {
            return Some(iv_val + offset);
        }
        if let Some(&c) = consts.get(&cur) {
            return Some(c as i128 + offset);
        }
        let defs = def_map.get(&cur)?;
        if defs.len() != 1 {
            return None;
        }
        let def_id = defs[0];
        // The def must be clone-local: a def outside this iteration's blocks
        // (e.g. a loop-invariant chained onto the multi-def IV) could have
        // executed under a DIFFERENT IV value.
        if !blocks
            .iter()
            .any(|&b| func.block(b).insts.contains(&def_id))
        {
            return None;
        }
        let inst = func.inst(def_id);
        match inst.opcode {
            AArch64Opcode::Movz => {
                let (dst, value) = crate::reaching_const::movz_value(inst)?;
                if dst != cur {
                    return None;
                }
                return Some(i128::from(value) + offset);
            }
            AArch64Opcode::MovI if inst.operands.len() == 2 => {
                return Some(inst.operands.get(1)?.as_imm()? as i128 + offset);
            }
            AArch64Opcode::AddRI => {
                let src = inst.operands.get(1)?.as_vreg()?;
                if src.class != cur.class {
                    return None;
                }
                offset += inst.operands.get(2)?.as_imm()? as i128;
                cur = src;
            }
            AArch64Opcode::SubRI => {
                let src = inst.operands.get(1)?.as_vreg()?;
                if src.class != cur.class {
                    return None;
                }
                offset -= inst.operands.get(2)?.as_imm()? as i128;
                cur = src;
            }
            AArch64Opcode::MovR | AArch64Opcode::Copy => {
                let src = inst.operands.get(1)?.as_vreg()?;
                if src.class != cur.class {
                    return None;
                }
                cur = src;
            }
            _ => return None,
        }
    }
    None
}

/// Within one unrolled iteration's `blocks` (where the loop-carried `iv`
/// holds the constant `iv_val`), fold `Madd dst, a, b, base` whose `a*b` is a
/// clone-constant product into the offsets of the `LdrRI`/`StrRI` that use
/// `dst`, deleting the `Madd` when every user folds. The extension over
/// `fold_const_index_addresses`: index operands may be affine chains of the
/// IV (`SubRI(iv, #1)` — ReedSolomon's `bb[j-1]`), evaluated by
/// `clone_const_value`. All-or-nothing per `Madd`; fails closed per candidate.
fn fold_iv_affine_addresses(
    func: &mut MachFunction,
    blocks: &[BlockId],
    iv: VReg,
    iv_val: i128,
    consts: &HashMap<VReg, i64>,
    def_map: &HashMap<VReg, Vec<InstId>>,
) {
    let block_set: HashSet<BlockId> = blocks.iter().copied().collect();

    // Candidate `Madd dst, a, b, base` whose `a*b` is a clone constant.
    let mut candidates: Vec<(InstId, VReg, VReg, i128)> = Vec::new();
    for &blk in blocks {
        for &iid in &func.block(blk).insts {
            let inst = func.inst(iid);
            if inst.opcode != AArch64Opcode::Madd || inst.operands.len() != 4 {
                continue;
            }
            let (Some(dst), Some(a), Some(b), Some(base)) = (
                inst.operands[0].as_vreg(),
                inst.operands[1].as_vreg(),
                inst.operands[2].as_vreg(),
                inst.operands[3].as_vreg(),
            ) else {
                continue;
            };
            if dst.class != trust_cg_ir::RegClass::Gpr64 {
                continue;
            }
            let va = clone_const_value(func, &block_set, iv, iv_val, consts, def_map, a);
            let vb = clone_const_value(func, &block_set, iv, iv_val, consts, def_map, b);
            let (Some(va), Some(vb)) = (va, vb) else {
                continue;
            };
            // `base` must be a genuine invariant pointer: not the IV, not a
            // constant, not itself clone-computed from the IV — and SINGLE-DEF
            // function-wide. Rewriting a user to read `base` directly is only
            // sound when the value it sees is provably the value the `Madd`
            // read: with a single def, every path to a (reached) user passes
            // through the `Madd` and hence through that def, and no redefinition
            // can intervene.
            if base == iv
                || clone_const_value(func, &block_set, iv, iv_val, consts, def_map, base).is_some()
                || def_map.get(&base).map(|d| d.len()) != Some(1)
            {
                continue;
            }
            // The Madd must be `dst`'s unique def, and `dst` must never be
            // read outside this iteration's blocks (the fold changes nothing
            // about `base`, but deleting the Madd requires exact use info).
            let Some(dst_defs) = def_map.get(&dst) else {
                continue;
            };
            if dst_defs.len() != 1 || dst_defs[0] != iid {
                continue;
            }
            candidates.push((iid, dst, base, va * vb));
        }
    }

    for (madd, dst, base, off) in candidates {
        // Every use of `dst` anywhere in the function must be inside `blocks`
        // and be the base operand of a `LdrRI`/`StrRI` with an encodable
        // resulting offset; otherwise leave this `Madd` alone.
        let mut rewrites: Vec<(InstId, i64)> = Vec::new();
        let mut foldable = true;
        'scan: for &blk in &func.block_order {
            let in_blocks = block_set.contains(&blk);
            for &iid in &func.block(blk).insts {
                if iid == madd {
                    continue;
                }
                let inst = func.inst(iid);
                for (oi, op) in inst.operands.iter().enumerate() {
                    if op.as_vreg() != Some(dst) {
                        continue;
                    }
                    if !in_blocks
                        || !matches!(inst.opcode, AArch64Opcode::LdrRI | AArch64Opcode::StrRI)
                        || oi != 1
                    {
                        foldable = false;
                        break 'scan;
                    }
                    let Some(asize) = inst.operands.first().and_then(gpr_access_size) else {
                        foldable = false;
                        break 'scan;
                    };
                    let existing = inst.operands.get(2).and_then(|o| o.as_imm()).unwrap_or(0);
                    let newoff = off + existing as i128;
                    if newoff < 0
                        || newoff > i64::MAX as i128
                        || !is_encodable_offset(newoff as i64, asize)
                    {
                        foldable = false;
                        break 'scan;
                    }
                    rewrites.push((iid, newoff as i64));
                }
            }
        }
        if !foldable || rewrites.is_empty() {
            continue;
        }
        for (iid, newoff) in rewrites {
            let inst = func.inst_mut(iid);
            inst.operands[1] = MachOperand::VReg(base);
            inst.operands[2] = MachOperand::Imm(newoff);
        }
        // Drop the now-dead address `Madd`.
        for &blk in &block_set {
            func.block_mut(blk).insts.retain(|&id| id != madd);
        }
    }
}

/// Map every single-def `Movz dst, #imm` to its constant value (loop-invariant
/// scale/const materializations). Multiply-defined vregs (e.g. the per-iteration
/// IV) are excluded — their value is not globally determined.
fn collect_single_def_movz_consts(func: &MachFunction) -> HashMap<VReg, i64> {
    let mut def_count: HashMap<VReg, u32> = HashMap::new();
    for &blk in &func.block_order {
        for &iid in &func.block(blk).insts {
            let inst = func.inst(iid);
            if inst_produces_value(inst)
                && let Some(v) = inst.operands.first().and_then(|op| op.as_vreg())
            {
                *def_count.entry(v).or_default() += 1;
            }
        }
    }
    let mut out: HashMap<VReg, i64> = HashMap::new();
    for &blk in &func.block_order {
        for &iid in &func.block(blk).insts {
            let inst = func.inst(iid);
            if let Some((dst, value)) = crate::reaching_const::movz_value(inst)
                && let Ok(imm) = i64::try_from(value)
                && def_count.get(&dst).copied() == Some(1)
            {
                out.insert(dst, imm);
            }
        }
    }
    out
}

/// The access size (in bytes) a `LdrRI`/`StrRI` uses, from its value register's
/// class: 4 for a 32-bit GPR, 8 for a 64-bit GPR. Other classes -> `None`
/// (fail closed: we do not fold non-GPR or sub-word memory ops here).
fn gpr_access_size(op: &MachOperand) -> Option<u8> {
    use trust_cg_ir::RegClass::*;
    match op.as_vreg()?.class {
        Gpr32 => Some(4),
        Gpr64 => Some(8),
        _ => None,
    }
}

/// Within one unrolled iteration's `blocks` (where `iv_next` holds the constant
/// `iv_val`), fold constant-index `Madd` addresses into the offsets of the
/// `LdrRI`/`StrRI` that use them, deleting the `Madd` when all its users fold.
fn fold_const_index_addresses(
    func: &mut MachFunction,
    blocks: &[BlockId],
    iv_next: VReg,
    iv_val: i128,
    consts: &HashMap<VReg, i64>,
) {
    let block_set: std::collections::HashSet<BlockId> = blocks.iter().copied().collect();

    // Collect candidate `Madd dst, a, b, base` whose `a*b` is a constant offset.
    let mut candidates: Vec<(InstId, VReg, VReg, i128)> = Vec::new();
    for &blk in blocks {
        for &iid in &func.block(blk).insts {
            let inst = func.inst(iid);
            if inst.opcode != AArch64Opcode::Madd || inst.operands.len() < 4 {
                continue;
            }
            let (Some(dst), Some(a), Some(b), Some(base)) = (
                inst.operands[0].as_vreg(),
                inst.operands[1].as_vreg(),
                inst.operands[2].as_vreg(),
                inst.operands[3].as_vreg(),
            ) else {
                continue;
            };
            let off = if a == iv_next {
                consts.get(&b).map(|s| iv_val * *s as i128)
            } else if b == iv_next {
                consts.get(&a).map(|s| iv_val * *s as i128)
            } else if let (Some(&x), Some(&y)) = (consts.get(&a), consts.get(&b)) {
                Some(x as i128 * y as i128)
            } else {
                None
            };
            // `base` must be a genuine pointer register, not the IV or another
            // materialized constant (else `[base, #off]` would be nonsense).
            if let Some(off) = off
                && base != iv_next
                && !consts.contains_key(&base)
            {
                candidates.push((iid, dst, base, off));
            }
        }
    }

    for (madd, dst, base, off) in candidates {
        // Every use of `dst` in this iteration must be the base operand of a
        // `LdrRI`/`StrRI` with an encodable resulting offset; otherwise we can
        // neither rewrite it nor drop the `Madd`.
        let mut rewrites: Vec<(InstId, i64)> = Vec::new();
        let mut foldable = true;
        'scan: for &blk in blocks {
            for &iid in &func.block(blk).insts {
                if iid == madd {
                    continue;
                }
                let inst = func.inst(iid);
                for (oi, op) in inst.operands.iter().enumerate() {
                    if op.as_vreg() != Some(dst) {
                        continue;
                    }
                    if !matches!(inst.opcode, AArch64Opcode::LdrRI | AArch64Opcode::StrRI)
                        || oi != 1
                    {
                        foldable = false;
                        break 'scan;
                    }
                    let Some(asize) = inst.operands.first().and_then(gpr_access_size) else {
                        foldable = false;
                        break 'scan;
                    };
                    let existing = inst.operands.get(2).and_then(|o| o.as_imm()).unwrap_or(0);
                    let newoff = off + existing as i128;
                    if newoff < 0
                        || newoff > i64::MAX as i128
                        || !is_encodable_offset(newoff as i64, asize)
                    {
                        foldable = false;
                        break 'scan;
                    }
                    rewrites.push((iid, newoff as i64));
                }
            }
        }
        if !foldable || rewrites.is_empty() {
            continue;
        }
        for (iid, newoff) in rewrites {
            let inst = func.inst_mut(iid);
            inst.operands[1] = MachOperand::VReg(base);
            inst.operands[2] = MachOperand::Imm(newoff);
        }
        // Drop the now-dead address `Madd`.
        for &blk in &block_set {
            func.block_mut(blk).insts.retain(|&id| id != madd);
        }
    }
}

/// Build a `Movz dst, #value` (16-bit immediate), carrying `loc`.
fn movz_inst(dst: VReg, value: i128, loc: Option<SourceLoc>) -> MachInst {
    let mut inst = MachInst::new(
        AArch64Opcode::Movz,
        vec![MachOperand::VReg(dst), MachOperand::Imm(value as i64)],
    );
    inst.source_loc = loc;
    inst
}

/// Clone `iid` verbatim (preserving flags / implicit defs+uses / proof /
/// source_loc) with its branch-target block operands remapped via `map` and its
/// per-clone-renamed vregs (both defs and uses) remapped via `vmap`. `vmap` only
/// contains vregs proven safe to rename (every use dominated by an in-body def,
/// not live-out, not the induction vreg), so applying it to every vreg operand
/// preserves single-def/single-use for downstream analyses without changing
/// semantics. When `vmap` is empty this is the identity vreg-wise (old behavior).
fn clone_inst_remap(
    func: &MachFunction,
    iid: InstId,
    map: &HashMap<BlockId, BlockId>,
    vmap: &HashMap<VReg, VReg>,
) -> MachInst {
    let mut inst = func.inst(iid).clone();
    for op in &mut inst.operands {
        match op {
            MachOperand::Block(b) => {
                if let Some(&nb) = map.get(b) {
                    *b = nb;
                }
            }
            MachOperand::VReg(v) => {
                if let Some(&nv) = vmap.get(v) {
                    *v = nv;
                }
            }
            _ => {}
        }
    }
    inst
}

/// Append `B -> target` to `block`, recording a clone of `src` for provenance.
fn push_branch(
    func: &mut MachFunction,
    block: BlockId,
    target: BlockId,
    provenance: Option<&mut ProvenanceMap>,
    src: InstId,
) {
    let br = MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(target)]);
    let id = func.push_inst(br);
    func.append_inst(block, id);
    if let Some(p) = provenance {
        p.record_clone(src, id, loop_unroll_pass_id());
    }
}

/// Add out-edges of a freshly-populated clone `block` from its branch operands.
fn wire_out_edges(func: &mut MachFunction, block: BlockId) {
    let mut targets: Vec<BlockId> = Vec::new();
    for &iid in &func.block(block).insts.clone() {
        for op in &func.inst(iid).operands {
            if let MachOperand::Block(b) = op
                && !targets.contains(b)
            {
                targets.push(*b);
            }
        }
    }
    for tgt in targets {
        func.add_edge(block, tgt);
    }
}

/// Redirect `block`'s terminator edge from `old` to `new` (branch operand + CFG
/// preds/succs).
fn redirect_branch_and_edge(func: &mut MachFunction, block: BlockId, old: BlockId, new: BlockId) {
    if let Some(&last) = func.block(block).insts.last() {
        for op in &mut func.inst_mut(last).operands {
            if let MachOperand::Block(b) = op
                && *b == old
            {
                *b = new;
            }
        }
    }
    func.block_mut(block).succs.retain(|s| *s != old);
    func.block_mut(old).preds.retain(|p| *p != block);
    func.add_edge(block, new);
}

fn max_trip_count_for_loop(
    func: &MachFunction,
    lp: &NaturalLoop,
    profile_hotness: Option<&ProfileHotness>,
) -> u64 {
    let Some(block_hotness) =
        profile_hotness.and_then(|hotness| hotness.block(&func.name, lp.header))
    else {
        return TCG_MAX_UNROLL_TRIP_COUNT;
    };

    if block_hotness.class.is_hot() && pgo_hot_unroll_enabled() {
        HOT_MAX_TRIP_COUNT
    } else {
        TCG_MAX_UNROLL_TRIP_COUNT
    }
}

/// Count the number of non-terminator instructions in the loop body.
fn count_body_insts(func: &MachFunction, lp: &NaturalLoop) -> usize {
    let mut count = 0;
    for &block_id in &func.block_order {
        if !lp.body.contains(&block_id) {
            continue;
        }
        let block = func.block(block_id);
        for &inst_id in &block.insts {
            let inst = func.inst(inst_id);
            if !inst.flags.is_branch() && !inst.flags.is_terminator() {
                count += 1;
            }
        }
    }
    count
}

/// Perform full loop unrolling by replicating the body `trip_count` times.
///
/// Strategy: duplicate all loop body blocks for each iteration, rewriting
/// vreg definitions to fresh vregs. Connect iterations sequentially.
/// Remove the back-edge and redirect the last iteration to fall through
/// to the exit.
fn unroll_loop(
    func: &mut MachFunction,
    lp: &NaturalLoop,
    trip_count: usize,
    mut provenance: Option<&mut ProvenanceMap>,
) -> bool {
    if trip_count == 0 {
        // Zero-trip loop: redirect preheader to exit and remove loop blocks.
        return redirect_zero_trip(func, lp, provenance);
    }

    if lp.preheader.is_none() {
        return false;
    }

    // Find the exit block (successor of header not in loop body).
    let exit_block = find_exit_block(func, lp);
    let exit_block = match exit_block {
        Some(eb) => eb,
        None => return false,
    };

    // Collect loop body blocks in block_order sequence (for deterministic iteration).
    let body_blocks: Vec<BlockId> = func
        .block_order
        .iter()
        .copied()
        .filter(|b| lp.body.contains(b))
        .collect();

    // Collect all non-terminator instructions from body blocks.
    let mut body_insts: Vec<(BlockId, InstId)> = Vec::new();
    for &bid in &body_blocks {
        let block = func.block(bid);
        for &iid in &block.insts {
            let inst = func.inst(iid);
            if !inst.flags.is_branch()
                && !inst.flags.is_terminator()
                && inst.opcode != AArch64Opcode::CmpRI
                && inst.opcode != AArch64Opcode::CmpRR
                && inst.opcode != AArch64Opcode::Phi
            {
                body_insts.push((bid, iid));
            }
        }
    }

    // For each unrolled iteration, duplicate the body instructions into
    // the preheader block (simple case: all go into a single linear block).
    // This is a simplified unrolling that works for simple single-block loops.
    // Multi-block loop bodies are not supported for now.
    if body_blocks.len() > 2 {
        // For now, only handle loops with header + latch (2 blocks) or
        // just header (self-loop, 1 block).
        return false;
    }

    // Clone body instructions for (trip_count - 1) additional iterations.
    // The original loop body serves as iteration 0; we add copies for 1..trip_count-1.
    // After all copies, redirect the latch's back-edge to the exit block.

    // Build vreg rename map for each iteration.
    // Collect all vregs defined in the loop body.
    let mut defined_vregs: Vec<VReg> = Vec::new();
    for &(_bid, iid) in &body_insts {
        let inst = func.inst(iid);
        if inst_produces_value(inst)
            && let Some(vreg) = inst.operands.first().and_then(|op| op.as_vreg())
        {
            defined_vregs.push(vreg);
        }
    }

    // Create a "flattened" block for the unrolled iterations after the existing body.
    // We'll insert duplicated instructions into a new block for each unrolled copy,
    // then replace the back-edge with a fall-through.

    let mut prev_rename: HashMap<VReg, VReg> = HashMap::new();
    let mut new_blocks: Vec<BlockId> = Vec::new();
    let latch_branch_id = func.block(lp.latch).insts.last().copied();
    let latch_branch_source_loc = latch_branch_id.and_then(|id| func.inst(id).source_loc);

    for _iter in 1..trip_count {
        // Create a new block for this iteration.
        let new_block = func.create_block();
        new_blocks.push(new_block);

        // Build rename map: old vreg -> new vreg for this iteration.
        let mut rename: HashMap<VReg, VReg> = HashMap::new();
        for &vreg in &defined_vregs {
            let new_id = func.alloc_vreg();
            rename.insert(vreg, VReg::new(new_id, vreg.class));
        }

        // Clone each body instruction with renamed operands.
        for &(_bid, iid) in &body_insts {
            let inst = func.inst(iid);
            let new_operands: Vec<MachOperand> = inst
                .operands
                .iter()
                .enumerate()
                .map(|(idx, op)| {
                    if let MachOperand::VReg(vreg) = op {
                        // For the def (operand 0 on value-producing insts), use this iter's rename.
                        if idx == 0
                            && inst_produces_value(inst)
                            && let Some(&new_vreg) = rename.get(vreg)
                        {
                            return MachOperand::VReg(new_vreg);
                        }
                        // For uses: use the previous iteration's version of
                        // this vreg (connecting iteration N to iteration N-1).
                        if let Some(&prev_vreg) = prev_rename.get(vreg) {
                            return MachOperand::VReg(prev_vreg);
                        }
                    }
                    op.clone()
                })
                .collect();

            let mut new_inst = MachInst::new(inst.opcode, new_operands);
            new_inst.source_loc = inst.source_loc;
            let new_inst_id = func.push_inst(new_inst);
            func.append_inst(new_block, new_inst_id);
            if let Some(provenance) = provenance.as_deref_mut() {
                provenance.record_clone(iid, new_inst_id, loop_unroll_pass_id());
            }
        }

        prev_rename = rename;
    }

    // Wire up the control flow:
    // 1. Latch -> first new block (instead of back to header).
    // 2. Each new block falls through to the next.
    // 3. Last new block falls through to exit.

    if !new_blocks.is_empty() {
        // Redirect latch's back-edge: replace B header -> B new_blocks[0]
        if let Some(branch_id) = rewrite_branch_target(func, lp.latch, lp.header, new_blocks[0])
            && let Some(provenance) = provenance.as_deref_mut()
        {
            provenance.record_in_place_transform(branch_id, loop_unroll_pass_id());
        }
        func.block_mut(lp.latch).succs.retain(|&s| s != lp.header);
        func.block_mut(lp.header).preds.retain(|&p| p != lp.latch);
        func.add_edge(lp.latch, new_blocks[0]);

        // Chain new blocks together.
        for i in 0..new_blocks.len() - 1 {
            let mut br_inst = MachInst::new(
                AArch64Opcode::B,
                vec![MachOperand::Block(new_blocks[i + 1])],
            );
            br_inst.source_loc = latch_branch_source_loc;
            let br = func.push_inst(br_inst);
            func.append_inst(new_blocks[i], br);
            if let (Some(source), Some(provenance)) = (latch_branch_id, provenance.as_deref_mut()) {
                provenance.record_clone(source, br, loop_unroll_pass_id());
            }
            func.add_edge(new_blocks[i], new_blocks[i + 1]);
        }

        // Last new block branches to exit.
        // SAFETY: `new_blocks` is non-empty (checked by enclosing if-guard).
        let last = new_blocks[new_blocks.len() - 1];
        let mut br_inst = MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(exit_block)]);
        br_inst.source_loc = latch_branch_source_loc;
        let br = func.push_inst(br_inst);
        func.append_inst(last, br);
        if let (Some(source), Some(provenance)) = (latch_branch_id, provenance.as_deref_mut()) {
            provenance.record_clone(source, br, loop_unroll_pass_id());
        }
        func.add_edge(last, exit_block);
    } else {
        // trip_count == 1: just remove the back-edge, redirect latch to exit.
        if let Some(branch_id) = rewrite_branch_target(func, lp.latch, lp.header, exit_block)
            && let Some(provenance) = provenance.as_deref_mut()
        {
            provenance.record_in_place_transform(branch_id, loop_unroll_pass_id());
        }
        func.block_mut(lp.latch).succs.retain(|&s| s != lp.header);
        func.block_mut(lp.header).preds.retain(|&p| p != lp.latch);
        func.add_edge(lp.latch, exit_block);
    }

    // Remove the conditional branch from the header (it always falls through now).
    // Replace BCond with unconditional B to the first body block after header.
    let first_body_after_header: Option<BlockId> = func
        .block(lp.header)
        .succs
        .iter()
        .find(|&&s| lp.body.contains(&s) && s != lp.header)
        .copied();

    if let Some(body_entry) = first_body_after_header {
        let header_block = func.block(lp.header);
        if let Some(&last_id) = header_block.insts.last() {
            let last_inst = func.inst(last_id);
            if last_inst.opcode == AArch64Opcode::BCond {
                // Replace BCond with unconditional B to body.
                let source_loc = last_inst.source_loc;
                let mut branch =
                    MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(body_entry)]);
                branch.source_loc = source_loc;
                *func.inst_mut(last_id) = branch;
                if let Some(provenance) = provenance.as_deref_mut() {
                    provenance.record_in_place_transform(last_id, loop_unroll_pass_id());
                }
                // Remove exit edge from header.
                func.block_mut(lp.header).succs.retain(|&s| s != exit_block);
                func.block_mut(exit_block).preds.retain(|&p| p != lp.header);
            }
        }
        // Also remove the CmpRI from header (no longer needed).
        // Collect IDs to remove first to avoid borrow conflict.
        let cmp_insts: Vec<InstId> = func
            .block(lp.header)
            .insts
            .iter()
            .copied()
            .filter(|&iid| {
                let inst = func.inst(iid);
                inst.opcode == AArch64Opcode::CmpRI || inst.opcode == AArch64Opcode::CmpRR
            })
            .collect();
        if let Some(provenance) = provenance {
            for &cmp_id in &cmp_insts {
                provenance.record_deletion(
                    cmp_id,
                    loop_unroll_pass_id(),
                    "loop-unroll removed trip-count compare after full unroll",
                );
            }
        }
        let header_block = func.block_mut(lp.header);
        header_block.insts.retain(|iid| !cmp_insts.contains(iid));
    }

    true
}

/// Find the exit block of a loop (successor of header not in loop body).
fn find_exit_block(func: &MachFunction, lp: &NaturalLoop) -> Option<BlockId> {
    func.block(lp.header)
        .succs
        .iter()
        .find(|&&succ| !lp.body.contains(&succ))
        .copied()
}

/// Redirect preheader to exit for zero-trip loops.
fn redirect_zero_trip(
    func: &mut MachFunction,
    lp: &NaturalLoop,
    provenance: Option<&mut ProvenanceMap>,
) -> bool {
    let preheader = match lp.preheader {
        Some(ph) => ph,
        None => return false,
    };
    let exit_block = match find_exit_block(func, lp) {
        Some(eb) => eb,
        None => return false,
    };

    // Rewrite preheader's branch to go directly to exit.
    let rewritten_branch = rewrite_branch_target(func, preheader, lp.header, exit_block);
    if let (Some(branch_id), Some(provenance)) = (rewritten_branch, provenance) {
        provenance.record_in_place_transform(branch_id, loop_unroll_pass_id());
    }

    // Update CFG edges.
    func.block_mut(preheader).succs.retain(|&s| s != lp.header);
    func.block_mut(lp.header).preds.retain(|&p| p != preheader);
    func.add_edge(preheader, exit_block);

    true
}

/// Rewrite branch targets in the terminator of `block` from `old_target` to `new_target`.
fn rewrite_branch_target(
    func: &mut MachFunction,
    block: BlockId,
    old_target: BlockId,
    new_target: BlockId,
) -> Option<InstId> {
    let block_data = func.block(block);
    if let Some(&last_id) = block_data.insts.last() {
        let inst = func.inst_mut(last_id);
        let mut changed = false;
        for op in &mut inst.operands {
            if let MachOperand::Block(target) = op
                && *target == old_target
            {
                *target = new_target;
                changed = true;
            }
        }
        if changed {
            return Some(last_id);
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pass_manager::MachinePass;
    use crate::pgo::{BlockProfile, FunctionProfile, ProfData, ProfileHotness};
    use trust_cg_ir::{
        AArch64Opcode, BlockId, CondCode, MachFunction, MachInst, MachOperand, PReg, RegClass,
        Signature, SourceLoc, TransformKind, TrustIrInstId, VReg,
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

    fn source_loc(line: u32) -> SourceLoc {
        SourceLoc {
            file: 0,
            line,
            col: 1,
        }
    }

    fn profile_hotness_for_named_header(
        function_name: &str,
        block: BlockId,
        hits: u64,
        function_count: u64,
    ) -> ProfileHotness {
        let mut profile = ProfData::new(0x396);
        let mut function = FunctionProfile::new(function_name);
        function.call_count = function_count;
        function.blocks.push(BlockProfile::new(block.0, hits));
        profile.functions.push(function);
        ProfileHotness::from_profile(&profile)
    }

    fn profile_hotness_for_header(hits: u64, function_count: u64) -> ProfileHotness {
        profile_hotness_for_named_header("counting_loop", BlockId(1), hits, function_count)
    }

    /// Build a simple counting loop:
    ///
    /// ```text
    ///   bb0 (preheader):
    ///     v0 = MovI #0          ; IV init
    ///     B bb1
    ///
    ///   bb1 (header):
    ///     v1 = Phi [v0, bb0], [v3, bb3]  ; IV
    ///     CmpRI v1, #N          ; compare IV to limit
    ///     BCond bb2, bb3        ; if >= N, exit to bb2
    ///
    ///   bb3 (latch):
    ///     v2 = AddRI v1, v1, #1 ; body work (use IV)
    ///     v3 = AddRI v1, v1, #1 ; IV increment
    ///     B bb1                 ; back-edge
    ///
    ///   bb2 (exit):
    ///     Ret
    /// ```
    fn make_counting_loop(trip_count: i64) -> MachFunction {
        let mut func =
            MachFunction::new("counting_loop".to_string(), Signature::new(vec![], vec![]));
        let bb0 = func.entry; // preheader
        let bb1 = func.create_block(); // header
        let bb2 = func.create_block(); // exit
        let bb3 = func.create_block(); // latch

        // bb0: preheader
        let init = func.push_inst(MachInst::new(AArch64Opcode::MovI, vec![vreg(0), imm(0)]));
        func.append_inst(bb0, init);
        let br0 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb1)],
        ));
        func.append_inst(bb0, br0);

        // bb1: header
        let phi = func.push_inst(MachInst::new(
            AArch64Opcode::Phi,
            vec![
                vreg(1),
                vreg(0),
                MachOperand::Block(bb0),
                vreg(3),
                MachOperand::Block(bb3),
            ],
        ));
        func.append_inst(bb1, phi);
        let cmp = func.push_inst(MachInst::new(
            AArch64Opcode::CmpRI,
            vec![vreg(1), imm(trip_count)],
        ));
        func.append_inst(bb1, cmp);
        let bcond = func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![MachOperand::Block(bb2), MachOperand::Block(bb3)],
        ));
        func.append_inst(bb1, bcond);

        // bb3: latch (body + IV update)
        let body_work = func.push_inst(MachInst::new(
            AArch64Opcode::AddRI,
            vec![vreg(2), vreg(1), imm(10)],
        ));
        func.append_inst(bb3, body_work);
        let iv_inc = func.push_inst(MachInst::new(
            AArch64Opcode::AddRI,
            vec![vreg(3), vreg(1), imm(1)],
        ));
        func.append_inst(bb3, iv_inc);
        let br3 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb1)],
        ));
        func.append_inst(bb3, br3);

        // bb2: exit
        let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb2, ret);

        // CFG edges
        func.add_edge(bb0, bb1);
        func.add_edge(bb1, bb2);
        func.add_edge(bb1, bb3);
        func.add_edge(bb3, bb1);

        func
    }

    #[test]
    fn test_unroll_trip_count_2() {
        let mut func = make_counting_loop(2);
        let mut pass = LoopUnroll::default();
        let changed = pass.run(&mut func);
        assert!(changed, "loop with trip count 2 should be unrolled");

        // After unrolling, the back-edge bb3 -> bb1 should be removed.
        // The latch should no longer branch to the header.
        let latch = func.block(BlockId(3));
        let has_backedge = latch.succs.contains(&BlockId(1));
        assert!(!has_backedge, "back-edge should be removed after unrolling");
    }

    #[test]
    fn test_unroll_trip_count_1() {
        let mut func = make_counting_loop(1);
        let mut pass = LoopUnroll::default();
        let changed = pass.run(&mut func);
        assert!(changed, "loop with trip count 1 should be unrolled");

        // Single iteration: latch should go to exit (bb2), not header (bb1).
        let latch = func.block(BlockId(3));
        assert!(
            !latch.succs.contains(&BlockId(1)),
            "back-edge should be removed"
        );
    }

    #[test]
    fn test_unroll_trip_count_4() {
        let mut func = make_counting_loop(4);
        let mut pass = LoopUnroll::default();
        let changed = pass.run(&mut func);
        assert!(changed, "loop with trip count 4 should be unrolled");
    }

    /// Build a bounded early-exit loop (Queens `Try` shape): a rotated,
    /// copy-threaded IV whose back-edge is guarded by
    /// `AndRR(CSet(iv_next != K), CSet(dynamic))`, with a multi-block body.
    ///
    /// ```text
    ///   bb0 preheader: v0=Movz#0; v1=MovR v0; B bb1
    ///   bb1 header:    v2=AddRI v1,#1; B bb2
    ///   bb2 mid:       v6=AddRI v2,#5; B bb3
    ///   bb3 T:         CmpRI v1,#0; CSet v3,EQ(dyn)
    ///                  CmpRI v2,#K; CSet v4,NE(trip)
    ///                  AndRR v5,v4,v3; CmpRI v5,#0; BCond[NE] bb4; B bb5
    ///   bb4 latch:     v1=MovR v2; B bb1
    ///   bb5 exit:      Ret
    /// ```
    fn make_bounded_early_exit_loop(k: i64) -> MachFunction {
        let mut func = MachFunction::new("bee_loop".to_string(), Signature::new(vec![], vec![]));
        let bb0 = func.entry;
        let bb1 = func.create_block();
        let bb2 = func.create_block();
        let bb3 = func.create_block();
        let bb4 = func.create_block();
        let bb5 = func.create_block();

        let push = |func: &mut MachFunction, blk, op, ops: Vec<MachOperand>| {
            let id = func.push_inst(MachInst::new(op, ops));
            func.append_inst(blk, id);
        };

        // preheader
        push(&mut func, bb0, AArch64Opcode::Movz, vec![vreg(0), imm(0)]);
        push(&mut func, bb0, AArch64Opcode::MovR, vec![vreg(1), vreg(0)]);
        push(
            &mut func,
            bb0,
            AArch64Opcode::B,
            vec![MachOperand::Block(bb1)],
        );
        // header
        push(
            &mut func,
            bb1,
            AArch64Opcode::AddRI,
            vec![vreg(2), vreg(1), imm(1)],
        );
        push(
            &mut func,
            bb1,
            AArch64Opcode::B,
            vec![MachOperand::Block(bb2)],
        );
        // mid (body work)
        push(
            &mut func,
            bb2,
            AArch64Opcode::AddRI,
            vec![vreg(6), vreg(2), imm(5)],
        );
        push(
            &mut func,
            bb2,
            AArch64Opcode::B,
            vec![MachOperand::Block(bb3)],
        );
        // T (exit-test)
        push(&mut func, bb3, AArch64Opcode::CmpRI, vec![vreg(1), imm(0)]);
        push(&mut func, bb3, AArch64Opcode::CSet, vec![vreg(3), imm(0)]); // EQ -> dyn
        push(&mut func, bb3, AArch64Opcode::CmpRI, vec![vreg(2), imm(k)]);
        push(&mut func, bb3, AArch64Opcode::CSet, vec![vreg(4), imm(1)]); // NE -> trip
        push(
            &mut func,
            bb3,
            AArch64Opcode::AndRR,
            vec![vreg(5), vreg(4), vreg(3)],
        );
        push(&mut func, bb3, AArch64Opcode::CmpRI, vec![vreg(5), imm(0)]);
        push(
            &mut func,
            bb3,
            AArch64Opcode::BCond,
            vec![imm(1), MachOperand::Block(bb4)],
        );
        push(
            &mut func,
            bb3,
            AArch64Opcode::B,
            vec![MachOperand::Block(bb5)],
        );
        // latch
        push(&mut func, bb4, AArch64Opcode::MovR, vec![vreg(1), vreg(2)]);
        push(
            &mut func,
            bb4,
            AArch64Opcode::B,
            vec![MachOperand::Block(bb1)],
        );
        // exit
        push(&mut func, bb5, AArch64Opcode::Ret, vec![]);

        func.add_edge(bb0, bb1);
        func.add_edge(bb1, bb2);
        func.add_edge(bb2, bb3);
        func.add_edge(bb3, bb4);
        func.add_edge(bb3, bb5);
        func.add_edge(bb4, bb1);
        func
    }

    #[test]
    fn test_bounded_early_exit_unroll_fires_and_materializes_constant_iv() {
        let mut func = make_bounded_early_exit_loop(3); // K=3 => 3 iterations
        let blocks_before = func.num_blocks();
        let mut pass = LoopUnroll::default();
        let changed = pass.run(&mut func);

        assert!(changed, "bounded early-exit loop should be unrolled");
        // Back-edge bb4 -> bb1 must be gone (fully unrolled, no loop).
        assert!(
            !func.block(BlockId(4)).succs.contains(&BlockId(1)),
            "the original latch back-edge must be redirected off the header"
        );
        assert!(
            !func.block(BlockId(1)).preds.contains(&BlockId(4)),
            "header must no longer have the latch as a predecessor"
        );
        // New iteration clones were created (2 extra iters; last skips latch).
        assert!(
            func.num_blocks() > blocks_before,
            "unrolling must create clone blocks"
        );
        // The IV is materialized as the per-iteration constants 1,2,3 (Movz),
        // and the AddRI increment is gone.
        let mut iv_consts: Vec<i64> = Vec::new();
        let mut any_iv_addri = false;
        for &blk in &func.block_order {
            for &iid in &func.block(blk).insts {
                let inst = func.inst(iid);
                let is_iv_def = inst.operands.first().and_then(|o| o.as_vreg())
                    == Some(VReg::new(2, RegClass::Gpr64));
                if is_iv_def && inst.opcode == AArch64Opcode::Movz {
                    iv_consts.push(inst.operands[1].as_imm().unwrap());
                }
                if is_iv_def && inst.opcode == AArch64Opcode::AddRI {
                    any_iv_addri = true;
                }
            }
        }
        iv_consts.sort_unstable();
        assert_eq!(
            iv_consts,
            vec![1, 2, 3],
            "each iteration's IV must be its exact constant value"
        );
        assert!(
            !any_iv_addri,
            "the IV increment must be replaced by a materialized constant"
        );
    }

    #[test]
    fn test_bounded_early_exit_clones_rename_body_defs_to_fresh_single_defs() {
        // The dynamic-condition CSet temp (v3) and every other in-body,
        // non-loop-carried def must be renamed to a FRESH id in each clone, so
        // the single-def/single-use invariant that cmp_branch_fusion relies on
        // is restored. Regression guard for the per-clone vreg rename.
        let mut func = make_bounded_early_exit_loop(3); // K=3 => 3 iterations.
        let mut pass = LoopUnroll::default();
        assert!(pass.run(&mut func));

        // The original dynamic-condition vreg (v3) must be DEFINED by a CSet in
        // exactly one place after unroll (iteration 1, in the original blocks);
        // the two clones each got their own fresh CSet destination.
        let dyn_orig = VReg::new(3, RegClass::Gpr64);
        let mut dyn_orig_cset_defs = 0usize;
        let mut total_cset_defs = 0usize;
        for &blk in &func.block_order {
            for &iid in &func.block(blk).insts {
                let inst = func.inst(iid);
                if inst.opcode == AArch64Opcode::CSet {
                    total_cset_defs += 1;
                    if inst.operands.first().and_then(|o| o.as_vreg()) == Some(dyn_orig) {
                        dyn_orig_cset_defs += 1;
                    }
                }
            }
        }
        assert_eq!(
            dyn_orig_cset_defs, 1,
            "the dynamic-condition temp must be single-def after unroll (renamed per clone)"
        );
        // The trip-limit CSet is dropped in every iteration (compile-time TRUE),
        // so only the dynamic-condition CSet survives: 1 (iter1) + 1 + 1 (the two
        // clones, each with its own fresh id) == 3.
        assert_eq!(
            total_cset_defs, 3,
            "each clone must retain its own fresh dynamic-condition CSet"
        );

        // Every clone's continue-test `CmpRI vcond, #0` must read a vreg that is
        // DEFINED by a CSet in the SAME block — i.e. the dyn override was
        // rewired to that clone's renamed condition (not the stale original).
        for &blk in &func.block_order {
            let insts = &func.block(blk).insts;
            // A T-clone ends with ... CmpRI vc,#0 ; BCond ; B.
            if insts.len() < 3 {
                continue;
            }
            let cmp = func.inst(insts[insts.len() - 3]);
            let bcond = func.inst(insts[insts.len() - 2]);
            if cmp.opcode != AArch64Opcode::CmpRI
                || bcond.opcode != AArch64Opcode::BCond
                || cmp.operands.get(1).and_then(|o| o.as_imm()) != Some(0)
            {
                continue;
            }
            let Some(vc) = cmp.operands.first().and_then(|o| o.as_vreg()) else {
                continue;
            };
            let defined_here = insts.iter().any(|&iid| {
                let i = func.inst(iid);
                i.opcode == AArch64Opcode::CSet
                    && i.operands.first().and_then(|o| o.as_vreg()) == Some(vc)
            });
            assert!(
                defined_here,
                "clone {blk:?}: continue-test must read a CSet defined in the same clone"
            );
        }
    }

    #[test]
    fn test_bounded_early_exit_refuses_non_boolean_dynamic_condition() {
        // If the dynamic AndRR operand is not a CSet (0/1 boolean), the branch
        // rewrite `dyn != 0` would not match `AndRR(1, dyn) = dyn & 1`; the
        // recognizer must fail closed.
        let mut func = make_bounded_early_exit_loop(3);
        // Replace the dynamic CSet (v3) with a plain AddRI (non-boolean).
        for &blk in &func.block_order.clone() {
            for &iid in &func.block(blk).insts.clone() {
                let inst = func.inst(iid);
                if inst.opcode == AArch64Opcode::CSet
                    && inst.operands.first().and_then(|o| o.as_vreg())
                        == Some(VReg::new(3, RegClass::Gpr64))
                {
                    *func.inst_mut(iid) =
                        MachInst::new(AArch64Opcode::AddRI, vec![vreg(3), vreg(1), imm(7)]);
                }
            }
        }
        let mut pass = LoopUnroll::default();
        let changed = pass.run(&mut func);
        assert!(
            !changed,
            "must fail closed when the dynamic condition is not a 0/1 boolean"
        );
    }

    #[test]
    fn test_bounded_early_exit_refuses_trip_over_cap() {
        // K above BEE_MAX_TRIP_COUNT must not unroll.
        let mut func = make_bounded_early_exit_loop(BEE_MAX_TRIP_COUNT as i64 + 1);
        let mut pass = LoopUnroll::default();
        let changed = pass.run(&mut func);
        assert!(!changed, "trip count above the cap must fail closed");
    }

    #[test]
    fn test_trip_count_ignores_same_id_different_class_latch_update_decoy() {
        let mut func = make_counting_loop(2);
        let decoy = func.push_inst(MachInst::new(
            AArch64Opcode::AddRI,
            vec![
                vreg_class(3, RegClass::Gpr32),
                vreg_class(1, RegClass::Gpr32),
                imm(-1),
            ],
        ));
        func.block_mut(BlockId(3)).insts.insert(1, decoy);

        let mut pass = LoopUnroll::default();
        let changed = pass.run(&mut func);

        assert!(
            changed,
            "same numeric ids in another register class must not hide the real IV update"
        );
        assert!(
            !func.block(BlockId(3)).succs.contains(&BlockId(1)),
            "class-exact trip-count matching should still remove the latch back-edge"
        );
    }

    #[test]
    fn test_body_clone_renames_same_id_different_class_defs_separately() {
        let mut func = make_counting_loop(2);
        let same_id_gpr32_def = func.push_inst(MachInst::new(
            AArch64Opcode::AddRI,
            vec![
                vreg_class(2, RegClass::Gpr32),
                vreg_class(1, RegClass::Gpr32),
                imm(7),
            ],
        ));
        let latch_insts = &mut func.block_mut(BlockId(3)).insts;
        let branch_pos = latch_insts.len() - 1;
        latch_insts.insert(branch_pos, same_id_gpr32_def);

        let mut pass = LoopUnroll::default();
        assert!(pass.run(&mut func));

        let cloned_block = func
            .block_order
            .iter()
            .copied()
            .find(|block| block.0 > 3)
            .expect("trip-count 2 unroll should create one cloned body block");
        let cloned_add_defs: Vec<VReg> = func
            .block(cloned_block)
            .insts
            .iter()
            .filter_map(|&inst_id| {
                let inst = func.inst(inst_id);
                (inst.opcode == AArch64Opcode::AddRI)
                    .then(|| inst.operands.first().and_then(|op| op.as_vreg()))
                    .flatten()
            })
            .collect();

        assert_eq!(
            cloned_add_defs.len(),
            3,
            "the cloned body should keep both same-id defs plus the IV update"
        );
        assert_eq!(cloned_add_defs[0].class, RegClass::Gpr64);
        assert_eq!(cloned_add_defs[2].class, RegClass::Gpr32);
        assert_ne!(
            cloned_add_defs[0].id, cloned_add_defs[2].id,
            "same numeric id in different classes must receive distinct cloned vreg ids"
        );
    }

    #[test]
    fn test_no_unroll_trip_count_5() {
        let mut func = make_counting_loop(5);
        let original_block_count = func.num_blocks();
        let mut pass = LoopUnroll::default();
        let changed = pass.run(&mut func);
        assert!(
            !changed,
            "loop with trip count 5 should NOT be unrolled (exceeds TCG_MAX_UNROLL_TRIP_COUNT)"
        );
        assert_eq!(func.num_blocks(), original_block_count);
    }

    #[test]
    fn test_hot_profile_header_raises_full_unroll_limit() {
        let mut func = make_counting_loop((TCG_MAX_UNROLL_TRIP_COUNT + 1) as i64);
        let hotness = profile_hotness_for_header(100, 100);
        let mut pass = LoopUnroll::new(Some(hotness));

        let changed = pass.run(&mut func);

        assert!(
            changed,
            "hot loop header should allow trip count {} to be fully unrolled",
            TCG_MAX_UNROLL_TRIP_COUNT + 1
        );
        assert!(
            !func.block(BlockId(3)).succs.contains(&BlockId(1)),
            "hot-profile unroll should remove the latch back-edge"
        );
    }

    #[test]
    fn test_hot_profile_header_adjustment_is_bounded() {
        let hotness = profile_hotness_for_header(100, 100);
        let mut at_hot_limit = make_counting_loop(HOT_MAX_TRIP_COUNT as i64);
        let mut at_hot_limit_pass = LoopUnroll::new(Some(hotness.clone()));

        assert!(
            at_hot_limit_pass.run(&mut at_hot_limit),
            "hot profile should allow full unroll at the bounded hot limit"
        );

        let mut above_hot_limit = make_counting_loop((HOT_MAX_TRIP_COUNT + 1) as i64);
        let original_block_count = above_hot_limit.num_blocks();
        let mut above_hot_limit_pass = LoopUnroll::new(Some(hotness));

        assert!(
            !above_hot_limit_pass.run(&mut above_hot_limit),
            "hot profile should not unroll past the bounded hot limit"
        );
        assert_eq!(above_hot_limit.num_blocks(), original_block_count);
    }

    #[test]
    fn test_non_hot_profile_headers_keep_default_full_unroll_limit() {
        let cases = [
            ("missing", None),
            ("cold", Some(profile_hotness_for_header(5, 100))),
            ("warm", Some(profile_hotness_for_header(50, 100))),
        ];

        for (case, hotness) in cases {
            let mut func = make_counting_loop((TCG_MAX_UNROLL_TRIP_COUNT + 1) as i64);
            let original_block_count = func.num_blocks();
            let mut pass = LoopUnroll::new(hotness);

            let changed = pass.run(&mut func);

            assert!(
                !changed,
                "{case} profile data should keep the default full-unroll limit"
            );
            assert_eq!(func.num_blocks(), original_block_count, "{case}");
        }
    }

    #[test]
    fn test_mismatched_profile_records_keep_default_full_unroll_limit() {
        let cases = [
            (
                "other function",
                profile_hotness_for_named_header("other_function", BlockId(1), 100, 100),
            ),
            (
                "other block",
                profile_hotness_for_named_header("counting_loop", BlockId(2), 100, 100),
            ),
        ];

        for (case, hotness) in cases {
            let mut func = make_counting_loop((TCG_MAX_UNROLL_TRIP_COUNT + 1) as i64);
            let original_block_count = func.num_blocks();
            let mut pass = LoopUnroll::new(Some(hotness));

            assert!(
                !pass.run(&mut func),
                "{case} profile records should keep the default full-unroll limit"
            );
            assert_eq!(func.num_blocks(), original_block_count, "{case}");
        }
    }

    #[test]
    fn test_no_unroll_no_loop() {
        // Simple function with no loop.
        let mut func = MachFunction::new("no_loop".to_string(), Signature::new(vec![], vec![]));
        let bb0 = func.entry;
        let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb0, ret);

        let mut pass = LoopUnroll::default();
        assert!(!pass.run(&mut func));
    }

    #[test]
    fn test_unroll_idempotent() {
        let mut func = make_counting_loop(2);
        let mut pass = LoopUnroll::default();

        // First run unrolls the loop.
        let changed1 = pass.run(&mut func);
        assert!(changed1);

        // Second run should find nothing to do (loop structure is gone).
        let changed2 = pass.run(&mut func);
        assert!(!changed2, "second unroll pass should be idempotent");
    }

    #[test]
    fn test_unroll_preserves_body_instructions() {
        let mut func = make_counting_loop(3);
        let mut pass = LoopUnroll::default();
        pass.run(&mut func);

        // Count total AddRI instructions across all blocks.
        // Original had 2 AddRI (body_work + iv_inc), unrolled 3x should have 6.
        let mut add_count = 0;
        for &bid in &func.block_order {
            let block = func.block(bid);
            for &iid in &block.insts {
                let inst = func.inst(iid);
                if inst.opcode == AArch64Opcode::AddRI {
                    add_count += 1;
                }
            }
        }
        // Original 2 in latch + 2*2 in unrolled copies = 6 total
        assert!(
            add_count >= 4,
            "unrolled loop should have at least 4 AddRI instructions, got {}",
            add_count
        );
    }

    #[test]
    fn test_source_loc_preserved_on_unrolled_body_clones() {
        let loc = source_loc(81);
        let mut func = make_counting_loop(3);

        let body_work = func.block(BlockId(3)).insts[0];
        func.inst_mut(body_work).source_loc = Some(loc);

        let mut pass = LoopUnroll::default();
        assert!(pass.run(&mut func));

        let with_loc = func
            .block_order
            .iter()
            .flat_map(|&bid| func.block(bid).insts.iter().copied())
            .filter(|&iid| {
                let inst = func.inst(iid);
                inst.opcode == AArch64Opcode::AddRI && inst.source_loc == Some(loc)
            })
            .count();

        assert_eq!(
            with_loc, 3,
            "loop-unroll must preserve source_loc on the original body instruction and both cloned iterations"
        );
    }

    #[test]
    fn test_source_loc_preserved_when_replacing_header_branch() {
        let loc = source_loc(97);
        let mut func = make_counting_loop(2);

        let header_branch = *func.block(BlockId(1)).insts.last().unwrap();
        func.inst_mut(header_branch).source_loc = Some(loc);

        let mut pass = LoopUnroll::default();
        assert!(pass.run(&mut func));

        let replacement = func.inst(header_branch);
        assert_eq!(replacement.opcode, AArch64Opcode::B);
        assert_eq!(
            replacement.source_loc,
            Some(loc),
            "loop-unroll must preserve source_loc when replacing the header BCond with B"
        );
    }

    #[test]
    fn test_provenance_records_body_and_branch_clones() {
        let mut func = make_counting_loop(3);
        let body_work = func.block(BlockId(3)).insts[0];
        let latch_branch = *func.block(BlockId(3)).insts.last().unwrap();

        let body_origin = TrustIrInstId(90);
        let branch_origin = TrustIrInstId(91);
        let mut provenance = ProvenanceMap::new();
        provenance.record_lowering(body_origin, &[body_work], PassId::new("isel"));
        provenance.record_lowering(branch_origin, &[latch_branch], PassId::new("isel"));

        let mut pass = LoopUnroll::default();
        assert!(pass.run_with_provenance(&mut func, &mut provenance));

        let body_mappings = provenance.get_mach_insts(body_origin).unwrap();
        assert_eq!(
            body_mappings.len(),
            3,
            "trip-count 3 should retain the original body instruction and add two clones"
        );
        assert_eq!(body_mappings[0], body_work);
        for &clone_id in &body_mappings[1..] {
            let entry = provenance.get_entry(clone_id).unwrap();
            assert_eq!(entry.trust_ir_origins, vec![body_origin]);
            let transform = entry.transforms.last().unwrap();
            assert_eq!(transform.pass, loop_unroll_pass_id());
            assert_eq!(transform.kind, TransformKind::Cloned { source: body_work });
        }

        let branch_mappings = provenance.get_mach_insts(branch_origin).unwrap();
        assert_eq!(
            branch_mappings.len(),
            3,
            "trip-count 3 should retain the rewritten latch branch and add two cloned branch terminators"
        );
        assert_eq!(branch_mappings[0], latch_branch);
        for &clone_id in &branch_mappings[1..] {
            let entry = provenance.get_entry(clone_id).unwrap();
            assert_eq!(entry.trust_ir_origins, vec![branch_origin]);
            let transform = entry.transforms.last().unwrap();
            assert_eq!(transform.pass, loop_unroll_pass_id());
            assert_eq!(
                transform.kind,
                TransformKind::Cloned {
                    source: latch_branch
                }
            );
        }
    }

    #[test]
    fn test_provenance_records_branch_rewrites_and_deleted_compare() {
        let mut func = make_counting_loop(2);
        let cmp = func.block(BlockId(1)).insts[1];
        let header_branch = *func.block(BlockId(1)).insts.last().unwrap();
        let latch_branch = *func.block(BlockId(3)).insts.last().unwrap();

        let cmp_origin = TrustIrInstId(100);
        let header_branch_origin = TrustIrInstId(101);
        let latch_branch_origin = TrustIrInstId(102);
        let mut provenance = ProvenanceMap::new();
        provenance.record_lowering(cmp_origin, &[cmp], PassId::new("isel"));
        provenance.record_lowering(header_branch_origin, &[header_branch], PassId::new("isel"));
        provenance.record_lowering(latch_branch_origin, &[latch_branch], PassId::new("isel"));

        let mut pass = LoopUnroll::default();
        assert!(pass.run_with_provenance(&mut func, &mut provenance));

        let header_entry = provenance.get_entry(header_branch).unwrap();
        assert_eq!(func.inst(header_branch).opcode, AArch64Opcode::B);
        let header_transform = header_entry.transforms.last().unwrap();
        assert_eq!(header_transform.pass, loop_unroll_pass_id());
        assert_eq!(header_transform.kind, TransformKind::Survived);

        let latch_entry = provenance.get_entry(latch_branch).unwrap();
        let latch_transform = latch_entry.transforms.last().unwrap();
        assert_eq!(latch_transform.pass, loop_unroll_pass_id());
        assert_eq!(latch_transform.kind, TransformKind::Survived);

        let cmp_entry = provenance.get_entry(cmp).unwrap();
        assert!(
            cmp_entry.is_optimized_away(),
            "loop-unroll should mark removed trip-count compares optimized away"
        );
        assert_eq!(cmp_entry.trust_ir_origins, vec![cmp_origin]);
        assert!(
            !func.block(BlockId(1)).insts.contains(&cmp),
            "removed compare should leave the header instruction list"
        );
    }

    // -----------------------------------------------------------------------
    // Copy-based (real importer dialect) recognizer tests.
    // -----------------------------------------------------------------------

    fn cc_imm(cc: CondCode) -> MachOperand {
        MachOperand::Imm(cc.encoding() as i64)
    }

    /// Build the real importer's copy-based / rotated counted loop:
    ///
    /// ```text
    ///   bb0 (preheader):
    ///     v0  = Movz #init
    ///     v1  = MovR v0            ; IV init phi-copy
    ///     v11 = Movz #limit        ; LICM-hoisted bound
    ///     B bb1
    ///   bb1 (header):
    ///     v20 = AddRI v1, #10      ; body work reading the IV
    ///     v10 = AddRI v1, #step    ; IV increment (rotated, in header)
    ///     CmpRR v10, v11           ; compare inc vs bound  (a=inc, b=bound)
    ///     CSet  v12, EQ
    ///     CmpRI v12, #0
    ///     BCond [NE, bb2]          ; exit-on-true
    ///     B bb3
    ///   bb2 (exit): Ret
    ///   bb3 (latch):
    ///     v1 = MovR v10            ; IV back-edge phi-copy
    ///     B bb1
    /// ```
    ///
    /// Trip count = (limit - init) / step for the EQ exit.
    fn make_copy_counted_loop(init: i64, step: i64, limit: i64) -> MachFunction {
        let mut func = MachFunction::new("copyloop".to_string(), Signature::new(vec![], vec![]));
        let bb0 = func.entry;
        let bb1 = func.create_block();
        let bb2 = func.create_block();
        let bb3 = func.create_block();

        // preheader
        let i0 = func.push_inst(MachInst::new(AArch64Opcode::Movz, vec![vreg(0), imm(init)]));
        func.append_inst(bb0, i0);
        let i1 = func.push_inst(MachInst::new(AArch64Opcode::MovR, vec![vreg(1), vreg(0)]));
        func.append_inst(bb0, i1);
        let i2 = func.push_inst(MachInst::new(
            AArch64Opcode::Movz,
            vec![vreg(11), imm(limit)],
        ));
        func.append_inst(bb0, i2);
        let b0 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb1)],
        ));
        func.append_inst(bb0, b0);

        // header
        let body = func.push_inst(MachInst::new(
            AArch64Opcode::AddRI,
            vec![vreg(20), vreg(1), imm(10)],
        ));
        func.append_inst(bb1, body);
        let inc = func.push_inst(MachInst::new(
            AArch64Opcode::AddRI,
            vec![vreg(10), vreg(1), imm(step)],
        ));
        func.append_inst(bb1, inc);
        let cmp = func.push_inst(MachInst::new(
            AArch64Opcode::CmpRR,
            vec![vreg(10), vreg(11)],
        ));
        func.append_inst(bb1, cmp);
        let cset = func.push_inst(MachInst::new(
            AArch64Opcode::CSet,
            vec![vreg(12), cc_imm(CondCode::EQ)],
        ));
        func.append_inst(bb1, cset);
        let brc = func.push_inst(MachInst::new(AArch64Opcode::CmpRI, vec![vreg(12), imm(0)]));
        func.append_inst(bb1, brc);
        let bcond = func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![cc_imm(CondCode::NE), MachOperand::Block(bb2)],
        ));
        func.append_inst(bb1, bcond);
        let bf = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb3)],
        ));
        func.append_inst(bb1, bf);

        // exit
        let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb2, ret);

        // latch
        let phicopy = func.push_inst(MachInst::new(AArch64Opcode::MovR, vec![vreg(1), vreg(10)]));
        func.append_inst(bb3, phicopy);
        let b3 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb1)],
        ));
        func.append_inst(bb3, b3);

        func.add_edge(bb0, bb1);
        func.add_edge(bb1, bb2);
        func.add_edge(bb1, bb3);
        func.add_edge(bb3, bb1);
        func
    }

    /// Count the number of `StrRI`/`AddRI`-style body clones by counting the
    /// body work instruction (`AddRI v20, ..., #10`) across the whole function.
    fn count_body_work(func: &MachFunction) -> usize {
        func.block_order
            .iter()
            .flat_map(|&b| func.block(b).insts.iter().copied())
            .filter(|&iid| {
                let inst = func.inst(iid);
                inst.opcode == AArch64Opcode::AddRI
                    && inst.operands.get(2).and_then(|o| o.as_imm()) == Some(10)
            })
            .count()
    }

    #[test]
    fn test_copy_based_recognizes_bcond_b_shape_trip_2_3_4() {
        for (limit, expected) in [(2, 2usize), (3, 3), (4, 4)] {
            let mut func = make_copy_counted_loop(0, 1, limit);
            let mut pass = LoopUnroll::default();
            assert!(
                pass.run(&mut func),
                "trip {expected} copy-loop should unroll"
            );
            // Back edge (latch -> header) must be gone.
            assert!(
                !func.block(BlockId(3)).succs.contains(&BlockId(1)),
                "back-edge should be removed for trip {expected}"
            );
            // Body work should appear once per iteration.
            assert_eq!(
                count_body_work(&func),
                expected,
                "trip {expected} should replicate the body work {expected} times"
            );
        }
    }

    #[test]
    fn test_copy_based_refuses_trip_over_max() {
        // (5-0)/1 = 5 > TCG_MAX_UNROLL_TRIP_COUNT (4).
        let mut func = make_copy_counted_loop(0, 1, 5);
        let before = func.num_blocks();
        let mut pass = LoopUnroll::default();
        assert!(!pass.run(&mut func), "trip 5 must not unroll");
        assert_eq!(func.num_blocks(), before);
        assert!(func.block(BlockId(3)).succs.contains(&BlockId(1)));
    }

    #[test]
    fn test_copy_based_step_2_trip_2() {
        // init 0, step 2, limit 4 -> exit when inc == 4 -> m=2.
        let mut func = make_copy_counted_loop(0, 2, 4);
        let mut pass = LoopUnroll::default();
        assert!(pass.run(&mut func));
        assert_eq!(count_body_work(&func), 2);
    }

    #[test]
    fn test_copy_based_cmpri_immediate_bound() {
        // Replace the CmpRR against v11 with a direct `CmpRI v10, #limit`.
        let mut func = make_copy_counted_loop(0, 1, 3);
        // Rewrite the header compare (index 2) to CmpRI v10, #3.
        let header = BlockId(1);
        let cmp_id = func.block(header).insts[2];
        *func.inst_mut(cmp_id) = MachInst::new(AArch64Opcode::CmpRI, vec![vreg(10), imm(3)]);
        let mut pass = LoopUnroll::default();
        assert!(
            pass.run(&mut func),
            "CmpRI-immediate bound should still unroll"
        );
        assert_eq!(count_body_work(&func), 3);
    }

    /// A copy-loop whose init and bound share a symbolic base (arg copy):
    ///   base = Copy x2 ; init = base+5 ; bound = base+7 ; EQ exit -> D=2 -> trip 2.
    fn make_symbolic_diff_loop() -> MachFunction {
        let mut func = MachFunction::new("symloop".to_string(), Signature::new(vec![], vec![]));
        let bb0 = func.entry;
        let bb1 = func.create_block();
        let bb2 = func.create_block();
        let bb3 = func.create_block();

        // preheader: base=Copy x2 ; v_init=base+5 ; v1=MovR v_init ; v_lim=base+7
        let base = func.push_inst(MachInst::new(
            AArch64Opcode::Copy,
            vec![vreg(2), MachOperand::PReg(PReg::new(2))],
        ));
        func.append_inst(bb0, base);
        let vinit = func.push_inst(MachInst::new(
            AArch64Opcode::AddRI,
            vec![vreg(5), vreg(2), imm(5)],
        ));
        func.append_inst(bb0, vinit);
        let iv0 = func.push_inst(MachInst::new(AArch64Opcode::MovR, vec![vreg(1), vreg(5)]));
        func.append_inst(bb0, iv0);
        let vlim = func.push_inst(MachInst::new(
            AArch64Opcode::AddRI,
            vec![vreg(17), vreg(2), imm(7)],
        ));
        func.append_inst(bb0, vlim);
        let b0 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb1)],
        ));
        func.append_inst(bb0, b0);

        // header
        let body = func.push_inst(MachInst::new(
            AArch64Opcode::AddRI,
            vec![vreg(20), vreg(1), imm(10)],
        ));
        func.append_inst(bb1, body);
        let inc = func.push_inst(MachInst::new(
            AArch64Opcode::AddRI,
            vec![vreg(10), vreg(1), imm(1)],
        ));
        func.append_inst(bb1, inc);
        // compare bound (a) vs inc (b): CmpRR v17, v10.
        let cmp = func.push_inst(MachInst::new(
            AArch64Opcode::CmpRR,
            vec![vreg(17), vreg(10)],
        ));
        func.append_inst(bb1, cmp);
        let cset = func.push_inst(MachInst::new(
            AArch64Opcode::CSet,
            vec![vreg(12), cc_imm(CondCode::EQ)],
        ));
        func.append_inst(bb1, cset);
        let brc = func.push_inst(MachInst::new(AArch64Opcode::CmpRI, vec![vreg(12), imm(0)]));
        func.append_inst(bb1, brc);
        let bcond = func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![cc_imm(CondCode::NE), MachOperand::Block(bb2)],
        ));
        func.append_inst(bb1, bcond);
        let bf = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb3)],
        ));
        func.append_inst(bb1, bf);

        let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb2, ret);

        let phicopy = func.push_inst(MachInst::new(AArch64Opcode::MovR, vec![vreg(1), vreg(10)]));
        func.append_inst(bb3, phicopy);
        let b3 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb1)],
        ));
        func.append_inst(bb3, b3);

        func.add_edge(bb0, bb1);
        func.add_edge(bb1, bb2);
        func.add_edge(bb1, bb3);
        func.add_edge(bb3, bb1);
        func
    }

    #[test]
    fn test_copy_based_symbolic_difference_trip_2() {
        // dry's Proc8 shape: init=base+5, bound=base+7, eq exit -> trip 2.
        let mut func = make_symbolic_diff_loop();
        let mut pass = LoopUnroll::default();
        assert!(
            pass.run(&mut func),
            "symbolic init/bound with constant difference should unroll"
        );
        assert_eq!(count_body_work(&func), 2);
        assert!(!func.block(BlockId(3)).succs.contains(&BlockId(1)));
    }

    #[test]
    fn test_copy_based_symbolic_relational_refused() {
        // Same symbolic loop but a signed-less-than exit (not EQ/NE): the base
        // does not cancel, so the trip count is not statically provable -> refuse.
        let mut func = make_symbolic_diff_loop();
        let header = BlockId(1);
        let cset_id = func.block(header).insts[3];
        *func.inst_mut(cset_id) =
            MachInst::new(AArch64Opcode::CSet, vec![vreg(12), cc_imm(CondCode::LT)]);
        let before = func.num_blocks();
        let mut pass = LoopUnroll::default();
        assert!(
            !pass.run(&mut func),
            "relational exit over a symbolic base must fail closed"
        );
        assert_eq!(func.num_blocks(), before);
    }

    /// Build a floating-point counted loop `d=init; do{...; d+=step}while(!(d>lim))`:
    ///   preheader: vi=FmovImm init; v1=FmovFprFpr vi; vs=FmovImm step; vl=FmovImm lim
    ///   header: v10=FaddRR v1,vs ; Fcmp v10,vl ; CSet v12,HI ; CmpRI v12,#0 ;
    ///           BCond[NE,exit] ; B latch
    ///   latch: v1=FmovFprFpr v10 ; B header
    fn make_fp_counted_loop(init: f64, step: f64, limit: f64) -> MachFunction {
        let mut func = MachFunction::new("fploop".to_string(), Signature::new(vec![], vec![]));
        let f = |id: u32| MachOperand::VReg(VReg::new(id, RegClass::Fpr64));
        let bb0 = func.entry;
        let bb1 = func.create_block();
        let bb2 = func.create_block();
        let bb3 = func.create_block();

        let vi = func.push_inst(MachInst::new(
            AArch64Opcode::FmovImm,
            vec![f(0), MachOperand::FImm(init)],
        ));
        func.append_inst(bb0, vi);
        let v1 = func.push_inst(MachInst::new(AArch64Opcode::FmovFprFpr, vec![f(1), f(0)]));
        func.append_inst(bb0, v1);
        let vs = func.push_inst(MachInst::new(
            AArch64Opcode::FmovImm,
            vec![f(2), MachOperand::FImm(step)],
        ));
        func.append_inst(bb0, vs);
        let vl = func.push_inst(MachInst::new(
            AArch64Opcode::FmovImm,
            vec![f(3), MachOperand::FImm(limit)],
        ));
        func.append_inst(bb0, vl);
        let b0 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb1)],
        ));
        func.append_inst(bb0, b0);

        // header
        let body = func.push_inst(MachInst::new(
            AArch64Opcode::FaddRR,
            vec![f(20), f(1), f(2)],
        ));
        func.append_inst(bb1, body);
        let inc = func.push_inst(MachInst::new(
            AArch64Opcode::FaddRR,
            vec![f(10), f(1), f(2)],
        ));
        func.append_inst(bb1, inc);
        // Fcmp inc(a), limit(b) ; CSet HI (a > b) -> exit when inc > limit.
        let cmp = func.push_inst(MachInst::new(AArch64Opcode::Fcmp, vec![f(10), f(3)]));
        func.append_inst(bb1, cmp);
        let cset = func.push_inst(MachInst::new(
            AArch64Opcode::CSet,
            vec![vreg(12), cc_imm(CondCode::HI)],
        ));
        func.append_inst(bb1, cset);
        let brc = func.push_inst(MachInst::new(AArch64Opcode::CmpRI, vec![vreg(12), imm(0)]));
        func.append_inst(bb1, brc);
        let bcond = func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![cc_imm(CondCode::NE), MachOperand::Block(bb2)],
        ));
        func.append_inst(bb1, bcond);
        let bf = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb3)],
        ));
        func.append_inst(bb1, bf);

        let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb2, ret);

        let phicopy = func.push_inst(MachInst::new(AArch64Opcode::FmovFprFpr, vec![f(1), f(10)]));
        func.append_inst(bb3, phicopy);
        let b3 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb1)],
        ));
        func.append_inst(bb3, b3);

        func.add_edge(bb0, bb1);
        func.add_edge(bb1, bb2);
        func.add_edge(bb1, bb3);
        func.add_edge(bb3, bb1);
        func
    }

    fn count_fp_body(func: &MachFunction) -> usize {
        func.block_order
            .iter()
            .flat_map(|&b| func.block(b).insts.iter().copied())
            .filter(|&iid| {
                let inst = func.inst(iid);
                inst.opcode == AArch64Opcode::FaddRR
                    && inst
                        .operands
                        .first()
                        .and_then(|o| o.as_vreg())
                        .map(|v| v.id)
                        == Some(20)
            })
            .count()
    }

    #[test]
    fn test_fp_iv_exact_8_1_9_trips_2() {
        // d=8; do {...; d+=1} while (!(d>9)) -> body runs for d=8,9 -> 2 trips.
        let mut func = make_fp_counted_loop(8.0, 1.0, 9.0);
        let mut pass = LoopUnroll::default();
        assert!(
            pass.run(&mut func),
            "exact FP-IV 8/1/9 should unroll to trip 2"
        );
        assert_eq!(count_fp_body(&func), 2);
        assert!(!func.block(BlockId(3)).succs.contains(&BlockId(1)));
    }

    #[test]
    fn test_fp_iv_inexact_step_refused() {
        // step 0.1 is not an exactly-representable integer -> refuse.
        let mut func = make_fp_counted_loop(0.0, 0.1, 1.0);
        let before = func.num_blocks();
        let mut pass = LoopUnroll::default();
        assert!(!pass.run(&mut func), "inexact FP step must fail closed");
        assert_eq!(func.num_blocks(), before);
        assert!(func.block(BlockId(3)).succs.contains(&BlockId(1)));
    }

    #[test]
    fn test_fp_iv_inexact_limit_refused() {
        // A non-integer bound (9.5) is refused even with an integer step.
        let mut func = make_fp_counted_loop(8.0, 1.0, 9.5);
        let mut pass = LoopUnroll::default();
        assert!(
            !pass.run(&mut func),
            "non-integer FP bound must fail closed"
        );
    }

    #[test]
    fn test_copy_based_does_not_disturb_legacy_phi_shape() {
        // The legacy synthetic Phi/CmpRI loop still unrolls via the fallback.
        let mut func = make_counting_loop(2);
        let mut pass = LoopUnroll::default();
        assert!(pass.run(&mut func));
        assert!(!func.block(BlockId(3)).succs.contains(&BlockId(1)));
    }

    /// Copy-counted trip-`limit` loop whose body loads `base[iv*4]` through
    /// the importer's `Madd` indexed-array dialect. With `slot_based`, the
    /// base is a stack-slot address root (const-addr unroll eligible).
    fn make_const_addr_madd_loop(limit: i64, slot_based: bool) -> MachFunction {
        use trust_cg_ir::{StackSlot, regs::SP};
        let mut func = MachFunction::new("caloop".to_string(), Signature::new(vec![], vec![]));
        let bb0 = func.entry;
        let bb1 = func.create_block(); // header
        let bb2 = func.create_block(); // exit
        let bb3 = func.create_block(); // latch
        func.next_vreg = 100;

        // preheader: base, k=4, iv init 0, bound.
        let base_def = if slot_based {
            let slot = func.alloc_stack_slot(StackSlot::new(64, 4));
            MachInst::new(
                AArch64Opcode::AddPCRel,
                vec![vreg(3), MachOperand::PReg(SP), MachOperand::StackSlot(slot)],
            )
        } else {
            MachInst::new(
                AArch64Opcode::Copy,
                vec![vreg(3), MachOperand::PReg(trust_cg_ir::regs::X0)],
            )
        };
        let i = func.push_inst(base_def);
        func.append_inst(bb0, i);
        for inst in [
            MachInst::new(AArch64Opcode::Movz, vec![vreg(14), imm(4)]),
            MachInst::new(AArch64Opcode::Movz, vec![vreg(0), imm(0)]),
            MachInst::new(AArch64Opcode::MovR, vec![vreg(1), vreg(0)]),
            MachInst::new(AArch64Opcode::Movz, vec![vreg(11), imm(limit)]),
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(bb1)]),
        ] {
            let id = func.push_inst(inst);
            func.append_inst(bb0, id);
        }

        // header: addr = Madd(iv, k, base); load; inc; exit test.
        for inst in [
            MachInst::new(
                AArch64Opcode::Madd,
                vec![vreg(33), vreg(1), vreg(14), vreg(3)],
            ),
            MachInst::new(
                AArch64Opcode::LdrRI,
                vec![vreg_class(34, RegClass::Gpr32), vreg(33), imm(0)],
            ),
            MachInst::new(AArch64Opcode::AddRI, vec![vreg(10), vreg(1), imm(1)]),
            MachInst::new(AArch64Opcode::CmpRR, vec![vreg(10), vreg(11)]),
            MachInst::new(AArch64Opcode::CSet, vec![vreg(12), cc_imm(CondCode::EQ)]),
            MachInst::new(AArch64Opcode::CmpRI, vec![vreg(12), imm(0)]),
            MachInst::new(
                AArch64Opcode::BCond,
                vec![cc_imm(CondCode::NE), MachOperand::Block(bb2)],
            ),
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(bb3)]),
        ] {
            let id = func.push_inst(inst);
            func.append_inst(bb1, id);
        }

        // exit
        let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb2, ret);

        // latch
        for inst in [
            MachInst::new(AArch64Opcode::MovR, vec![vreg(1), vreg(10)]),
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(bb1)]),
        ] {
            let id = func.push_inst(inst);
            func.append_inst(bb3, id);
        }

        func.add_edge(bb0, bb1);
        func.add_edge(bb1, bb2);
        func.add_edge(bb1, bb3);
        func.add_edge(bb3, bb1);
        func
    }

    #[test]
    fn test_const_addr_unroll_trip_16_slot_madd() {
        let mut func = make_const_addr_madd_loop(16, true);
        let mut pass = LoopUnroll::default();
        assert!(pass.run(&mut func), "trip-16 slot-Madd loop should unroll");
        // Back edge gone.
        assert!(!func.block(BlockId(3)).succs.contains(&BlockId(1)));

        // No Madd remains; 16 constant-offset AddRIs (base v3) at 0,4,...,60.
        let mut offsets: Vec<i64> = Vec::new();
        let mut madds = 0;
        for &b in &func.block_order {
            for &iid in &func.block(b).insts {
                let inst = func.inst(iid);
                if inst.opcode == AArch64Opcode::Madd {
                    madds += 1;
                }
                if inst.opcode == AArch64Opcode::AddRI && inst.operands.get(1) == Some(&vreg(3)) {
                    offsets.push(inst.operands[2].as_imm().unwrap());
                }
            }
        }
        assert_eq!(madds, 0, "every Madd must be rewritten");
        offsets.sort_unstable();
        assert_eq!(offsets, (0..16).map(|m| m * 4).collect::<Vec<i64>>());

        // Each rewritten address vreg is single-def (fresh per clone): the
        // SROA tracer's requirement.
        let mut def_counts: HashMap<VReg, usize> = HashMap::new();
        for &b in &func.block_order {
            for &iid in &func.block(b).insts {
                let inst = func.inst(iid);
                if inst.opcode == AArch64Opcode::AddRI
                    && inst.operands.get(1) == Some(&vreg(3))
                    && let Some(MachOperand::VReg(d)) = inst.operands.first()
                {
                    *def_counts.entry(*d).or_default() += 1;
                }
            }
        }
        assert!(def_counts.values().all(|&c| c == 1));

        // The IV increment chain is materialized: header inc became Movz #1.
        let header_movz = func
            .block(BlockId(1))
            .insts
            .iter()
            .map(|&iid| func.inst(iid))
            .any(|inst| {
                inst.opcode == AArch64Opcode::Movz
                    && inst.operands.first() == Some(&vreg(10))
                    && inst.operands.get(1) == Some(&imm(1))
            });
        assert!(header_movz, "header IV inc must become Movz #1");
    }

    #[test]
    fn test_const_addr_unroll_requires_slot_base() {
        // Same shape but the Madd base is a plain pointer argument: the
        // targeted trip-count raise must NOT fire (status quo: no unroll).
        let mut func = make_const_addr_madd_loop(16, false);
        let mut pass = LoopUnroll::default();
        assert!(!pass.run(&mut func), "non-slot base must not raise the cap");
        assert!(func.block(BlockId(3)).succs.contains(&BlockId(1)));
    }

    #[test]
    fn test_const_addr_unroll_trip_17_refused() {
        // One above CONST_ADDR_UNROLL_MAX_TRIP: fail closed.
        let mut func = make_const_addr_madd_loop(17, true);
        let mut pass = LoopUnroll::default();
        assert!(!pass.run(&mut func), "trip 17 exceeds the const-addr cap");
        assert!(func.block(BlockId(3)).succs.contains(&BlockId(1)));
    }

    #[test]
    fn test_const_addr_unroll_small_trip_keeps_verbatim_path() {
        // Trip <= TCG_MAX_UNROLL_TRIP_COUNT takes the existing verbatim
        // unroll (Madds cloned as-is, no constant rewrite).
        let mut func = make_const_addr_madd_loop(3, true);
        let mut pass = LoopUnroll::default();
        assert!(pass.run(&mut func));
        let madds = func
            .block_order
            .iter()
            .flat_map(|&b| func.block(b).insts.iter())
            .filter(|&&iid| func.inst(iid).opcode == AArch64Opcode::Madd)
            .count();
        assert_eq!(madds, 3, "small trips keep the verbatim clone path");
    }

    /// Build the ReedSolomon-shaped diamond-body constant-trip loop:
    ///
    /// ```text
    ///   bb0 (preheader): v0=Movz #init ; v1=MovR v0 (iv) ; v2=Movz #4 ;
    ///                    v20=Copy x0 (base) ; B bb1
    ///   bb1 (header):    v4=Madd v1,v2,v20 ; v5=LdrRI [v4] ;
    ///                    CmpRI v5,#1 ; BCond[EQ]->bb2 ; B bb3
    ///   bb2 (arm A):     v7=MovR v5 ; B bb4
    ///   bb3 (arm B):     v7=Movz #9 ; B bb4
    ///   bb4 (T):         v8=Madd v1,v2,v20 ; StrRI v7,[v8] ;
    ///                    v9=SubRI v1,#1 ;
    ///                    pre_inc:  CmpRI v1,#1 ; CSet v10,HI ;
    ///                              CmpRI v10,#0 ; BCond[NE]->bb5 ; B bb6
    ///                    post_inc: CmpRI v9,#0 ; CSet v10,EQ ;
    ///                              CmpRI v10,#0 ; BCond[NE]->bb6 ; B bb5
    ///   bb5 (latch):     v1=MovR v9 ; B bb1
    ///   bb6 (exit):      Ret
    /// ```
    ///
    /// With `init = 15`: j runs 15..1 (15 iterations) in both compare forms.
    fn make_diamond_const_trip_loop(init: i64, pre_inc: bool) -> MachFunction {
        let mut func =
            MachFunction::new("diamond_loop".to_string(), Signature::new(vec![], vec![]));
        let bb0 = func.entry;
        let bb1 = func.create_block(); // header
        let bb2 = func.create_block(); // arm A
        let bb3 = func.create_block(); // arm B
        let bb4 = func.create_block(); // T (join + exit test)
        let bb5 = func.create_block(); // latch
        let bb6 = func.create_block(); // exit

        let push = |func: &mut MachFunction, blk, op, ops: Vec<MachOperand>| {
            let id = func.push_inst(MachInst::new(op, ops));
            func.append_inst(blk, id);
        };
        let w = |id: u32| vreg_class(id, RegClass::Gpr32);

        // preheader
        push(
            &mut func,
            bb0,
            AArch64Opcode::Movz,
            vec![vreg(0), imm(init)],
        );
        push(&mut func, bb0, AArch64Opcode::MovR, vec![vreg(1), vreg(0)]);
        push(&mut func, bb0, AArch64Opcode::Movz, vec![vreg(2), imm(4)]);
        push(
            &mut func,
            bb0,
            AArch64Opcode::Copy,
            vec![vreg(20), MachOperand::PReg(PReg::new(0))],
        );
        push(
            &mut func,
            bb0,
            AArch64Opcode::B,
            vec![MachOperand::Block(bb1)],
        );
        // header: load a[j], diamond branch on it
        push(
            &mut func,
            bb1,
            AArch64Opcode::Madd,
            vec![vreg(4), vreg(1), vreg(2), vreg(20)],
        );
        push(
            &mut func,
            bb1,
            AArch64Opcode::LdrRI,
            vec![w(5), vreg(4), imm(0)],
        );
        push(&mut func, bb1, AArch64Opcode::CmpRI, vec![w(5), imm(1)]);
        push(
            &mut func,
            bb1,
            AArch64Opcode::BCond,
            vec![imm(0), MachOperand::Block(bb2)], // EQ
        );
        push(
            &mut func,
            bb1,
            AArch64Opcode::B,
            vec![MachOperand::Block(bb3)],
        );
        // arm A
        push(&mut func, bb2, AArch64Opcode::MovR, vec![w(7), w(5)]);
        push(
            &mut func,
            bb2,
            AArch64Opcode::B,
            vec![MachOperand::Block(bb4)],
        );
        // arm B
        push(&mut func, bb3, AArch64Opcode::Movz, vec![w(7), imm(9)]);
        push(
            &mut func,
            bb3,
            AArch64Opcode::B,
            vec![MachOperand::Block(bb4)],
        );
        // T: store a[j], increment, trip test
        push(
            &mut func,
            bb4,
            AArch64Opcode::Madd,
            vec![vreg(8), vreg(1), vreg(2), vreg(20)],
        );
        push(
            &mut func,
            bb4,
            AArch64Opcode::StrRI,
            vec![w(7), vreg(8), imm(0)],
        );
        push(
            &mut func,
            bb4,
            AArch64Opcode::SubRI,
            vec![vreg(9), vreg(1), imm(1)],
        );
        if pre_inc {
            // continue while j >u 1 (compares the OLD iv, ReedSolomon's shape)
            push(&mut func, bb4, AArch64Opcode::CmpRI, vec![vreg(1), imm(1)]);
            push(&mut func, bb4, AArch64Opcode::CSet, vec![vreg(10), imm(8)]); // HI
            push(&mut func, bb4, AArch64Opcode::CmpRI, vec![vreg(10), imm(0)]);
            push(
                &mut func,
                bb4,
                AArch64Opcode::BCond,
                vec![imm(1), MachOperand::Block(bb5)], // NE -> latch
            );
            push(
                &mut func,
                bb4,
                AArch64Opcode::B,
                vec![MachOperand::Block(bb6)],
            );
        } else {
            // exit when j-1 == 0 (compares the incremented iv)
            push(&mut func, bb4, AArch64Opcode::CmpRI, vec![vreg(9), imm(0)]);
            push(&mut func, bb4, AArch64Opcode::CSet, vec![vreg(10), imm(0)]); // EQ
            push(&mut func, bb4, AArch64Opcode::CmpRI, vec![vreg(10), imm(0)]);
            push(
                &mut func,
                bb4,
                AArch64Opcode::BCond,
                vec![imm(1), MachOperand::Block(bb6)], // NE -> exit
            );
            push(
                &mut func,
                bb4,
                AArch64Opcode::B,
                vec![MachOperand::Block(bb5)],
            );
        }
        // latch
        push(&mut func, bb5, AArch64Opcode::MovR, vec![vreg(1), vreg(9)]);
        push(
            &mut func,
            bb5,
            AArch64Opcode::B,
            vec![MachOperand::Block(bb1)],
        );
        // exit
        push(&mut func, bb6, AArch64Opcode::Ret, vec![]);

        func.add_edge(bb0, bb1);
        func.add_edge(bb1, bb2);
        func.add_edge(bb1, bb3);
        func.add_edge(bb2, bb4);
        func.add_edge(bb3, bb4);
        func.add_edge(bb4, bb5);
        func.add_edge(bb4, bb6);
        func.add_edge(bb5, bb1);
        // Hand-numbered vregs above: keep `alloc_vreg` (per-clone renaming)
        // from colliding with them.
        func.next_vreg = 100;
        func
    }

    /// Collect (offset) of every StrRI in the function, and count Madds.
    fn diamond_strs_and_madds(func: &MachFunction) -> (Vec<i64>, usize) {
        let mut strs = Vec::new();
        let mut madds = 0;
        for &blk in &func.block_order {
            for &iid in &func.block(blk).insts {
                let inst = func.inst(iid);
                match inst.opcode {
                    AArch64Opcode::StrRI => {
                        strs.push(inst.operands.get(2).and_then(|o| o.as_imm()).unwrap_or(-1));
                    }
                    AArch64Opcode::Madd => madds += 1,
                    _ => {}
                }
            }
        }
        (strs, madds)
    }

    #[test]
    fn test_diamond_const_trip_unroll_fires_pre_increment_compare() {
        // ReedSolomon's shape: 15 trips, diamond body, exit test on the OLD iv.
        let mut func = make_diamond_const_trip_loop(15, true);
        let mut pass = LoopUnroll::default();
        assert!(pass.run(&mut func), "diamond loop should fully unroll");

        // Back edge gone.
        assert!(!func.block(BlockId(5)).succs.contains(&BlockId(1)));
        assert!(!func.block(BlockId(1)).preds.contains(&BlockId(5)));

        // 15 stores, every address folded to an immediate offset 4*j for
        // j = 15..1, and no Madd survives.
        let (mut strs, madds) = diamond_strs_and_madds(&func);
        assert_eq!(madds, 0, "all IV-indexed Madd addresses must fold");
        strs.sort_unstable();
        let expected: Vec<i64> = (1..=15).map(|j| 4 * j).collect();
        assert_eq!(strs, expected, "per-iteration constant store offsets");

        // The trip-test CSet is dropped from every iteration.
        let csets = func
            .block_order
            .iter()
            .flat_map(|&b| func.block(b).insts.iter())
            .filter(|&&iid| func.inst(iid).opcode == AArch64Opcode::CSet)
            .count();
        assert_eq!(csets, 0, "the compile-time trip test must be dropped");
    }

    #[test]
    fn test_diamond_const_trip_unroll_fires_post_increment_compare() {
        let mut func = make_diamond_const_trip_loop(15, false);
        let mut pass = LoopUnroll::default();
        assert!(pass.run(&mut func), "post-inc compare form should unroll");
        assert!(!func.block(BlockId(5)).succs.contains(&BlockId(1)));
        let (mut strs, madds) = diamond_strs_and_madds(&func);
        assert_eq!(madds, 0);
        strs.sort_unstable();
        let expected: Vec<i64> = (1..=15).map(|j| 4 * j).collect();
        assert_eq!(strs, expected);
    }

    #[test]
    fn test_diamond_const_trip_unroll_renames_clone_locals() {
        // Per-clone renaming restores single-def form for safe body vregs:
        // the header load's dst (v5) must appear as 15 distinct single-def
        // vregs, while the diamond-merged v7 (defined in BOTH arms — not
        // dominated at its use) keeps its original multi-def name.
        let mut func = make_diamond_const_trip_loop(15, true);
        let mut pass = LoopUnroll::default();
        assert!(pass.run(&mut func));
        let mut ldr_dst_defs: HashMap<VReg, usize> = HashMap::new();
        let mut v7_defs = 0usize;
        for &blk in &func.block_order {
            for &iid in &func.block(blk).insts {
                let inst = func.inst(iid);
                if inst.opcode == AArch64Opcode::LdrRI
                    && let Some(d) = inst.operands.first().and_then(|o| o.as_vreg())
                {
                    *ldr_dst_defs.entry(d).or_default() += 1;
                }
                if inst_produces_value(inst)
                    && inst.operands.first().and_then(|o| o.as_vreg())
                        == Some(VReg::new(7, RegClass::Gpr32))
                {
                    v7_defs += 1;
                }
            }
        }
        assert_eq!(ldr_dst_defs.len(), 15, "one fresh load dst per clone");
        assert!(
            ldr_dst_defs.values().all(|&c| c == 1),
            "every clone load dst is single-def"
        );
        assert_eq!(
            v7_defs, 30,
            "the arm-merged vreg keeps its (multi-def) name in all 15 clones"
        );
    }

    #[test]
    fn test_diamond_const_trip_refuses_third_iv_def() {
        // A conditional IV re-assignment inside an arm breaks the
        // `init + m*step` value proof: fail closed.
        let mut func = make_diamond_const_trip_loop(15, true);
        let extra = func.push_inst(MachInst::new(AArch64Opcode::MovR, vec![vreg(1), vreg(5)]));
        let arm_a = BlockId(2);
        let pos = func.block(arm_a).insts.len() - 1;
        func.block_mut(arm_a).insts.insert(pos, extra);
        let mut pass = LoopUnroll::default();
        assert!(!pass.run(&mut func), "third IV def must fail closed");
        assert!(func.block(BlockId(5)).succs.contains(&BlockId(1)));
    }

    #[test]
    fn test_diamond_const_trip_refuses_call_in_body() {
        let mut func = make_diamond_const_trip_loop(15, true);
        let call = func.push_inst(MachInst::new(
            AArch64Opcode::Bl,
            vec![MachOperand::Symbol("helper".to_string())],
        ));
        let arm_b = BlockId(3);
        let pos = func.block(arm_b).insts.len() - 1;
        func.block_mut(arm_b).insts.insert(pos, call);
        let mut pass = LoopUnroll::default();
        assert!(!pass.run(&mut func), "calls in the body must fail closed");
        assert!(func.block(BlockId(5)).succs.contains(&BlockId(1)));
    }

    #[test]
    fn test_diamond_const_trip_refuses_symbolic_init() {
        // Init from an opaque register (not a compile-time constant).
        let mut func = make_diamond_const_trip_loop(15, true);
        let init_id = func.block(BlockId(0)).insts[0];
        *func.inst_mut(init_id) = MachInst::new(
            AArch64Opcode::Copy,
            vec![vreg(0), MachOperand::PReg(PReg::new(1))],
        );
        let mut pass = LoopUnroll::default();
        assert!(!pass.run(&mut func), "symbolic init must fail closed");
        assert!(func.block(BlockId(5)).succs.contains(&BlockId(1)));
    }

    #[test]
    fn test_diamond_const_trip_refuses_trip_over_cap() {
        // 17 trips exceeds DIAMOND_UNROLL_MAX_TRIP (16): fail closed.
        let mut func = make_diamond_const_trip_loop(17, true);
        let mut pass = LoopUnroll::default();
        assert!(!pass.run(&mut func), "trip 17 exceeds the diamond cap");
        assert!(func.block(BlockId(5)).succs.contains(&BlockId(1)));
    }

    #[test]
    fn test_diamond_const_trip_refuses_vcond_reuse() {
        // The trip-test boolean must have no reader beyond its own branch
        // compare (the whole tail is dropped).
        let mut func = make_diamond_const_trip_loop(15, true);
        let use_id = func.push_inst(MachInst::new(
            AArch64Opcode::AddRR,
            vec![vreg(21), vreg(10), vreg(9)],
        ));
        let exit = BlockId(6);
        func.block_mut(exit).insts.insert(0, use_id);
        let mut pass = LoopUnroll::default();
        assert!(!pass.run(&mut func), "vcond reuse must fail closed");
        assert!(func.block(BlockId(5)).succs.contains(&BlockId(1)));
    }
}
