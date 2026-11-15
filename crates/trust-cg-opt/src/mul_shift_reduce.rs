// trust-cg-opt - Multiply-by-small-constant -> shift/add-sub strength reduction (aarch64)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Rewrites an integer multiply — a `MulRR`, or the multiply half of a `Madd`
//! multiply-accumulate — BY A SMALL COMPILE-TIME CONSTANT into a short
//! shift + add/sub sequence, off the hardware `MUL`/`MADD` critical path.
//!
//! The pass also carries the closely-related unsigned widening-multiply
//! combine:
//!
//! ```text
//!   ta = AndRI(a, 0xffff_ffff)
//!   tb = AndRI(b, 0xffff_ffff)
//!   d  = MulRR(ta, tb)
//!   =>
//!   d  = Umull(a, b)
//! ```
//!
//! `UMULL Xd, Wn, Wm` reads exactly the low 32 bits of each source and returns
//! their full 64-bit product, so this is the exact identity
//! `(a & (2^32-1)) * (b & (2^32-1)) = zext32(a) * zext32(b)`.  The product is
//! at most `(2^32-1)^2 < 2^64`, so the rewrite also preserves the absence of
//! unsigned overflow established by the source masks.  Both AND results must
//! be function-wide single-use, same-block reaching definitions, with neither
//! unmasked source redefined before the multiply.  Every uncertain shape is
//! left unchanged.
//!
//! # Why
//!
//! `MUL`/`MADD` are latency-3-4 on Apple cores. When the multiply sits on a
//! LOOP-CARRIED dependence (p2_collatz's odd step `c = c*3 + 1`, which isel
//! fuses to a single `MADD c, #3, #1`), that latency is the loop's speed limit.
//! LLVM instead emits `add x, c, c, lsl #1` — a 1-cycle shifted add — plus the
//! `+1`, shortening the carried path. This pass reproduces that win using only
//! the already-gate-credited `LslRI` / `AddRR` / `SubRR` opcodes (there is no
//! shifted-register ADD opcode in this backend; the ROR-shifted `EorRRShift` is
//! the only shifted-register ALU form, and it is EOR-only). A shift feeding an
//! add is 2 machine instructions but ≤ 2 cycles of latency versus the madd's
//! 3-4, and — because the shifts of `x` are independent and the addend folds in
//! parallel — the carried path is 2 cycles for the `2^k+1` shape.
//!
//! # What fires
//!
//! The signed constant `c` (sign-extended to the operation width) must be a
//! single positive power of two `2^a`, or a **one-shift** two-term form
//! `s_a·2^a + s_b·2^0` with `a > 0` and sign combination in `{(+,+), (+,-),
//! (-,+)}` — i.e. `2^a + 1`, `2^a - 1`, `1 - 2^a`. That covers `2,3,4,5,7,8,9,
//! 15,16,17,…` and negatives like `-3 = 1 - 4`, `-7 = 1 - 8`. It emits AT MOST
//! ONE `LslRI` plus one add/sub, so it is never a throughput regression.
//!
//! Deliberately BAILED (kept as the original multiply):
//!   * **Two-shift forms** — both powers ≥ 2, e.g. `6 = 4+2`, `10 = 8+2`,
//!     `24 = 16+8`. These would need two shifts + an add (3 ALU ops for one
//!     MUL); the only payoff is a latency edge for latency-bound chains, while a
//!     THROUGHPUT-bound loop (matmul's `i*24` index math) measurably regresses.
//!     Bailing keeps the pass strictly throughput-safe.
//!   * **≥3-term constants** — `11 = 8+2+1`, `13 = 8+4+1`, large primes.
//!   * `(-,-)` (e.g. `-6 = -(4+2)`) — needs a leading negate, no positive term
//!     to seed the accumulator.
//!
//! # Soundness
//!
//! Pure ring identity over Z/2^W (wrapping): `x·(s_a·2^a + s_b·2^b) ≡
//! (x<<a)·s_a + (x<<b)·s_b (mod 2^W)`, bit-exact for `wrapping_mul`; the addend
//! of a `Madd` is summed in verbatim. No overflow concern (wrapping). The
//! constant is resolved by [`unique_reaching_const`] — a sound reaching-defs
//! query that returns `Some` ONLY when exactly one `Movz`(+`Movk`)
//! materialization reaches the use — so a non-constant, ambiguous, or
//! loop-redefined multiplier resolves to `None` and BAILS. Every unproven
//! precondition (non-GPR class, mismatched widths, out-of-range shift, ≥3 term
//! constant) bails to the unchanged `MulRR`/`Madd`.
//!
//! Emits ONLY `LslRI`/`AddRR`/`SubRR` — opcodes already emitted throughout isel
//! and gate-covered — so there is NO new emittable surface and no gate impact.
//!
//! # Kill switches
//!
//! Compile-time: set `TCG_NO_MUL_SHIFT_REDUCE` (any value) — [`run`] becomes a
//! no-op. Per-pass bisect: `TRUST_CG_DISABLE_PASSES=mulshift`.
//! The widening combine alone can be disabled with
//! `TCG_NO_MASKED_UMULL_FUSE` (the constant strength reduction keeps running).
//!
//! [`run`]: MachinePass::run

use crate::fast_hash::FxHashMap as HashMap;

use trust_cg_ir::{
    AArch64Opcode, BlockId, InstId, MachFunction, MachInst, MachOperand, PassId, ProvenanceMap,
    RegClass, SourceLoc, VReg,
};

use crate::pass_manager::MachinePass;
use crate::reaching_const::{ReachingCtx, unique_reaching_const_with};

/// Multiply-by-small-constant -> shift/add-sub strength reduction pass.
pub struct MulShiftReduce;

/// Compile-time kill switch: set `TCG_NO_MUL_SHIFT_REDUCE` (any value) to
/// disable the pass entirely.
fn pass_enabled() -> bool {
    std::env::var_os("TCG_NO_MUL_SHIFT_REDUCE").is_none()
}

impl MachinePass for MulShiftReduce {
    fn name(&self) -> &str {
        "mul-shift-reduce"
    }

    fn run(&mut self, func: &mut MachFunction) -> bool {
        if !pass_enabled() {
            return false;
        }
        run_mul_shift_reduce(func, None)
    }

    fn run_with_provenance(
        &mut self,
        func: &mut MachFunction,
        provenance: &mut ProvenanceMap,
    ) -> bool {
        if !pass_enabled() {
            return false;
        }
        run_mul_shift_reduce(func, Some(provenance))
    }

    fn run_with_analyses_and_provenance(
        &mut self,
        func: &mut MachFunction,
        _analyses: &mut crate::pass_manager::AnalysisCache,
        provenance: &mut ProvenanceMap,
    ) -> bool {
        if !pass_enabled() {
            return false;
        }
        run_mul_shift_reduce(func, Some(provenance))
    }
}

fn pass_id() -> PassId {
    PassId::new("mul-shift-reduce")
}

fn masked_umull_pass_id() -> PassId {
    PassId::new("masked-umull-fuse")
}

/// Narrow rollback lever for the `AND #0xffff_ffff` + `MUL` -> `UMULL`
/// combine.  Use the shared environment accessor so tests can override it
/// without racing the process environment.
fn masked_umull_enabled() -> bool {
    crate::env_lock::var_os("TCG_NO_MASKED_UMULL_FUSE").is_none()
}

/// A single signed power-of-two term of the multiplier decomposition:
/// `positive ? +(x<<shift) : -(x<<shift)`. `shift == 0` means the plain `x`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Term {
    positive: bool,
    shift: u32,
}

/// A validated, infallible-to-materialize rewrite of one `MulRR`/`Madd`.
#[derive(Clone, Debug)]
struct Plan {
    /// The multiplicand register `x` (the non-constant multiply operand).
    x: VReg,
    /// The `Madd` addend register `y` (result is `y + x*c`); `None` for `MulRR`.
    addend: Option<VReg>,
    /// The original result register the final emitted instruction must define.
    dst: VReg,
    /// GPR class (`Gpr32`/`Gpr64`) shared by `x`, `addend`, `dst`, all temps.
    class: RegClass,
    /// The `x*c` decomposition (1 or 2 signed power-of-two terms).
    terms: Vec<Term>,
    /// Source location copied onto the emitted instructions.
    source_loc: Option<SourceLoc>,
}

/// Inclusive magnitude ceiling on a resolvable multiplier — keeps the pass to
/// genuinely SMALL constants (the strength-reduction never fires on large
/// multipliers even when they happen to be 2-term). Well past every realistic
/// small-constant multiply; the ≤2-term structure is the real gate.
const MAX_ABS_CONST: i128 = 1 << 20;

impl MulShiftReduce {
    /// Run the pass directly on a function (tests / standalone use).
    pub fn run_on_function(&mut self, func: &mut MachFunction) -> bool {
        <Self as MachinePass>::run(self, func)
    }
}

/// One block's instruction list and the plans recognized in it.
type BlockPlans = (BlockId, Vec<InstId>, Vec<(InstId, Plan)>);

fn run_mul_shift_reduce(
    func: &mut MachFunction,
    mut provenance: Option<&mut ProvenanceMap>,
) -> bool {
    // PREFILTER (exact): the rewrite sites are `MulRR` / `Madd` by a constant. Without one in the live block lists the pass cannot
    // change anything, so skip the per-block scan. Over-approximating
    // presence is safe; the check is a single opcode sweep.
    if !(func
        .block_order
        .iter()
        .flat_map(|b| func.block(*b).insts.iter())
        .any(|&i| func.inst(i).opcode == AArch64Opcode::MulRR)
        || func
            .block_order
            .iter()
            .flat_map(|b| func.block(*b).insts.iter())
            .any(|&i| func.inst(i).opcode == AArch64Opcode::Madd))
    {
        return false;
    }
    let mut changed = false;
    // Phase A recognizes candidates for the whole function before any mutation,
    // so one lazy reaching-definitions context serves all queries. Phase B/C
    // invalidate that snapshot, but never query it again. Interleaving rewrites
    // with recognition would require rebuilding it or using one-shot scans.
    //
    // Recognition is unaffected by hoisting it ahead of every rewrite. Phase B
    // materializes a shift/add sequence and Phase C splices the multiply out;
    // neither removes the MOVZ/MOVK that defines a multiplier constant, and the
    // only vreg a rewrite defines is the multiply's own `dst`, whose defining
    // opcode is not a move-wide either before (Mul/Madd) or after (Add/Lsl).
    // `unique_reaching_const` therefore returns the same verdict for every query
    // whether it runs before or after the earlier blocks were rewritten.
    // The reaching-defs context is built only if a candidate survives the
    // structural prefilter in `plan_for` (most no-change runs never need it);
    // the move-wide census that feeds the prefilter is one linear scan.
    let ctx: std::cell::OnceCell<ReachingCtx> = std::cell::OnceCell::new();
    let mw = MoveWideCensus::build(func);

    // Phase A (immutable, whole function): recognize every rewritable multiply
    // against the UNMUTATED function, building a fully-validated Plan for each.
    let mut recognized: Vec<BlockPlans> = Vec::new();
    for block_id in func.block_order.clone() {
        let block_insts = func.block(block_id).insts.clone();
        let mut plans: Vec<(InstId, Plan)> = Vec::new();
        for &inst_id in &block_insts {
            if let Some(plan) = analyze(func, &ctx, &mw, inst_id) {
                plans.push((inst_id, plan));
            }
        }
        if !plans.is_empty() {
            recognized.push((block_id, block_insts, plans));
        }
    }

    // Materialization moves ProvenanceMap history before the splices commit.
    // Require one actual reference in ALL blocks, including blocks omitted
    // from layout, before any such mutation. Saturating at two suffices for
    // uniqueness and keeps arbitrary duplicate reference counts bounded.
    // Repeated layout entries must not materialize the same site twice either.
    if !recognized.is_empty() {
        let mut owners: HashMap<InstId, (u8, u8)> = HashMap::default();
        for (_, _, plans) in &recognized {
            for (id, _) in plans {
                let (planned, _) = owners.entry(*id).or_default();
                *planned = planned.saturating_add(1).min(2);
            }
        }
        for block in &func.blocks {
            for id in &block.insts {
                if let Some((_, references)) = owners.get_mut(id) {
                    *references = references.saturating_add(1).min(2);
                }
            }
        }
        for (_, _, plans) in &mut recognized {
            plans.retain(|(id, _)| owners.get(id) == Some(&(1, 1)));
        }
        recognized.retain(|(_, _, plans)| !plans.is_empty());
    }

    let mut consumed = Vec::new();
    for (block_id, block_insts, plans) in recognized {
        // Phase B (mutable): materialize each plan into fresh instructions.
        let mut replacements: HashMap<InstId, Vec<InstId>> = HashMap::default();
        for (inst_id, plan) in plans {
            let new_ids = materialize(func, &plan, inst_id, provenance.as_deref_mut());
            replacements.insert(inst_id, new_ids);
            changed = true;
        }

        // Phase C: splice each rewritten multiply's InstId out for its sequence.
        // Collect only actual replacement keys. The original arena payload is
        // retired after EVERY splice, and only when no block still links it.
        let new_insts: Vec<InstId> = block_insts
            .iter()
            .flat_map(|iid| match replacements.get(iid) {
                Some(seq) => seq.clone(),
                None => vec![*iid],
            })
            .collect();
        func.block_mut(block_id).insts = new_insts;
        consumed.extend(replacements.keys().copied());
    }
    crate::retirement::retire_unlinked(func, &consumed);

    // Run the independent low-word widening combine only after every
    // constant-multiply candidate has been recognized and materialized.  This
    // preserves Phase A's invariant that its indexes observe the original
    // function, while still folding any untouched masked `MulRR` sites.
    if masked_umull_enabled() {
        changed |= run_masked_umull_fuse(func, provenance);
    }
    changed
}

// ---------------------------------------------------------------------------
// `(x & 0xffff_ffff) * (y & 0xffff_ffff)` -> `UMULL x, y`
// ---------------------------------------------------------------------------

const LOW_WORD_MASK: i64 = 0xffff_ffff;

#[derive(Clone, Copy)]
struct MaskedWordDef {
    inst: InstId,
    pos: usize,
}

#[derive(Clone, Copy)]
struct MaskedUmullPlan {
    lhs_and: InstId,
    rhs_and: InstId,
    lhs: VReg,
    rhs: VReg,
}

/// Require the ordinary value-producing shape before deleting or changing an
/// instruction.  An instruction with bespoke implicit effects or flags is not
/// the isel form this identity proves and is therefore left alone.
fn canonical_masked_umull_inst(inst: &MachInst, opcode: AArch64Opcode, arity: usize) -> bool {
    inst.opcode == opcode
        && inst.operands.len() == arity
        && inst.implicit_defs.is_empty()
        && inst.implicit_uses.is_empty()
        && inst.flags == opcode.default_flags()
        // No transfer of an opcode-bound proof to a shift/add or UMULL is
        // established here. Preserve the original instruction instead.
        && inst.proof.is_none()
}

fn masked_word_source(
    func: &MachFunction,
    masked: VReg,
    def: MaskedWordDef,
    last_def_pos: &HashMap<u32, usize>,
) -> Option<VReg> {
    let inst = func.inst(def.inst);
    if !canonical_masked_umull_inst(inst, AArch64Opcode::AndRI, 3)
        || inst.operands[0].as_vreg()? != masked
        || inst.operands[2].as_imm()? != LOW_WORD_MASK
        || masked.class != RegClass::Gpr64
        || masked.id >= func.next_vreg
    {
        return None;
    }
    let src = inst.operands[1].as_vreg()?;
    // Keep the producer in ordinary SSA-like form.  A tied `t = t & mask`
    // would make deleting the defining instruction depend on the pre-def value
    // of the same VReg, an admission surface this F1 combine does not need.
    if src.class != RegClass::Gpr64 || src.id >= func.next_vreg || src == masked {
        return None;
    }

    // Folding moves the source read from the AND down to the multiply.  A
    // redefinition in that interval would make the later read observe a
    // different value.  No entry means the source is a live-in, which is fine.
    if last_def_pos
        .get(&src.id)
        .is_some_and(|&last| last > def.pos)
    {
        return None;
    }
    Some(src)
}

fn analyze_masked_umull(
    func: &MachFunction,
    mul: &MachInst,
    and_defs: &HashMap<u32, MaskedWordDef>,
    read_counts: &HashMap<u32, u8>,
    last_def_pos: &HashMap<u32, usize>,
) -> Option<MaskedUmullPlan> {
    if !canonical_masked_umull_inst(mul, AArch64Opcode::MulRR, 3) {
        return None;
    }
    let dst = mul.operands[0].as_vreg()?;
    let masked_lhs = mul.operands[1].as_vreg()?;
    let masked_rhs = mul.operands[2].as_vreg()?;
    if dst.class != RegClass::Gpr64
        || masked_lhs.class != RegClass::Gpr64
        || masked_rhs.class != RegClass::Gpr64
        || dst.id >= func.next_vreg
        || masked_lhs.id >= func.next_vreg
        || masked_rhs.id >= func.next_vreg
        // Keep the admission surface deliberately narrow.  A single masked
        // value squared could also use UMULL, but deleting one producer would
        // require a separate exact-two-reads proof.
        || masked_lhs == masked_rhs
        || read_counts.get(&masked_lhs.id).copied() != Some(1)
        || read_counts.get(&masked_rhs.id).copied() != Some(1)
    {
        return None;
    }
    let lhs_def = *and_defs.get(&masked_lhs.id)?;
    let rhs_def = *and_defs.get(&masked_rhs.id)?;
    if lhs_def.inst == rhs_def.inst {
        return None;
    }
    let lhs = masked_word_source(func, masked_lhs, lhs_def, last_def_pos)?;
    let rhs = masked_word_source(func, masked_rhs, rhs_def, last_def_pos)?;
    Some(MaskedUmullPlan {
        lhs_and: lhs_def.inst,
        rhs_and: rhs_def.inst,
        lhs,
        rhs,
    })
}

fn run_masked_umull_fuse(
    func: &mut MachFunction,
    mut provenance: Option<&mut ProvenanceMap>,
) -> bool {
    // Collect only eligible opcode/metadata shapes from layout. Without both
    // opcodes there is no candidate and no need for a whole-function census.
    // Count layout occurrences too: a duplicate layout must not authorize
    // mutating a site as though it were uniquely emitted.
    let mut has_and = false;
    let mut has_mul = false;
    let mut owners: HashMap<InstId, (u8, u8)> = HashMap::default();
    let mut read_counts: HashMap<u32, u8> = HashMap::default();
    for &block_id in &func.block_order {
        for &inst_id in &func.block(block_id).insts {
            let inst = func.inst(inst_id);
            match inst.opcode {
                AArch64Opcode::AndRI
                    if canonical_masked_umull_inst(inst, AArch64Opcode::AndRI, 3) =>
                {
                    has_and = true;
                    if let Some(dst) = inst.operands[0].as_vreg()
                        && dst.class == RegClass::Gpr64
                        && dst.id < func.next_vreg
                    {
                        read_counts.entry(dst.id).or_default();
                    }
                }
                AArch64Opcode::MulRR
                    if canonical_masked_umull_inst(inst, AArch64Opcode::MulRR, 3) =>
                {
                    has_mul = true;
                }
                _ => continue,
            }
            let (planned, _) = owners.entry(inst_id).or_default();
            *planned = planned.saturating_add(1).min(2);
        }
    }
    if !has_and || !has_mul {
        return false;
    }

    // Overwriting/deleting an arena instruction requires unique ownership in
    // ALL blocks, not just layout. Deleting an AND additionally requires one
    // read operand in the whole function: the multiply operand. Compute both
    // inventories in the same traversal, including omitted-layout consumers
    // through different instruction IDs. Shared operand roles remain the sole
    // read classifier; no instruction semantics are reimplemented here. Only
    // potential AND-result registers need storage; saturating at two retains
    // exactly the distinction that deletion's single-read gate consumes.
    // Keys are numeric IDs, not class-sensitive VRegs: a W-view read still
    // consumes the low bits of its X-view producer.
    for block in &func.blocks {
        for &inst_id in &block.insts {
            if let Some((_, references)) = owners.get_mut(&inst_id) {
                *references = references.saturating_add(1).min(2);
            }
            crate::effects::for_each_inst_use(func.inst(inst_id), |used| {
                if let Some(count) = read_counts.get_mut(&used.id) {
                    *count = count.saturating_add(1).min(2);
                }
            });
        }
    }
    let mut changed = false;

    for block_id in func.block_order.clone() {
        // Only same-block preceding ANDs are eligible.  Entries are removed by
        // every later definition of the same numeric ID, making a hit the
        // actual reaching definition at the multiply. W writes clobber the X
        // view too, matching the shared reaching-constant definition model.
        let mut and_defs: HashMap<u32, MaskedWordDef> = HashMap::default();
        let mut last_def_pos: HashMap<u32, usize> = HashMap::default();
        let block_insts = func.block(block_id).insts.clone();

        for (pos, inst_id) in block_insts.into_iter().enumerate() {
            // Keep the original shape for def-map maintenance after an in-place
            // rewrite of the current multiply.
            let original = func.inst(inst_id).clone();

            if original.opcode == AArch64Opcode::MulRR
                && let Some(plan) =
                    analyze_masked_umull(func, &original, &and_defs, &read_counts, &last_def_pos)
                && [plan.lhs_and, plan.rhs_and, inst_id]
                    .iter()
                    .all(|id| owners.get(id) == Some(&(1, 1)))
            {
                let mut fused = original.clone();
                fused.opcode = AArch64Opcode::Umull;
                fused.operands = vec![
                    original.operands[0].clone(),
                    MachOperand::VReg(plan.lhs),
                    MachOperand::VReg(plan.rhs),
                ];
                fused.flags = AArch64Opcode::Umull.default_flags();
                *func.inst_mut(inst_id) = fused;
                *func.inst_mut(plan.lhs_and) = MachInst::new(AArch64Opcode::Nop, vec![]);
                *func.inst_mut(plan.rhs_and) = MachInst::new(AArch64Opcode::Nop, vec![]);
                if let Some(provenance) = provenance.as_deref_mut() {
                    provenance.record_merge(
                        &[plan.lhs_and, plan.rhs_and, inst_id],
                        inst_id,
                        masked_umull_pass_id(),
                    );
                }
                changed = true;
            }

            // Update the maps from the original instruction AFTER matching so
            // an instruction cannot act as its own reaching definition.
            let mut defs = Vec::new();
            crate::effects::aarch64_for_each_def_position(
                original.opcode,
                original.operands.len(),
                |def_pos| {
                    if let Some(MachOperand::VReg(v)) = original.operands.get(def_pos) {
                        defs.push(*v);
                    }
                },
            );
            for v in defs {
                and_defs.remove(&v.id);
                last_def_pos.insert(v.id, pos);
            }
            if original.opcode == AArch64Opcode::AndRI
                && let Some(dst) = original.operands.first().and_then(MachOperand::as_vreg)
            {
                and_defs.insert(dst.id, MaskedWordDef { inst: inst_id, pos });
            }
        }
    }
    changed
}

/// Recognize a `MulRR` / `Madd` by a small compile-time constant and build a
/// validated [`Plan`]. Returns `None` (BAIL) on every unproven precondition.
/// One linear scan's census of the move-wide defs (`Movz`/`Movn`/`Movk`)
/// of every vreg id, for `plan_for`'s structural prefilter.
enum MoveWide {
    /// Exactly one move-wide def: its base value when it is a `Movz`/`Movn`
    /// (`fold_chain`'s base cases, class-masked exactly as there), `None` for
    /// a `Movk` (a chain whose base is not known without the query).
    Single(Option<u64>),
    /// More than one move-wide def of this id.
    Many,
}

struct MoveWideCensus {
    by_id: crate::fast_hash::FxHashMap<u32, MoveWide>,
}

impl MoveWideCensus {
    fn build(func: &MachFunction) -> Self {
        use crate::reaching_const::{movn_value, movz_value};
        let mut by_id: crate::fast_hash::FxHashMap<u32, MoveWide> = Default::default();
        for &block_id in &func.block_order {
            for &inst_id in &func.block(block_id).insts {
                let inst = func.inst(inst_id);
                let base = match inst.opcode {
                    AArch64Opcode::Movz => movz_value(inst).map(|(dst, value)| {
                        let v = if dst.class == RegClass::Gpr32 {
                            value & 0xFFFF_FFFF
                        } else {
                            value
                        };
                        (dst.id, Some(v))
                    }),
                    AArch64Opcode::Movn => {
                        movn_value(inst).map(|(dst, value)| (dst.id, Some(value)))
                    }
                    AArch64Opcode::Movk => inst
                        .operands
                        .first()
                        .and_then(|o| o.as_vreg())
                        .map(|d| (d.id, None)),
                    _ => None,
                };
                let Some((id, base)) = base else {
                    continue;
                };
                by_id
                    .entry(id)
                    .and_modify(|e| *e = MoveWide::Many)
                    .or_insert(MoveWide::Single(base));
            }
        }
        Self { by_id }
    }

    fn get(&self, id: u32) -> Option<&MoveWide> {
        self.by_id.get(&id)
    }
}

fn analyze(
    func: &MachFunction,
    ctx: &std::cell::OnceCell<ReachingCtx>,
    mw: &MoveWideCensus,
    inst_id: InstId,
) -> Option<Plan> {
    let inst = func.inst(inst_id);
    match inst.opcode {
        AArch64Opcode::MulRR => {
            // MulRR [dst, op1, op2] : dst = op1 * op2. Multiply commutes, so the
            // constant may be either source; the other is `x`.
            if !canonical_masked_umull_inst(inst, AArch64Opcode::MulRR, 3) {
                return None;
            }
            let dst = inst.operands[0].as_vreg()?;
            let op1 = inst.operands[1].as_vreg()?;
            let op2 = inst.operands[2].as_vreg()?;
            // Prefer op2 as the constant (isel's `x * C` order), then op1.
            plan_for(func, ctx, mw, inst_id, dst, op1, op2, None)
                .or_else(|| plan_for(func, ctx, mw, inst_id, dst, op2, op1, None))
        }
        AArch64Opcode::Madd => {
            // Madd [dst, Xn, Xm, Xa] : dst = Xa + Xn*Xm. Xn*Xm commutes; Xa is
            // the addend folded in verbatim.
            if !canonical_masked_umull_inst(inst, AArch64Opcode::Madd, 4) {
                return None;
            }
            let dst = inst.operands[0].as_vreg()?;
            let xn = inst.operands[1].as_vreg()?;
            let xm = inst.operands[2].as_vreg()?;
            let xa = inst.operands[3].as_vreg()?;
            plan_for(func, ctx, mw, inst_id, dst, xn, xm, Some(xa))
                .or_else(|| plan_for(func, ctx, mw, inst_id, dst, xm, xn, Some(xa)))
        }
        _ => None,
    }
}

/// Try to build a plan for `dst = addend? + x * (const held by `cst`)`. `x` is
/// the multiplicand; `cst` is the candidate constant-multiplier operand.
#[allow(clippy::too_many_arguments)]
fn plan_for(
    func: &MachFunction,
    ctx: &std::cell::OnceCell<ReachingCtx>,
    mw: &MoveWideCensus,
    inst_id: InstId,
    dst: VReg,
    x: VReg,
    cst: VReg,
    addend: Option<VReg>,
) -> Option<Plan> {
    // Materialization allocates temporaries starting at next_vreg. Every old
    // operand must belong to the existing arena or a fresh temporary could
    // collide with a live operand. Refuse before reaching-def queries as well
    // as before any allocation or provenance mutation.
    if [dst, x, cst].iter().any(|v| v.id >= func.next_vreg)
        || addend.is_some_and(|v| v.id >= func.next_vreg)
    {
        return None;
    }

    // All operands must be the SAME GPR class as the destination — the emitted
    // shift/add/sub derive their W-vs-X form from the destination register, so a
    // width mismatch would silently change semantics. Bail on any non-GPR class.
    let class = dst.class;
    let width = match class {
        RegClass::Gpr32 => 32u32,
        RegClass::Gpr64 => 64u32,
        _ => return None,
    };
    if x.class != class || cst.class != class {
        return None;
    }
    if let Some(y) = addend
        && y.class != class
    {
        return None;
    }

    // Resolve the multiplier to a proven unique compile-time constant, or bail.
    // Structural prefilter, before any reaching-defs query. The query can
    // only succeed when the unique reaching def of `cst` is a move-wide
    // instruction (`fold_chain`'s Movz/Movn/Movk arms; anything else is
    // `None`): no move-wide def of that id anywhere -> None, exactly as the
    // query would answer. One move-wide def with a known base (Movz/Movn,
    // not a Movk chain) -> if the query succeeds it yields that very base,
    // so a base that does not decompose is the same `None` the full path
    // returns after the query; a base that does decompose falls through to
    // the query, which alone decides whether that def actually reaches.
    match mw.get(cst.id) {
        None => return None,
        Some(MoveWide::Single(Some(base))) => {
            let mut val = *base;
            if cst.class.size_bits() <= 32 {
                val &= 0xFFFF_FFFF;
            }
            let raw = val as i64;
            let c: i128 = if width == 32 {
                i128::from(raw as i32)
            } else {
                i128::from(raw)
            };
            decompose(c, width)?;
        }
        Some(MoveWide::Single(None)) | Some(MoveWide::Many) => {}
    }
    let raw = unique_reaching_const_with(
        func,
        ctx.get_or_init(|| ReachingCtx::new(func)),
        inst_id,
        cst,
    )?;
    // Sign-extend from the operation width: a 32-bit `-3` arrives as the
    // zero-extended `0xFFFF_FFFD`; interpret it as `-3` so the compact 2-term
    // `1 - 4` decomposition is found. `x * c ≡ x * (c mod 2^W) (mod 2^W)`, so
    // re-signing the low `W` bits is value-preserving.
    let c: i128 = if width == 32 {
        i128::from(raw as i32)
    } else {
        i128::from(raw)
    };

    let terms = decompose(c, width)?;
    // A leading positive term is required to seed the additive accumulator
    // without a negate; `decompose` guarantees it, but re-check fail-closed.
    if !terms.iter().any(|t| t.positive) {
        return None;
    }

    Some(Plan {
        x,
        addend,
        dst,
        class,
        terms,
        source_loc: func.inst(inst_id).source_loc,
    })
}

/// Decompose signed `c` into AT MOST TWO signed power-of-two terms
/// `s_a·2^a (+ s_b·2^b)` with `a > b ≥ 0`, shifts `< width`, sign combination
/// restricted to `{(+), (+,+), (+,-), (-,+)}` (a leading positive always
/// exists; `(-,-)` is excluded). Returns the terms larger-shift-first, or
/// `None` if `c` needs ≥3 terms / is out of range (BAIL).
fn decompose(c: i128, width: u32) -> Option<Vec<Term>> {
    // Only genuinely small constants; `|c| <= 1` (mul by 0/1/-1) is a degenerate
    // case handled by const-fold / declarative-rewrite, not this pass.
    if c.abs() < 2 || c.abs() > MAX_ABS_CONST {
        return None;
    }
    let w = width as i128;
    for a in 1..w {
        let pa: i128 = 1i128 << a;
        // Single positive power of two: c == 2^a.
        if c == pa {
            return Some(vec![Term {
                positive: true,
                shift: a as u32,
            }]);
        }
        // Two-term: c == s_a·2^a + s_b·2^b, with b < a.
        for &sa in &[1i128, -1i128] {
            let rem = c - sa * pa;
            if rem == 0 {
                // c == s_a·2^a exactly; the +2^a single term is handled above,
                // and a lone -2^a is intentionally not emitted (needs a negate).
                continue;
            }
            let mag = rem.unsigned_abs();
            if !mag.is_power_of_two() {
                continue;
            }
            let b = mag.trailing_zeros();
            if (a as u32) <= b || b >= width {
                continue; // require distinct powers b < a, and b in range
            }
            // ONE-SHIFT restriction: require the smaller power to be 2^0, so the
            // sequence emits at most a SINGLE `LslRI` (`x<<a`) plus one add/sub
            // — `2^a ± 1` / `1 - 2^a`. A two-shift form (both powers ≥ 2, e.g.
            // `24 = 16 + 8`) would emit two shifts + an add (3 ALU ops for one
            // MUL); in a THROUGHPUT-bound loop (matmul's `i*24` index math) that
            // is a measured regression, and its only benefit is a latency edge
            // that helps solely latency-bound chains. Bailing keeps the pass
            // strictly throughput-safe (never slower). The collatz target
            // `3 = 2 + 1` is a one-shift form and still fires.
            if b != 0 {
                continue;
            }
            let sa_pos = sa > 0;
            let sb_pos = rem > 0;
            // Exclude (-,-): no positive term to seed the accumulator.
            if !sa_pos && !sb_pos {
                continue;
            }
            return Some(vec![
                Term {
                    positive: sa_pos,
                    shift: a as u32,
                },
                Term {
                    positive: sb_pos,
                    shift: b,
                },
            ]);
        }
    }
    None
}

/// Whether a `Madd`'s addend `y` is computed in the multiply's own block (its
/// last definition before the `Madd` there, by numeric register ID, is not a
/// constant materialization)
/// while the decomposition subtracts a term (`2^k - 1`, `1 - 2^k`). Such an
/// addend is the per-iteration value the multiply's result waits for
/// (p5_struct_acc's `a = a*31 + (c ^ i)`: `c ^ i` is the end of the loop's
/// long recurrence), so it is added LAST: `((x<<k) - x) + y` puts one add
/// after `y` instead of two (`(y + (x<<k)) - x`), and the path from `x` stays
/// shift, sub, add. The `2^k + 1` shape keeps its order: with no subtracted
/// term the deferral measured as a regression on `m1_call_chain`
/// (`addend_last`'s note).
fn late_addend_with_negative_term(func: &MachFunction, plan: &Plan, madd: InstId) -> bool {
    let Some(y) = plan.addend else {
        return false;
    };
    if !plan.terms.iter().any(|t| !t.positive) {
        return false;
    }
    for &bid in &func.block_order {
        let insts = &func.block(bid).insts;
        let Some(pos) = insts.iter().position(|&iid| iid == madd) else {
            continue;
        };
        let Some(def) = insts[..pos]
            .iter()
            .rev()
            .map(|&iid| func.inst(iid))
            .find(|inst| crate::effects::inst_clobbers_vreg_id(inst, y.id))
        else {
            return false;
        };
        return !matches!(
            def.opcode,
            AArch64Opcode::Movz
                | AArch64Opcode::Movn
                | AArch64Opcode::Movk
                | AArch64Opcode::MovI
                | AArch64Opcode::Adrp
                | AArch64Opcode::AddPCRel
        );
    }
    false
}

/// Does any `Csel` read `dst` as one of its two SELECT VALUE operands
/// (positions 1/2 — the `cond ? op1 : op2` values), NOT the condition immediate?
/// Sound whole-function scan; used to gate the deferred-addend reorder to sites
/// where a downstream Csel->Csinc fold can consume the exposed `+1`.
fn dst_feeds_csel_value_arm(func: &MachFunction, dst: VReg) -> bool {
    for &bid in &func.block_order {
        for &iid in &func.block(bid).insts {
            let inst = func.inst(iid);
            if inst.opcode == AArch64Opcode::Csel && inst.operands.len() >= 3 {
                let arm1 = inst.operands[1].as_vreg() == Some(dst);
                let arm2 = inst.operands[2].as_vreg() == Some(dst);
                if arm1 || arm2 {
                    return true;
                }
            }
        }
    }
    false
}

/// Materialize a validated plan into fresh instructions and return their
/// InstIds in emission order (shifts first, then the add/sub fold whose last
/// instruction defines `dst`). Infallible: `analyze` validated every
/// precondition.
fn materialize(
    func: &mut MachFunction,
    plan: &Plan,
    old_id: InstId,
    mut provenance: Option<&mut ProvenanceMap>,
) -> Vec<InstId> {
    let class = plan.class;
    let sloc = plan.source_loc;
    let mut new_ids: Vec<InstId> = Vec::new();

    // Emit one instruction, stamping source_loc and threading provenance.
    let push_new = |func: &mut MachFunction,
                    provenance: &mut Option<&mut ProvenanceMap>,
                    new_ids: &mut Vec<InstId>,
                    opcode: AArch64Opcode,
                    operands: Vec<MachOperand>|
     -> InstId {
        let mut inst = MachInst::new(opcode, operands);
        inst.source_loc = sloc;
        let id = func.push_inst(inst);
        if let Some(p) = provenance.as_deref_mut() {
            p.record_creation(id, pass_id(), "mul->shift-add strength reduction");
        }
        new_ids.push(id);
        id
    };

    // Fast path: single positive power-of-two multiply (`MulRR x, 2^a`), no
    // addend — a lone `LslRI` straight into `dst`.
    if plan.addend.is_none() && plan.terms.len() == 1 {
        let t = plan.terms[0];
        debug_assert!(t.positive && t.shift >= 1);
        let id = push_new(
            func,
            &mut provenance,
            &mut new_ids,
            AArch64Opcode::LslRI,
            vec![
                MachOperand::VReg(plan.dst),
                MachOperand::VReg(plan.x),
                MachOperand::Imm(i64::from(t.shift)),
            ],
        );
        if let Some(p) = provenance.as_deref_mut() {
            p.record_replacement(old_id, id, pass_id());
        }
        return new_ids;
    }

    // Materialize each term's summand register: a fresh `x << shift` temp for a
    // real shift, or plain `x` for a shift-0 term. Record whether it is a
    // 1-cycle-later shift temp (for latency-minimizing fold ordering).
    struct Summand {
        positive: bool,
        reg: VReg,
        is_shift: bool,
    }
    let mut summands: Vec<Summand> = Vec::new();
    for &t in &plan.terms {
        let reg = if t.shift == 0 {
            plan.x
        } else {
            let temp = VReg::new(func.alloc_vreg(), class);
            push_new(
                func,
                &mut provenance,
                &mut new_ids,
                AArch64Opcode::LslRI,
                vec![
                    MachOperand::VReg(temp),
                    MachOperand::VReg(plan.x),
                    MachOperand::Imm(i64::from(t.shift)),
                ],
            );
            temp
        };
        summands.push(Summand {
            positive: t.positive,
            reg,
            is_shift: t.shift != 0,
        });
    }
    // ADDEND PLACEMENT. For the ALL-POSITIVE `2^k + 1` shape (a plain-`x`
    // shift-0 seed term plus one or more positive shift terms), with a `Madd`
    // addend `y`, DEFER the addend to the single OUTERMOST add — emitting
    // `(x + (x<<k)) + y` rather than the historical `(x + y) + (x<<k)`. Two
    // reasons this is the better order and never a regression:
    //   * The plain-`x` term still seeds the accumulator and the shift term is
    //     added to it, so shift-alu-fuse still folds the `x<<k` into a single
    //     `AddRRShift` (`ADD x, x, LSL #k`) — identical op count to before.
    //   * The trailing `+ y` becomes the LONE outermost op feeding the value's
    //     consumer, so a downstream `Csel`->`Csinc` fold can absorb a `+1`
    //     addend into the select's increment (p2_collatz's `c*3+1` odd arm,
    //     where `y` materializes the constant `1`).
    // SOUNDNESS: pure wrapping-add reassociation over Z/2^W. Integer `+` is
    // associative and commutative in the ring, so `(x + y) + (x<<k)` and
    // `(x + (x<<k)) + y` are the SAME sum of `{x, x<<k, y}` and are bit-exact
    // for `wrapping_mul`/`Madd`. Every OTHER decomposition shape (pure powers,
    // `2^k - 1`, `1 - 2^k`, multi-term) keeps the prior emission byte-for-byte:
    // the addend stays a ready summand folded first, exactly as before.
    // Gate the reorder on the Madd result actually FEEDING a `Csel` value arm.
    // The deferred-addend order exists ONLY to expose a `+1` for the downstream
    // Csel->Csinc fold; where the result is not a select arm (m1_call_chain's
    // `f(x) = 3x + acc` chain), the reorder buys nothing and perturbs scheduling
    // (a measured regression). Requiring a Csel consumer keeps EVERY non-select
    // 2^k+1 Madd byte-identical, and by O2/O3 pass order `if-convert` has already
    // formed the Csel that consumes this Madd's dst, so the check sees it.
    let addend_last = (plan.addend.is_some()
        && plan.terms.iter().all(|t| t.positive)
        && plan.terms.iter().any(|t| t.shift == 0)
        && dst_feeds_csel_value_arm(func, plan.dst))
        || late_addend_with_negative_term(func, plan, old_id);
    // The `Madd` addend is an extra positive summand, ready before the loop body
    // (loop-invariant / early), so it sorts with the ready terms — UNLESS
    // `addend_last`, in which case it is deferred to the final outermost add.
    if let Some(y) = plan.addend
        && !addend_last
    {
        summands.push(Summand {
            positive: true,
            reg: y,
            is_shift: false,
        });
    }

    // Order for the shortest carried path: fold the 0-cycle-ready operands
    // (plain `x`, the addend) FIRST while the `x<<k` shifts compute in parallel,
    // then fold the shift temps in last. Within each list, ready-before-shift.
    let mut pos: Vec<VReg> = Vec::new();
    let mut neg: Vec<VReg> = Vec::new();
    for s in summands.iter().filter(|s| s.positive && !s.is_shift) {
        pos.push(s.reg);
    }
    for s in summands.iter().filter(|s| s.positive && s.is_shift) {
        pos.push(s.reg);
    }
    for s in summands.iter().filter(|s| !s.positive && !s.is_shift) {
        neg.push(s.reg);
    }
    for s in summands.iter().filter(|s| !s.positive && s.is_shift) {
        neg.push(s.reg);
    }

    // `analyze` guarantees at least one positive term.
    debug_assert!(!pos.is_empty());

    // Build the additive/subtractive fold: acc = pos[0]; += pos[1..]; -= neg[..].
    // Each op writes a fresh temp except the LAST, which writes `dst`.
    let mut steps: Vec<(AArch64Opcode, VReg)> = Vec::new();
    for &p in &pos[1..] {
        steps.push((AArch64Opcode::AddRR, p));
    }
    for &n in &neg {
        steps.push((AArch64Opcode::SubRR, n));
    }
    // Deferred addend: the FINAL outermost `+ y` (see `addend_last`). The
    // step list is non-empty either way: the `2^k+1` shape has ≥2 positive
    // terms, and the late-addend shapes have a negative term (a `-` step).
    if addend_last {
        let y = plan.addend.expect("addend_last implies a Madd addend");
        steps.push((AArch64Opcode::AddRR, y));
    }
    debug_assert!(!steps.is_empty(), "≥2 summands ⇒ ≥1 fold op");

    let n_steps = steps.len();
    let mut acc = pos[0];
    let mut last_id = old_id; // overwritten below
    for (i, (opc, rm)) in steps.into_iter().enumerate() {
        let out = if i == n_steps - 1 {
            plan.dst
        } else {
            VReg::new(func.alloc_vreg(), class)
        };
        last_id = push_new(
            func,
            &mut provenance,
            &mut new_ids,
            opc,
            vec![
                MachOperand::VReg(out),
                MachOperand::VReg(acc),
                MachOperand::VReg(rm),
            ],
        );
        acc = out;
    }

    if let Some(p) = provenance {
        p.record_replacement(old_id, last_id, pass_id());
    }
    new_ids
}

#[cfg(test)]
mod tests;
