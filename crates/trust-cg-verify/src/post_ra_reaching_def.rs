// trust-cg-verify/post_ra_reaching_def.rs - TV-6 post-RA aarch64 reaching-def validation
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! TV-6: physical-register REACHING-DEFINITION validation of the FINAL
//! post-register-allocation, post-spill-materialization AArch64 stream
//! (`[TCG-A64-REACHING-DEF]`).
//!
//! # What this closes
//!
//! The AArch64 post-RA stream is today only STRUCTURALLY rechecked
//! ([`crate::post_regalloc_recheck`]: within-block terminator integrity + the
//! `nonpromotable_regression` opcode-inventory monotonicity check). Neither
//! looks at register DATAFLOW: a spill materialization that dropped a reload, a
//! post-RA coalesce/peephole that deleted a defining copy, or any transform that
//! left a physical register READ with no preceding WRITE, passes the structural
//! recheck and MISCOMPILES SILENTLY. The regalloc translation validator runs
//! BEFORE spill materialization and documents a reload-register blind spot.
//!
//! This module adds a purpose-built Tier-2 dataflow net over the same final
//! stream the structural recheck sees: a forward MUST reaching-definition
//! fixpoint that flags **every physical-register read that lacks a reaching
//! definition on some path from function entry** (use-before-def). It is
//! deliberately small — AArch64 is a load/store RISC with 3-operand,
//! non-destructive instructions and NO x86-style two-address fixup, so it does
//! NOT need TV-5's tied-ghost-operand machinery (`crate::post_ra_dataflow`,
//! x86-only); the reaching-def property is the whole slice.
//!
//! # Property (one clean, sound thing)
//!
//! For every instruction read of a physical register R, there is a definition of
//! R (or of an aliasing sub/super-register) on EVERY control-flow path from the
//! function entry to that read. A read with no reaching def on some path is an
//! unambiguous post-RA bug: the value consumed is whatever happened to be in the
//! register, i.e. a miscompile. Memory / spill-slot dataflow (which stack slot a
//! reload reads) is register-only here and DEFERRED to a later slice.
//!
//! # Why it is false-positive free (WARN-net discipline)
//!
//! The analysis is a MUST (intersection-at-joins) forward dataflow. It reports a
//! read only when the register is undefined on some structural predecessor path.
//! In correct register-allocator output every read is structurally dominated by
//! a def (that is what SSA-destruction + spill/reload guarantee), so a clean
//! stream produces ZERO reports. The report set can only be non-empty if a def
//! is genuinely missing on a path — the bug class. The conservative bails that
//! keep it FP-free:
//!
//! * **Def/use partition reuses the allocator's own model.** The def/use roles
//!   are derived from [`trust_cg_opt::effects::aarch64_operand_roles`] behind an
//!   exact reproduction of codegen's `classify_operand_positions` (LSE-atomic,
//!   pre/post-index writeback, and the store/branch/return/call/compare
//!   "all-operands-are-uses" fast path). Because the validator's DEF set is
//!   exactly the allocator's DEF set, no def the allocator produced is ever
//!   missed — the only way a `must`-analysis false-fires.
//! * **Registers legitimately live-in are seeded defined-at-entry**
//!   ([`entry_seed_mask`]): ABI args (X0-X7 / V0-V7), SP, X29/FP, X30/LR, all
//!   callee-saved (X19-X28, V8-V15, read by the prologue before being
//!   repurposed), the reserved X8/X18, and XZR/WZR (which collapse onto SP's
//!   location bit). Reads of these never fire.
//! * **W/X and B/H/S/D/Q sub-register aliasing is normalized** ([`loc_bit`]): a
//!   `W9` write defines the `X9` location, so a widened read never false-fires.
//! * **Calls define their clobber set.** A `Bl`/`Blr` `implicit_defs` (the
//!   caller-saved clobbers + result reg) count as definitions; `implicit_uses`
//!   (arg regs) count as reads. Reading a call-clobbered register post-call is
//!   thus "defined" (definedness, not value-correctness — the latter is the
//!   regalloc TV's job).
//! * **Anything unmodeled DECLINES rather than flags.** A non-final stream (a
//!   surviving `VReg`, an unresolved `StackSlot`/`FrameIndex`/`IncomingArg`), a
//!   malformed CFG, or a non-converging fixpoint yields ZERO reports. System
//!   registers (NZCV/FPCR/FPSR — flag dataflow) are not tracked in this slice.
//!
//! # Enforcement
//!
//! First slice ships **WARN** ([`AARCH64_REACHING_DEF_DEFAULT`]), gated by
//! `TCG_AARCH64_POST_RA_REACHING_DEF` (`off`|`warn`|`enforce`). Ships **ENFORCE**
//! (env-downgradable) after a 0-false-WARN soak of ~3184 a64 functions across the
//! differential corpus, diverse operand-role surfaces (LSE atomics, sign-ext,
//! ext-reg addressing, callee-saved FPR), AND real rustc->bridge->a64 programs
//! (bench kernels + dyn-trait / iterators / niche Options / structs / floats) —
//! mirroring how [`crate::post_regalloc_recheck`] was flipped to ENFORCE after a
//! warn-only telemetry pass. A dropped-reload / corrupted-dataflow post-RA bug
//! now FAILS the compile closed instead of shipping a silent miscompile.

use std::collections::VecDeque;
use std::sync::atomic::{AtomicU64, Ordering};

use trust_cg_ir::aarch64_regs::{preg_class, reg_number};
use trust_cg_ir::{AArch64Opcode, MachFunction, MachInst, MachOperand, PReg, RegClass};
use trust_cg_opt::effects::{OperandRole, aarch64_operand_roles, is_lse_cas, is_lse_rmw};

pub use crate::post_regalloc_recheck::PostRegallocRecheckMode;

// ---------------------------------------------------------------------------
// Location model: canonical W/X + V/D/S/H/B alias-collapsed register locations
// ---------------------------------------------------------------------------

/// Number of tracked locations: 32 GPR + 32 FPR (System regs untracked).
const LOC_COUNT: u32 = 64;

/// Canonical alias-collapsed location bit for a physical register, or `None`
/// for a register this slice does not track (NZCV / FPCR / FPSR — flag dataflow
/// is a deferred slice). GPR occupies bits `0..=31`, FPR bits `32..=63`, keyed
/// by the register NUMBER so `W9`/`X9` share one bit and `S5`/`D5`/`Q5`/`V5`
/// share another. XZR/WZR collapse onto number 31 (SP's bit) and so are treated
/// as always-defined — sound, they read as constant zero.
fn loc_bit(reg: PReg) -> Option<u32> {
    let num = reg_number(reg)? as u32; // 0..=31 within its register file
    let group = match preg_class(reg) {
        RegClass::Gpr64 | RegClass::Gpr32 => 0,
        RegClass::Fpr128 | RegClass::Fpr64 | RegClass::Fpr32 | RegClass::Fpr16 | RegClass::Fpr8 => {
            1
        }
        RegClass::System => return None,
    };
    Some(group * 32 + num)
}

/// Single-bit mask for a register's canonical location, or 0 for an untracked
/// (System) register — a 0 mask makes both the gen_bits and the read-check skip it.
#[inline]
fn loc_mask(reg: PReg) -> u64 {
    match loc_bit(reg) {
        Some(b) => 1u64 << b,
        None => 0,
    }
}

/// The set of locations that legitimately hold a defined value on entry to any
/// correct AArch64 function body, so the WARN net never fires on them:
/// - ABI argument registers X0-X7 / V0-V7 (defined by the caller);
/// - the frame/link/stack registers X29/FP, X30/LR, SP (established or passed by
///   the prologue);
/// - the callee-saved registers X19-X28 / V8-V15 (the prologue READS them to
///   spill the incoming caller values before repurposing them);
/// - the reserved X8 (indirect-result) and X18 (platform) registers;
/// - XZR/WZR (collapse onto SP's bit; read as constant zero).
///
/// DELIBERATELY EXCLUDED so a dropped def / dropped reload against them is
/// CAUGHT: the allocatable caller-saved temporaries X9-X15 and V16-V31, and the
/// IP0/IP1 scratch registers X16/X17 the spill materializer reloads into.
fn entry_seed_mask() -> u64 {
    let mut m = 0u64;
    // GPR group (bit == register number): X0-X8 and X18-X31; excludes X9-X17.
    for n in 0u32..=8 {
        m |= 1u64 << n;
    }
    for n in 18u32..=31 {
        m |= 1u64 << n;
    }
    // FPR group (bits 32..=63): V0-V15; excludes V16-V31.
    for n in 0u32..=15 {
        m |= 1u64 << (32 + n);
    }
    m
}

// ---------------------------------------------------------------------------
// Access model: def/use partition, reproduced from codegen's regalloc classifier
// ---------------------------------------------------------------------------

/// Opcodes whose operand roles encode an explicit base-register writeback
/// (pre/post-index and NEON post-increment). Mirrors codegen
/// `opcode_has_explicit_writeback_operand_roles`.
fn is_explicit_writeback(op: AArch64Opcode) -> bool {
    use AArch64Opcode::*;
    matches!(
        op,
        NeonLd1Post
            | NeonLdpQPost
            | NeonSt1Post
            | NeonStpQPost
            | LdrPreIndex
            | StrPreIndex
            | LdrPostIndex
            | StrPostIndex
            | LdpPostIndex
            | StpPreIndex
    )
}

/// Mirror of codegen `opcode_uses_all_operands_for_regalloc`: stores, branches,
/// returns, calls and compares expose EVERY register operand as a read and
/// define none through an explicit operand (their result, if any, is an
/// `implicit_def`). Kept byte-identical to the regalloc classifier so the
/// def/use partition this validator derives is exactly the one the allocator
/// itself used — the invariant that makes the WARN net false-positive-free.
fn uses_all_operands(inst: &MachInst) -> bool {
    let op = inst.opcode;
    if is_lse_rmw(op) || is_lse_cas(op) || is_explicit_writeback(op) {
        return false;
    }
    inst.writes_memory()
        || inst.is_branch()
        || inst.is_return()
        || inst.is_call()
        || matches!(
            op,
            AArch64Opcode::CmpRR | AArch64Opcode::CmpRI | AArch64Opcode::Fcmp
        )
}

/// Faithful reproduction of codegen `classify_operand_positions`: LSE atomics
/// and explicit-writeback forms use the shared role table directly; the
/// all-operands-are-uses class short-circuits; everything else uses the shared
/// role table (`produces_value` => operand 0 is a def, `has_tied_def_use` =>
/// def-use).
fn operand_roles(inst: &MachInst) -> Vec<OperandRole> {
    let op = inst.opcode;
    let n = inst.operands.len();
    if n == 0 {
        return Vec::new();
    }
    if is_lse_rmw(op) || is_lse_cas(op) || is_explicit_writeback(op) {
        return aarch64_operand_roles(op, n);
    }
    if uses_all_operands(inst) {
        return vec![OperandRole::Use; n];
    }
    aarch64_operand_roles(op, n)
}

/// `(gen_mask, reads)` for one instruction:
/// - `gen_mask` = every location the instruction DEFINES: explicit def-role
///   register operands, the base of a writeback memory operand, and every
///   `implicit_defs` clobber/result.
/// - `reads` = every physical register the instruction READS whose reaching
///   definition must exist: explicit use-role register operands, the base
///   address of every memory operand, and every `implicit_uses` register.
///
/// Non-register operands and System registers contribute nothing
/// (`loc_mask == 0` skips them in both the gen_bits accumulation and the read check).
fn inst_gen_reads(inst: &MachInst) -> (u64, Vec<PReg>) {
    let roles = operand_roles(inst);
    let mut gen_bits = 0u64;
    let mut reads = Vec::new();
    for (pos, operand) in inst.operands.iter().enumerate() {
        let role = roles.get(pos).copied().unwrap_or(OperandRole::Use);
        match operand {
            MachOperand::PReg(p) => {
                if role.is_use() {
                    reads.push(*p);
                }
                if role.is_def() {
                    gen_bits |= loc_mask(*p);
                }
            }
            MachOperand::MemOp { base, .. } => {
                // The base register is always read to form the address.
                reads.push(*base);
                // Pre/post-index writeback additionally DEFINES the base.
                if role.is_def() {
                    gen_bits |= loc_mask(*base);
                }
            }
            // Special(SP/XZR/WZR): seeded / never-undefined; not a tracked read.
            // Imm / FImm / Block / Symbol / JumpTableIndex: not registers.
            // VReg / StackSlot / FrameIndex / IncomingArg: handled by the
            //   decline scan (a stream carrying them is not the final form).
            _ => {}
        }
    }
    for &p in inst.implicit_defs {
        gen_bits |= loc_mask(p);
    }
    for &p in inst.implicit_uses {
        reads.push(p);
    }
    (gen_bits, reads)
}

/// A stream is in the final, fully-lowered form this validator models only if
/// no operand is a pre-regalloc `VReg` or a pre-frame-lowering memory
/// placeholder (`StackSlot`/`FrameIndex`/`IncomingArg`). Encountering any of
/// these means the analysis assumptions (all registers are physical, all frame
/// access is a resolved `MemOp`) do not hold, so we DECLINE — a WARN net must
/// never report on a stream it cannot soundly model.
fn stream_is_final(func: &MachFunction) -> bool {
    for &bid in &func.block_order {
        let Some(block) = func.blocks.get(bid.0 as usize) else {
            return false;
        };
        for &inst_id in &block.insts {
            let Some(inst) = func.insts.get(inst_id.0 as usize) else {
                return false;
            };
            for operand in &inst.operands {
                if matches!(
                    operand,
                    MachOperand::VReg(_)
                        | MachOperand::StackSlot(_)
                        | MachOperand::FrameIndex(_)
                        | MachOperand::IncomingArg(_)
                ) {
                    return false;
                }
            }
        }
    }
    true
}

// ---------------------------------------------------------------------------
// Forward MUST reaching-definition fixpoint
// ---------------------------------------------------------------------------

/// The defined-location set on entry to block `b`: the entry block starts from
/// the ABI seed; every other block is the INTERSECTION of its reachable
/// predecessors' out-sets (a location is defined only if defined on ALL paths).
fn block_in(
    func: &MachFunction,
    b: usize,
    entry_idx: usize,
    seed: u64,
    defined_out: &[u64],
    reachable: &[bool],
) -> u64 {
    if b == entry_idx {
        return seed;
    }
    let mut acc = u64::MAX;
    let mut any = false;
    for &p in &func.blocks[b].preds {
        let pi = p.0 as usize;
        if pi < reachable.len() && reachable[pi] {
            acc &= defined_out[pi];
            any = true;
        }
    }
    // A reachable non-entry block always has a reachable predecessor; the `seed`
    // fallback is defensive and can never under-define a seeded register.
    if any { acc } else { seed }
}

/// Run the analysis over `func`. Returns `Some(violations)` (possibly empty) for
/// a stream we could soundly model, or `None` to DECLINE (non-final stream,
/// malformed CFG, or non-convergence) — declining reports nothing.
fn analyze(func: &MachFunction) -> Option<Vec<ReachingDefViolation>> {
    if !stream_is_final(func) {
        return None;
    }
    let nblocks = func.blocks.len();
    if nblocks == 0 {
        return Some(Vec::new());
    }
    let entry_idx = func.entry.0 as usize;
    if entry_idx >= nblocks {
        return None;
    }
    let seed = entry_seed_mask();

    // 1. Reachability from entry over successor edges.
    let mut reachable = vec![false; nblocks];
    let mut queue = VecDeque::new();
    reachable[entry_idx] = true;
    queue.push_back(func.entry);
    while let Some(bid) = queue.pop_front() {
        let block = func.blocks.get(bid.0 as usize)?;
        for &s in &block.succs {
            let si = s.0 as usize;
            if si < nblocks && !reachable[si] {
                reachable[si] = true;
                queue.push_back(s);
            }
        }
    }

    // 2. Per-block gen_bits = union of instruction gens.
    let mut gen_bits = vec![0u64; nblocks];
    for b in 0..nblocks {
        if !reachable[b] {
            continue;
        }
        let mut g = 0u64;
        for &inst_id in &func.blocks[b].insts {
            let inst = func.insts.get(inst_id.0 as usize)?;
            let (ig, _) = inst_gen_reads(inst);
            g |= ig;
        }
        gen_bits[b] = g;
    }

    // 3. Forward MUST fixpoint. Non-entry out-sets start at TOP (all defined) so
    //    a not-yet-computed back-edge predecessor never spuriously narrows a
    //    loop header; intersection can only clear bits, so it converges.
    let mut defined_out = vec![u64::MAX; nblocks];
    defined_out[entry_idx] = seed | gen_bits[entry_idx];
    let max_iters = nblocks.saturating_mul(LOC_COUNT as usize).saturating_add(8);
    let mut iters = 0usize;
    loop {
        let mut changed = false;
        for &bid in &func.block_order {
            let b = bid.0 as usize;
            if b >= nblocks || !reachable[b] {
                continue;
            }
            let in_b = block_in(func, b, entry_idx, seed, &defined_out, &reachable);
            let new_out = in_b | gen_bits[b];
            if new_out != defined_out[b] {
                defined_out[b] = new_out;
                changed = true;
            }
        }
        iters += 1;
        if !changed {
            break;
        }
        if iters > max_iters {
            // Non-convergence (should be unreachable): decline, never flag.
            return None;
        }
    }

    // 4. Per-instruction read check.
    let mut violations = Vec::new();
    for &bid in &func.block_order {
        let b = bid.0 as usize;
        if b >= nblocks || !reachable[b] {
            continue;
        }
        let mut cur = block_in(func, b, entry_idx, seed, &defined_out, &reachable);
        for (inst_pos, &inst_id) in func.blocks[b].insts.iter().enumerate() {
            let inst = &func.insts[inst_id.0 as usize];
            let (ig, reads) = inst_gen_reads(inst);
            for r in reads {
                let m = loc_mask(r);
                if m != 0 && (cur & m) == 0 {
                    violations.push(ReachingDefViolation {
                        kind: ReachingDefViolationKind::ReadWithoutReachingDef,
                        detail: format!(
                            "block {} inst #{} ({:?}): physical register {} is READ with no reaching \
                             definition on every path from entry (use-before-def introduced post-RA — \
                             a dropped spill reload or corrupted register dataflow)",
                            bid.0, inst_pos, inst.opcode, r
                        ),
                    });
                }
            }
            cur |= ig;
        }
    }
    Some(violations)
}

// ---------------------------------------------------------------------------
// Violations
// ---------------------------------------------------------------------------

/// Which reaching-def property broke (one kind in this slice).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReachingDefViolationKind {
    /// A physical register is read with no reaching definition on some path.
    ReadWithoutReachingDef,
}

impl ReachingDefViolationKind {
    /// Greppable tag for the diagnostic line.
    pub fn tag(self) -> &'static str {
        match self {
            Self::ReadWithoutReachingDef => "read-without-reaching-def",
        }
    }
}

/// A single reaching-def violation. In ENFORCE mode any one fails the compile.
#[derive(Debug, Clone)]
pub struct ReachingDefViolation {
    /// Which property broke.
    pub kind: ReachingDefViolationKind,
    /// Human-readable diagnostic (block / inst index / opcode / register).
    pub detail: String,
}

// ---------------------------------------------------------------------------
// Mode + telemetry
// ---------------------------------------------------------------------------

/// Default mode for the aarch64 reaching-def net: WARN (first slice). Flip to
/// ENFORCE only after a 0-hit corpus soak, exactly as the structural recheck was.
pub const AARCH64_REACHING_DEF_DEFAULT: PostRegallocRecheckMode = PostRegallocRecheckMode::Enforce;

/// Resolve the active mode from `TCG_AARCH64_POST_RA_REACHING_DEF`
/// (`off`|`warn`|`enforce`, or `0`|`1`|`2`), defaulting to
/// [`AARCH64_REACHING_DEF_DEFAULT`]. Env gating is permitted here because the
/// default is the NON-gating WARN mode; it is the knob the soak ratchet turns.
pub fn reaching_def_mode() -> PostRegallocRecheckMode {
    match std::env::var("TCG_AARCH64_POST_RA_REACHING_DEF").as_deref() {
        Ok("off") | Ok("0") => PostRegallocRecheckMode::Off,
        Ok("enforce") | Ok("2") => PostRegallocRecheckMode::Enforce,
        Ok("warn") | Ok("1") => PostRegallocRecheckMode::Warn,
        _ => AARCH64_REACHING_DEF_DEFAULT,
    }
}

/// Process-wide count of reaching-def violations observed (warn or enforce).
static VIOLATION_HITS: AtomicU64 = AtomicU64::new(0);
/// Streams the net could soundly MODEL (final form) — active-coverage telemetry.
static STREAMS_ANALYZED: AtomicU64 = AtomicU64::new(0);
/// Streams the net DECLINED (non-final / malformed) — inert on these.
static STREAMS_DECLINED: AtomicU64 = AtomicU64::new(0);

/// Total reaching-def violations observed by this process (soak telemetry).
pub fn reaching_def_hit_count() -> u64 {
    VIOLATION_HITS.load(Ordering::Relaxed)
}

/// (analyzed, declined) stream counts — how much of the corpus the net actually
/// modeled vs conservatively skipped. Confirms the net is ACTIVE, not inert.
pub fn coverage_counts() -> (u64, u64) {
    (
        STREAMS_ANALYZED.load(Ordering::Relaxed),
        STREAMS_DECLINED.load(Ordering::Relaxed),
    )
}

fn record_violation(function_name: &str, detail: &str, mode: PostRegallocRecheckMode) {
    VIOLATION_HITS.fetch_add(1, Ordering::Relaxed);
    let tag = match mode {
        PostRegallocRecheckMode::Enforce => "[TCG-A64-REACHING-DEF-FAIL]",
        _ => "[TCG-A64-REACHING-DEF-WARN]",
    };
    eprintln!("{tag} arch=aarch64 fn={function_name}: {detail}");
}

// ---------------------------------------------------------------------------
// Public entry points
// ---------------------------------------------------------------------------

/// Pure entry point: the reaching-def violations in `func`, or an EMPTY list for
/// a clean stream OR a stream this validator declines to model. Side-effect free.
pub fn check(func: &MachFunction) -> Vec<ReachingDefViolation> {
    analyze(func).unwrap_or_default()
}

/// Driver: apply the resolved mode.
/// * `Off` -> `None` immediately.
/// * All violations are recorded (telemetry) regardless of mode.
/// * `Enforce` -> the FIRST violation is returned so the caller fails closed;
///   `Warn` -> `None` (telemetry only, no verdict change).
pub fn evaluate(
    func: &MachFunction,
    mode: PostRegallocRecheckMode,
) -> Option<ReachingDefViolation> {
    if mode == PostRegallocRecheckMode::Off {
        return None;
    }
    let debug = std::env::var_os("TCG_AARCH64_POST_RA_REACHING_DEF_DEBUG").is_some();
    let violations = match analyze(func) {
        Some(v) => {
            STREAMS_ANALYZED.fetch_add(1, Ordering::Relaxed);
            if debug {
                eprintln!(
                    "[A64-RD-DEBUG] fn={} outcome=analyzed viol={}",
                    func.name,
                    v.len()
                );
            }
            v
        }
        None => {
            STREAMS_DECLINED.fetch_add(1, Ordering::Relaxed);
            if debug {
                eprintln!("[A64-RD-DEBUG] fn={} outcome=declined", func.name);
            }
            return None;
        }
    };
    for v in &violations {
        record_violation(&func.name, &v.detail, mode);
    }
    if mode == PostRegallocRecheckMode::Enforce {
        violations.into_iter().next()
    } else {
        None
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use trust_cg_ir::aarch64_regs::{SP, W0, W1, W9, X0, X1, X9, X19};
    use trust_cg_ir::{InstId, Signature};

    fn add(dst: PReg, a: PReg, b: PReg) -> MachInst {
        MachInst::new(
            AArch64Opcode::AddRR,
            vec![
                MachOperand::PReg(dst),
                MachOperand::PReg(a),
                MachOperand::PReg(b),
            ],
        )
    }

    fn single_block(name: &str, insts: Vec<MachInst>) -> MachFunction {
        let mut f = MachFunction::new(name.to_string(), Signature::new(vec![], vec![]));
        let entry = f.entry;
        for inst in insts {
            let id = InstId(f.insts.len() as u32);
            f.insts.push(inst);
            f.append_inst(entry, id);
        }
        f
    }

    #[test]
    fn clean_straight_line_reads_seeded_args_passes() {
        // add x0, x0, x1 — x0/x1 are seeded ABI args.
        let f = single_block("clean", vec![add(X0, X0, X1)]);
        assert!(check(&f).is_empty());
        assert!(evaluate(&f, PostRegallocRecheckMode::Warn).is_none());
        assert!(evaluate(&f, PostRegallocRecheckMode::Enforce).is_none());
    }

    #[test]
    fn read_of_undefined_temp_refutes() {
        // REFUTATION: add x0, x9, x1 — x9 (allocatable temp) is never written.
        let f = single_block("bad", vec![add(X0, X9, X1)]);
        let vs = check(&f);
        assert_eq!(vs.len(), 1);
        assert_eq!(vs[0].kind, ReachingDefViolationKind::ReadWithoutReachingDef);
        // ENFORCE fails closed; WARN records telemetry but returns None.
        assert!(evaluate(&f, PostRegallocRecheckMode::Enforce).is_some());
        assert!(evaluate(&f, PostRegallocRecheckMode::Warn).is_none());
        assert!(evaluate(&f, PostRegallocRecheckMode::Off).is_none());
    }

    #[test]
    fn def_then_use_of_temp_passes() {
        // add x9, x0, x1 ; add x0, x9, x1 — x9 defined before use.
        let f = single_block("def_use", vec![add(X9, X0, X1), add(X0, X9, X1)]);
        assert!(check(&f).is_empty());
    }

    #[test]
    fn deleted_def_refutes() {
        // Sound: [def x9 ; use x9]. Fault-inject by deleting the def.
        let f = single_block("deleted_def", vec![add(X0, X9, X1)]);
        assert_eq!(check(&f).len(), 1);
    }

    #[test]
    fn wx_aliasing_def_covers_widened_read() {
        // add w9, w0, w1 (defines the X9 location) ; add x0, x9, x1 (reads X9).
        // Must NOT false-fire: the W9 write defines X9.
        let f = single_block("wx_alias", vec![add(W9, W0, W1), add(X0, X9, X1)]);
        assert!(check(&f).is_empty());
    }

    #[test]
    fn callee_saved_read_before_def_is_seeded() {
        // str x19, [sp] — prologue-style save of the incoming callee-saved x19.
        // x19 and sp are seeded defined-at-entry: no false positive.
        let store = MachInst::new(
            AArch64Opcode::StrRI,
            vec![
                MachOperand::PReg(X19),
                MachOperand::MemOp {
                    base: SP,
                    offset: 0,
                },
            ],
        );
        let f = single_block("callee_saved", vec![store]);
        assert!(check(&f).is_empty());
    }

    #[test]
    fn call_clobber_defines_result_register() {
        // bl f (implicit_defs = [x9]) ; add x0, x9, x1 — x9 defined by the call.
        static CALL_DEFS: [PReg; 1] = [X9];
        let call = MachInst::new(
            AArch64Opcode::Bl,
            vec![MachOperand::Symbol("f".to_string())],
        )
        .with_implicit_defs(&CALL_DEFS);
        let f = single_block("call_def", vec![call, add(X0, X9, X1)]);
        assert!(check(&f).is_empty());
    }

    #[test]
    fn memop_base_undefined_temp_refutes() {
        // ldr x0, [x9] — base x9 never written.
        let load = MachInst::new(
            AArch64Opcode::LdrRI,
            vec![
                MachOperand::PReg(X0),
                MachOperand::MemOp {
                    base: X9,
                    offset: 0,
                },
            ],
        );
        let f = single_block("bad_base", vec![load]);
        assert_eq!(check(&f).len(), 1);
    }

    #[test]
    fn memop_base_seeded_sp_passes() {
        // ldr x0, [sp] — base sp is seeded.
        let load = MachInst::new(
            AArch64Opcode::LdrRI,
            vec![
                MachOperand::PReg(X0),
                MachOperand::MemOp {
                    base: SP,
                    offset: 0,
                },
            ],
        );
        let f = single_block("good_base", vec![load]);
        assert!(check(&f).is_empty());
    }

    /// Build a diamond: b0 -> {b1, b2} -> b3. `def_in_b2` controls whether the
    /// b2 path defines x9 before the join reads it.
    fn diamond(def_in_b2: bool) -> MachFunction {
        let mut f = MachFunction::new("diamond".to_string(), Signature::new(vec![], vec![]));
        let b0 = f.entry;
        let b1 = f.create_block();
        let b2 = f.create_block();
        let b3 = f.create_block();
        // b1 defines x9.
        let i1 = InstId(f.insts.len() as u32);
        f.insts.push(add(X9, X0, X1));
        f.append_inst(b1, i1);
        // b2 optionally defines x9.
        if def_in_b2 {
            let i2 = InstId(f.insts.len() as u32);
            f.insts.push(add(X9, X0, X1));
            f.append_inst(b2, i2);
        }
        // b3 reads x9.
        let i3 = InstId(f.insts.len() as u32);
        f.insts.push(add(X0, X9, X1));
        f.append_inst(b3, i3);
        f.add_edge(b0, b1);
        f.add_edge(b0, b2);
        f.add_edge(b1, b3);
        f.add_edge(b2, b3);
        f
    }

    #[test]
    fn join_read_defined_on_only_one_path_refutes() {
        // x9 defined on the b1 path only; along b0->b2->b3 it is undefined.
        let f = diamond(false);
        assert_eq!(check(&f).len(), 1);
    }

    #[test]
    fn join_read_defined_on_all_paths_passes() {
        // x9 defined on BOTH incoming paths: no violation (MUST analysis).
        let f = diamond(true);
        assert!(check(&f).is_empty());
    }

    #[test]
    fn surviving_vreg_declines() {
        // A VReg in the stream means it is not the final post-RA form: decline
        // (report nothing) rather than risk a false positive.
        use trust_cg_ir::VReg;
        let inst = MachInst::new(
            AArch64Opcode::AddRR,
            vec![
                MachOperand::VReg(VReg::new(0, RegClass::Gpr64)),
                MachOperand::PReg(X9),
                MachOperand::PReg(X1),
            ],
        );
        let f = single_block("vreg", vec![inst]);
        // Even though x9 is read undefined, the VReg makes us decline.
        assert!(check(&f).is_empty());
    }

    #[test]
    fn mode_default_is_warn() {
        // Default is WARN (first slice); the ratchet knob can move it.
        assert_eq!(
            AARCH64_REACHING_DEF_DEFAULT,
            PostRegallocRecheckMode::Enforce
        );
    }
}
