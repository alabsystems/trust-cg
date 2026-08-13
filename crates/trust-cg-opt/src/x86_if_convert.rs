// trust-cg-opt - x86-64 if-conversion (OPT-11): value-select diamond -> CMOVcc
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! OPT-11: x86-64 if-conversion of short, side-effect-free value-select
//! diamonds into branchless `CMOVcc`.
//!
//! # The shape converted (v1 movs + v2 flag-free computed arms)
//!
//! The x86 ISel lowers `let m = if c { a } else { b }` (a rustc `SwitchInt`,
//! never a `Select`) as a control-flow DIAMOND whose two arm blocks each copy
//! their contribution into a shared block-parameter merge vreg `m`
//! (`define_block_params` / edge copies — see the ADR
//! `docs/adr-opt-ir-universe-2026-07-02.md` §2c):
//!
//! ```text
//!   header:                       header:
//!     ... <cond>, cmp/test ...       ... <cond>, cmp/test ...   (flag-setter kept)
//!     jcc  cc, T          ===>        mov    m, a-val           (default = taken value)
//!     jmp  F                          cmovcc inv(cc), m, b-val  (overwrite on !cc)
//!   T: mov m, a-val; jmp J            jmp    J
//!   F: mov m, b-val; jmp J          J: ... uses m ...
//!   J: ... uses m ...
//! ```
//!
//! The branch (a data-dependent, often-mispredicted `jcc`) becomes a single
//! flag-dependent `cmovcc`, and the two arm blocks are deleted.
//!
//! # Why this is verdict-preserving BY CONSTRUCTION (bounded speculation)
//!
//! This pass converts ONLY diamonds whose arms carry NOTHING unsafe to
//! speculate. Two arm shapes are admitted:
//!
//! * **v1 — pure value selects**: each arm is a chain of plain register/
//!   immediate MOVs whose net effect is to copy ONE already-available register
//!   value into the merge vreg. Nothing is hoisted; the two selected values are
//!   already live at the header.
//! * **v2 — flag-free COMPUTED arms**: an arm may additionally compute its
//!   contribution with `LEA`/`LeaSib` (address arithmetic — never dereferences,
//!   never faults) and `MOV r, imm` (`MovRI`). These ops are, on x86,
//!   **flag-free and non-faulting and touch no memory**, so — unlike an `ADD`/
//!   `SUB`/`SHR`/`IMUL` (which write RFLAGS) or a load/store (which can fault) —
//!   they can be SPECULATED: executed unconditionally in the header BEFORE the
//!   `mov`/`cmovcc`, on both paths, without observably changing the program.
//!   The arm's final value (now header-defined) becomes the `cmovcc` source.
//!
//! Either way the conversion is sound because:
//!
//! * **No trapping op is speculated** (no loads, div, store, or memory — the
//!   `[TCG-PTRSEL-STORE]` / idiv-speculation hazards the roadmap OPT-11 spec
//!   calls out cannot arise: arms with any load/store/call/div/flag-writing op
//!   are rejected; `LEA` computes an address ARITHMETICALLY and never
//!   dereferences, so it cannot fault even when its `base`/`index` are garbage
//!   on the not-taken path). Verified per-op through `x86_opcode_effect`
//!   (must be `MemoryEffect::Pure`).
//! * **No RFLAGS hazard** — every inserted/hoisted op is flag-free
//!   (`!x86_writes_flags`), so the `cmovcc` reads exactly the flags the deleted
//!   `jcc` would have read (the flag-setter in the header is untouched and still
//!   the most recent flag write before the select). x86 ALU ops write RFLAGS
//!   (ADR §2c#2), which is *precisely* why they stay out of scope — a
//!   speculated `ADD`/`SHR`/`IMUL` between the flag-setter and the `cmovcc`
//!   would corrupt the condition.
//! * **No clobber of a live value** — a hoisted op's def is an SSA vreg defined
//!   ONLY inside its arm (this pass runs pre-regalloc; the multi-def guard in
//!   `find_one` rejects any vreg defined in BOTH arms other than the merge), so
//!   hoisting its definition to the header cannot overwrite any value live on
//!   the other path or a `cmovcc` input. The arm's merge-write is redirected to
//!   a FRESH per-arm vreg so the merge stays single-def.
//!
//! The one semantic step — that `inv(cc)` branches on EXACTLY the complement of
//! `cc` (the #3-trap-carriers "wrong-cc silently inverts the select" class) —
//! is NOT assumed. Every applied inversion is admitted by the
//! [`CcInversionAdmit`] callback; the production wiring backs it with
//! `trust_cg_verify::pass_validators::CondCodeInversionValidator`, an exhaustive
//! equivalence proof over all 32 RFLAGS states minted through the fail-closed
//! `CertifiedPassChain` (the SAME validator OPT-8's branch layout uses). A
//! rejected inversion leaves the correct two-branch diamond in place — admission
//! is an optimization gate, never a soundness gate.
//!
//! Downstream, every existing fail-closed stage (carrier hygiene, glue-pass
//! validator, regalloc + its validators, per-instruction certs — `CMOVcc`/`
//! CMOVcc32` are inside the cert-covered surface and reconstructed lane-exactly,
//! `x86_64_function_verifier.rs`, decode-check) re-verifies the rewritten
//! function exactly as it would any ISel output.
//!
//! # Composition with OPT-8 (branch layout)
//!
//! If-conversion runs BEFORE `X86BranchLayout`: it deletes the diamond's branch
//! entirely, so branch layout never sees those blocks (it operates on whatever
//! two-way exits survive). The two passes are disjoint on any given block.
//!
//! # Deferred (with reason)
//!
//! * **Flag-WRITING computed arms** (the benchmark diamonds — `p2_collatz`'s
//!   `c>>1` [SHR, writes RFLAGS] vs `c*3+1` [IMUL+ADD, both write RFLAGS; the
//!   isel emits `imul $3` not `lea`], `b1_mispredict`'s `rotate_left` triangle).
//!   Speculating an arm's flag-writing ALU work would corrupt the `cmovcc`
//!   condition; hoisting it needs the header flag-setter re-materialized after
//!   the speculation, the mutation-heavy territory the ADR marks port-first.
//!   Rejected here (any `x86_writes_flags` op in an arm fails the arm).
//! * **Multi-value merges, i128/XMM merges, loop-carried merges** (join with a
//!   back-edge predecessor). Rejected structurally.

use std::collections::HashMap;

use trust_cg_ir::regs::{RegClass, VReg};
use trust_cg_ir::x86_64_ops::{X86CondCode, X86Opcode};
use trust_cg_lower::instructions::Block;
use trust_cg_lower::{X86ISelBlock, X86ISelFunction, X86ISelInst, X86ISelOperand};

use crate::effects::{MemoryEffect, x86_opcode_effect, x86_writes_flags};
use crate::generic_branch_layout::analyze_branch_layout;
use crate::mach_view::predecessor_map;
use crate::x86_branch_layout::CcInversionAdmit;
use crate::x86_pass_manager::X86MachinePass;

/// x86-64 if-conversion pass (OPT-11). See the module docs.
pub struct X86IfConvert {
    admit_inversion: CcInversionAdmit,
    /// Number of diamonds converted by the most recent [`run`] invocation
    /// (diagnostics/tests only).
    ///
    /// [`run`]: X86MachinePass::run
    pub last_run_conversions: usize,
}

impl X86IfConvert {
    /// Create the pass with the given inversion-admission callback.
    pub fn new(admit_inversion: CcInversionAdmit) -> Self {
        Self {
            admit_inversion,
            last_run_conversions: 0,
        }
    }
}

/// A fully-validated conversion plan for one value-select diamond.
struct DiamondPlan {
    header: Block,
    /// The taken arm (`jcc cc` target) — deleted after the rewrite.
    taken_arm: Block,
    /// The taken arm's resolved value (the `cmovcc` default source).
    taken_val: X86ISelOperand,
    /// Flag-free computed body of the taken arm to hoist into the header before
    /// the `mov`/`cmovcc` (empty for a pure mov-alias arm). See [`ArmSpec`].
    taken_hoist: Vec<X86ISelInst>,
    /// The not-taken arm (`jmp` target) — deleted after the rewrite.
    nottaken_arm: Block,
    /// The not-taken arm's resolved value (the `cmovcc` overwrite source).
    nottaken_val: X86ISelOperand,
    /// Flag-free computed body of the not-taken arm to hoist into the header.
    nottaken_hoist: Vec<X86ISelInst>,
    /// The reconvergence (join) block.
    join: Block,
    /// The shared block-parameter merge vreg written by both arms.
    merge: VReg,
    /// Condition code carried by the header's `jcc`.
    cc: X86CondCode,
    /// The proven complement of `cc`, written into the emitted `cmovcc`.
    inverted_cc: X86CondCode,
    /// `(MovRR|MovRR32, Cmovcc|Cmovcc32)` selected from the merge width.
    mov_op: X86Opcode,
    cmov_op: X86Opcode,
    /// The function's `next_vreg` after minting fresh output vregs for any
    /// hoisted computed arm — written back to `func.next_vreg` in `apply` so the
    /// fresh ids stay unique across later conversions.
    next_vreg: u32,
    /// v3 (flag-writing arms): the guard flag-setter to RE-EMIT after the
    /// hoisted arm bodies (whose ALU flag-writes clobbered the header's
    /// original flags) and immediately before the `mov`/`cmovcc`, so the cmov
    /// reads the same predicate the deleted `jcc` did. `None` for v1/v2 arms
    /// (all flag-free — the original header flag-setter still stands).
    guard_refresh: Option<X86ISelInst>,
}

/// If `inst` is a plain register/immediate move (`mov d, s` with a VReg `d`),
/// return `(d, s)`. Rejects (returns `None` for) every other opcode — including
/// moves writing a physical register, extends (`movzx`/`movsx`, which COMPUTE),
/// and anything with side effects, memory, flags, or a fixed-register clobber.
fn plain_reg_mov(inst: &X86ISelInst) -> Option<(VReg, &X86ISelOperand)> {
    match inst.opcode {
        X86Opcode::MovRR | X86Opcode::MovRR32 | X86Opcode::MovRI => {
            if let [X86ISelOperand::VReg(dst), src] = inst.operands.as_slice() {
                Some((*dst, src))
            } else {
                None
            }
        }
        _ => None,
    }
}

/// The vregs defined by an all-plain-mov arm body (excluding its terminator).
/// Returns `None` if the arm holds any instruction other than a plain
/// register/immediate move followed by the terminating `Jmp` (i.e. anything
/// computed, memory, call, trapping, flag-writing, or physical-register write).
fn arm_mov_defs(func: &X86ISelFunction, arm: Block) -> Option<Vec<VReg>> {
    let block = func.blocks.get(&arm)?;
    let n = block.insts.len();
    if n < 2 {
        // Must have at least one mov (defining the merge) plus the Jmp.
        return None;
    }
    // Terminator must be exactly `Jmp J`.
    let last = &block.insts[n - 1];
    if last.opcode != X86Opcode::Jmp {
        return None;
    }
    let mut defs = Vec::new();
    for inst in &block.insts[..n - 1] {
        let (dst, _) = plain_reg_mov(inst)?;
        defs.push(dst);
    }
    Some(defs)
}

/// The vregs defined by an all-SPECULATABLE arm body (excluding its terminator).
/// Generalizes [`arm_mov_defs`] to also admit flag-free `LEA`/`LeaSib`/`MovRI`
/// computes (via [`speculatable_def`]). Returns `None` if the arm holds any
/// instruction this pass cannot speculate (flag-writing ALU, memory, call, div,
/// trapping, or a physical-register write) or lacks the terminating `Jmp`.
///
/// Used only to identify the merge vreg (the unique vreg defined in BOTH arms);
/// the per-arm hoist/source decision is made by [`analyze_arm_spec`].
fn arm_speculatable_defs_impl(
    func: &X86ISelFunction,
    arm: Block,
    allow_flag_write: bool,
) -> Option<Vec<VReg>> {
    let block = func.blocks.get(&arm)?;
    let n = block.insts.len();
    if n < 2 {
        return None;
    }
    if block.insts[n - 1].opcode != X86Opcode::Jmp {
        return None;
    }
    let mut defs = Vec::new();
    for inst in &block.insts[..n - 1] {
        defs.push(speculatable_def_impl(inst, allow_flag_write)?);
    }
    Some(defs)
}

/// Resolve the register value an all-plain-mov arm copies into `merge`, tracing
/// through the arm's internal mov chain to a header-available operand.
///
/// Returns the resolved value only when it is a VReg NOT defined inside the arm
/// (hence dominating the header's end, since the arm's sole predecessor is the
/// header) whose reg class matches `merge`. Immediates, physical registers,
/// wrong-class values, and `merge` itself all yield `None` (v1 scope /
/// degenerate-select guard).
fn resolve_arm_value(func: &X86ISelFunction, arm: Block, merge: VReg) -> Option<X86ISelOperand> {
    let block = func.blocks.get(&arm)?;
    let n = block.insts.len();
    // Last-write-wins map of arm-internal mov definitions.
    let mut def: HashMap<VReg, X86ISelOperand> = HashMap::new();
    for inst in &block.insts[..n - 1] {
        let (dst, src) = plain_reg_mov(inst)?;
        def.insert(dst, src.clone());
    }
    let mut cur = def.get(&merge)?.clone();
    // Trace through arm-internal aliases; bounded by the arm length to defend
    // against any cyclic definition (impossible in SSA, cheap to guard).
    for _ in 0..=n {
        match &cur {
            X86ISelOperand::VReg(v) if def.contains_key(v) => {
                cur = def.get(v).cloned()?;
            }
            _ => break,
        }
    }
    match cur {
        X86ISelOperand::VReg(v)
            if !def.contains_key(&v) && v != merge && v.class == merge.class =>
        {
            Some(X86ISelOperand::VReg(v))
        }
        _ => None,
    }
}

/// The `(mov, cmov)` opcode pair for a merge vreg's width, or `None` for classes
/// this pass does not handle (i128 pairs, XMM/float selects).
fn width_ops(class: RegClass) -> Option<(X86Opcode, X86Opcode)> {
    match class {
        RegClass::Gpr64 => Some((X86Opcode::MovRR, X86Opcode::Cmovcc)),
        RegClass::Gpr32 => Some((X86Opcode::MovRR32, X86Opcode::Cmovcc32)),
        _ => None,
    }
}

/// The `LEA`/`MovRI`-immediate opcodes a v2 computed arm may hoist-and-speculate.
///
/// EVERY member is, on x86-64, **flag-free** (`!x86_writes_flags`, verified in
/// the `speculatable_op_defs_flag_free_pure` test) AND **non-faulting +
/// memory-free** (`x86_opcode_effect == Pure`). `LEA` computes an address by
/// register arithmetic and NEVER dereferences memory, so it cannot fault even
/// when speculated on the not-taken path with arbitrary `base`/`index` inputs;
/// `MovRI` materializes an immediate. Neither touches RFLAGS, so hoisting them
/// between the header's flag-setter and the emitted `cmovcc` leaves the
/// condition the `cmovcc` reads exactly as the deleted `jcc` would have read it.
/// Diagnostic: why a candidate diamond was rejected. `TCG_IFCONV_TRACE=1`.
fn ic_trace(why: &str, msg: String) {
    if std::env::var_os("TCG_IFCONV_TRACE").is_some() {
        eprintln!("[ifconv] DECLINE({why}) {msg}");
    }
}

fn is_speculatable_compute_op(opcode: X86Opcode) -> bool {
    matches!(
        opcode,
        X86Opcode::Lea | X86Opcode::LeaSib | X86Opcode::MovRI
    )
}

/// v3: additionally-admissible arm-body ops that WRITE FLAGS but are otherwise
/// safe to speculate — non-faulting, memory-free, register-def ALU. Admitted
/// ONLY when the caller can re-establish the guard's flags immediately before
/// the `cmovcc` (see `guard_refresh`). Excludes DIV/IDIV (fault on 0), all
/// memory/call ops, and the fixed-register-clobbering wide MUL/IMUL forms.
fn is_flagwriting_speculatable_op(opcode: X86Opcode) -> bool {
    matches!(
        opcode,
        X86Opcode::AddRR
            | X86Opcode::AddRI
            | X86Opcode::SubRR
            | X86Opcode::SubRI
            | X86Opcode::AndRR
            | X86Opcode::AndRI
            | X86Opcode::OrRR
            | X86Opcode::OrRI
            | X86Opcode::XorRR
            | X86Opcode::XorRI
            | X86Opcode::ShlRI
            | X86Opcode::ShrRI
            | X86Opcode::SarRI
            | X86Opcode::ShlRR
            | X86Opcode::ShrRR
            | X86Opcode::SarRR
            | X86Opcode::ImulRR
            | X86Opcode::ImulRRI
            | X86Opcode::Neg
            | X86Opcode::Inc
            | X86Opcode::Dec
            // `RolRI` is pure, non-trapping and writes flags — the exact
            // sibling of the `ShlRI`/`ShrRI`/`SarRI` entries above. It was
            // simply missed when the opcode was added. On its own this entry
            // fires ZERO times: the diamond it unblocks (b1_mispredict's
            // `if s & 6 == 2 { acc = acc.rotate_left(7) }`) is rejected
            // STRUCTURALLY first, because its taken arm is a two-block chain
            // and `find_one` requires each arm to be one block. It only pays
            // together with `X86BlockMerge`.
            | X86Opcode::RolRI
    )
}

/// A pure flag-SETTER whose inputs are all VReg/Imm (re-emittable to refresh
/// the guard's flags). Its VReg inputs are returned so the caller can verify
/// none is clobbered by the hoisted arm bodies.
fn guard_flag_setter_reads(inst: &X86ISelInst) -> Option<Vec<VReg>> {
    if !matches!(
        inst.opcode,
        X86Opcode::CmpRR
            | X86Opcode::CmpRI
            | X86Opcode::CmpRI8
            | X86Opcode::TestRR
            | X86Opcode::TestRI
            | X86Opcode::BtRI
    ) {
        return None;
    }
    let mut reads = Vec::new();
    for op in &inst.operands {
        match op {
            X86ISelOperand::VReg(v) => reads.push(*v),
            X86ISelOperand::Imm(_) | X86ISelOperand::CondCode(_) => {}
            // A memory/PReg operand is out of scope (may alias / be clobbered).
            _ => return None,
        }
    }
    Some(reads)
}

/// The single VReg an arm-body instruction DEFINES (its destination), if the
/// instruction is one this pass may speculate.
///
/// Admits exactly the flag-free, non-faulting, memory-free, register-def ops:
/// * a plain register/immediate MOV (`plain_reg_mov`), or
/// * a `LEA`/`LeaSib`/`MovRI` whose destination is a VReg (operand 0).
///
/// Returns `None` — rejecting the whole arm — for ANY other instruction:
/// * a flag-writing op (`ADD`/`SUB`/`SHR`/`IMUL`/…): `x86_writes_flags` guard;
/// * a memory op (load/store) or call/div: `x86_opcode_effect != Pure` guard;
/// * a physical-register or non-VReg destination.
///
/// The two guards are belt-and-suspenders over the opcode allow-list: a future
/// opcode wrongly added to `is_speculatable_compute_op` that writes flags or
/// touches memory is still rejected here (fail-safe).
fn speculatable_def(inst: &X86ISelInst) -> Option<VReg> {
    speculatable_def_impl(inst, false)
}

/// [`speculatable_def`] that also admits the flag-writing ALU ops
/// ([`is_flagwriting_speculatable_op`]) when `allow_flag_write`. Flag-writing
/// arms are only sound if the caller re-emits the guard flag-setter after the
/// hoisted bodies (see the v3 path in `find_one` / `apply`).
fn speculatable_def_impl(inst: &X86ISelInst, allow_flag_write: bool) -> Option<VReg> {
    if let Some((dst, _)) = plain_reg_mov(inst) {
        return Some(dst);
    }
    let flagwriting = allow_flag_write && is_flagwriting_speculatable_op(inst.opcode);
    if !is_speculatable_compute_op(inst.opcode) && !flagwriting {
        return None;
    }
    // Every admitted op must be non-faulting and memory-pure. Its flag effect
    // is fine only when the caller re-emits the guard flag-setter after the
    // hoisted bodies (the v3 `allow_flag_write` contract).
    if x86_opcode_effect(inst.opcode) != MemoryEffect::Pure {
        return None;
    }
    if !allow_flag_write && x86_writes_flags(inst.opcode) {
        return None;
    }
    // The destination (operand 0) must be a VReg; a physical-register def would
    // clobber an ABI/fixed register and is out of scope.
    match inst.operands.first() {
        Some(X86ISelOperand::VReg(dst)) => Some(*dst),
        _ => None,
    }
}

/// A per-arm speculation plan: the computed body to hoist into the header (empty
/// for a pure mov-alias arm) plus the `cmovcc`-source operand.
struct ArmSpec {
    /// Arm-body instructions to execute UNCONDITIONALLY in the header before the
    /// `mov`/`cmovcc`, in original order, with the write to `merge` redirected to
    /// `source`'s fresh vreg so the merge stays single-def. Empty when the arm is
    /// a pure mov-alias whose value is already header-available.
    hoist: Vec<X86ISelInst>,
    /// The VReg the `cmovcc` reads for this arm — either a header-available value
    /// (mov-alias fast path) or the fresh vreg the hoisted body defines.
    source: X86ISelOperand,
}

/// Analyze one arm into an [`ArmSpec`], or `None` if the arm is not convertible.
///
/// Two shapes succeed:
///
/// * **Pure mov-alias** — the arm is only plain movs and `merge` traces back to
///   a header-available VReg. `hoist` is empty; `source` is that VReg. (This is
///   the v1 fast path; it never hoists, matching prior behavior exactly.)
/// * **Flag-free computed** — the arm contains at least one `LEA`/`LeaSib`/
///   `MovRI`. The whole arm body is hoisted (every inst must pass
///   `speculatable_def`), the write to `merge` is redirected to a FRESH vreg
///   `out` (minted from `next_vreg`, threaded via `&mut`), and `source` is `out`.
///   The redirect keeps `merge` single-def after both arms hoist.
///
/// Both require the arm's contribution to land in a GPR of `merge`'s class (so
/// the `cmovcc` source width matches) and to differ from `merge` itself.
fn analyze_arm_spec(
    func: &X86ISelFunction,
    arm: Block,
    merge: VReg,
    next_vreg: &mut u32,
) -> Option<ArmSpec> {
    // Fast path: a pure mov-alias arm keeps the allocation-free v1 behavior.
    if arm_mov_defs(func, arm).is_some()
        && let Some(source) = resolve_arm_value(func, arm, merge)
    {
        return Some(ArmSpec {
            hoist: Vec::new(),
            source,
        });
    }

    // v2: flag-free computed arm. Every body instruction must be speculatable.
    let block = func.blocks.get(&arm)?;
    let n = block.insts.len();
    if n < 2 || block.insts[n - 1].opcode != X86Opcode::Jmp {
        return None;
    }
    let body = &block.insts[..n - 1];
    // Reject a pure mov-only body here: it either resolved above (fast path) or
    // is a degenerate select the fast path already declined; without a computed
    // op there is nothing new to admit and hoisting movs would only add churn.
    let mut has_compute = false;
    // Collect defs and verify each op is speculatable.
    let mut defs: Vec<VReg> = Vec::with_capacity(body.len());
    for inst in body {
        let dst = speculatable_def(inst)?;
        if is_speculatable_compute_op(inst.opcode) {
            has_compute = true;
        }
        defs.push(dst);
    }
    if !has_compute {
        return None;
    }
    // `merge` must be defined exactly once in this arm (its final contribution).
    // A second write to merge would make the redirect ambiguous.
    if defs.iter().filter(|&&d| d == merge).count() != 1 {
        return None;
    }
    // Every arm-internal def other than `merge` must be defined ONCE (SSA) — a
    // repeated non-merge def would mean a value is overwritten mid-arm, so
    // hoisting the whole body verbatim could reorder a def past a use. (SSA
    // guarantees this pre-regalloc; we check defensively.)
    for &d in &defs {
        if d != merge && defs.iter().filter(|&&x| x == d).count() != 1 {
            return None;
        }
    }

    // Mint a fresh vreg for the arm's output and redirect the merge-write to it.
    let out = VReg::new(*next_vreg, merge.class);
    *next_vreg += 1;
    let mut hoist = Vec::with_capacity(body.len());
    for inst in body {
        let mut cloned = inst.clone();
        // Redirect ONLY the destination write to `merge` (operand 0). Uses of
        // `merge` cannot occur (merge is the arm's output, defined once, not
        // read inside the arm), so no use-side rewrite is needed.
        if let Some(X86ISelOperand::VReg(d)) = cloned.operands.first()
            && *d == merge
        {
            cloned.operands[0] = X86ISelOperand::VReg(out);
        }
        hoist.push(cloned);
    }
    Some(ArmSpec {
        hoist,
        source: X86ISelOperand::VReg(out),
    })
}

/// v3 arm analyzer: like [`analyze_arm_spec`] but admits flag-writing ALU
/// bodies ([`speculatable_def_impl`] with `allow_flag_write`). Only sound when
/// the caller re-emits the guard flag-setter after the hoisted body (the
/// caller validates the guard's inputs are not among the arm's defs).
fn analyze_arm_spec_flagwrite(
    func: &X86ISelFunction,
    arm: Block,
    merge: VReg,
    next_vreg: &mut u32,
) -> Option<(ArmSpec, Vec<VReg>)> {
    let block = func.blocks.get(&arm)?;
    let n = block.insts.len();
    if n < 2 || block.insts[n - 1].opcode != X86Opcode::Jmp {
        return None;
    }
    let body = &block.insts[..n - 1];
    let mut defs: Vec<VReg> = Vec::with_capacity(body.len());
    let mut has_flagwrite = false;
    for inst in body {
        let dst = speculatable_def_impl(inst, true)?;
        if is_flagwriting_speculatable_op(inst.opcode) {
            has_flagwrite = true;
        }
        defs.push(dst);
    }
    // Only take this path when the arm actually contains a flag-writing op;
    // otherwise the flag-free analyzer already handled (or declined) it.
    if !has_flagwrite {
        return None;
    }
    if defs.iter().filter(|&&d| d == merge).count() != 1 {
        return None;
    }
    for &d in &defs {
        if d != merge && defs.iter().filter(|&&x| x == d).count() != 1 {
            return None;
        }
    }
    let out = VReg::new(*next_vreg, merge.class);
    *next_vreg += 1;
    let mut hoist = Vec::with_capacity(body.len());
    for inst in body {
        let mut cloned = inst.clone();
        if let Some(X86ISelOperand::VReg(d)) = cloned.operands.first()
            && *d == merge
        {
            cloned.operands[0] = X86ISelOperand::VReg(out);
        }
        hoist.push(cloned);
    }
    let all_defs: Vec<VReg> = defs
        .into_iter()
        .map(|d| if d == merge { out } else { d })
        .collect();
    Some((
        ArmSpec {
            hoist,
            source: X86ISelOperand::VReg(out),
        },
        all_defs,
    ))
}

/// True iff `target` is named by exactly one instruction-level `Block`
/// operand and by no out-of-line block-keyed side table.
///
/// [`predecessor_map`] is intentionally set-valued: two branches in the same
/// source block that target the same destination contribute one predecessor.
/// That is the right CFG abstraction, but it is not sufficient authority for
/// deleting an if-converted arm.  A switch lowering can emit several `Jcc`s in
/// one header that share a case target; rewriting only the terminal `jcc; jmp`
/// pair must not delete a block still named by an earlier branch.  Likewise a
/// jump table or EH record is a live reference even though it is not an
/// instruction `Block` operand.
///
/// `find_one` separately proves that the one instruction reference is the
/// terminal edge it plans to rewrite.  This helper closes the multiplicity and
/// side-table gaps before either arm can be deleted.
pub(crate) fn has_single_deletable_block_reference(func: &X86ISelFunction, target: Block) -> bool {
    let instruction_references = func
        .blocks
        .values()
        .flat_map(|block| &block.insts)
        .flat_map(|inst| &inst.operands)
        .filter(|operand| matches!(operand, X86ISelOperand::Block(block) if *block == target))
        .count();
    if instruction_references != 1 {
        return false;
    }

    if func
        .jump_tables
        .iter()
        .any(|table| table.targets.contains(&target))
    {
        return false;
    }

    !func
        .eh_info
        .landing_pads
        .iter()
        .any(|pad| pad.block == target)
        && !func
            .eh_info
            .call_sites
            .iter()
            .any(|site| site.call_block == target || site.landing_pad_block == target)
}

impl X86IfConvert {
    /// Search the current function state for ONE convertible value-select
    /// diamond and return its validated plan, or `None` when none remains.
    ///
    /// Re-derives every fact from the live IR (never a stale report), so it is
    /// safe to call in a loop that mutates the function between calls.
    fn find_one(&self, func: &X86ISelFunction) -> Option<DiamondPlan> {
        if func.block_order.len() < 4 {
            return None;
        }
        let report = analyze_branch_layout(func);
        if report.cond_then_jump_exits.is_empty() {
            return None;
        }
        let preds = predecessor_map(func);

        for exit in &report.cond_then_jump_exits {
            // The header ends in `jcc T; jmp F` with exactly one jcc target.
            let [taken_arm] = exit.cond_targets.as_slice() else {
                ic_trace(
                    "multi-cond-target",
                    format!("block={:?} targets={:?}", exit.block, exit.cond_targets),
                );
                continue;
            };
            let (taken_arm, nottaken_arm) = (*taken_arm, exit.jump_target);
            if taken_arm == nottaken_arm {
                continue; // degenerate two-way branch to one block
            }

            // Each arm's SOLE predecessor is the header.
            if preds.get(&taken_arm).map(Vec::as_slice) != Some(&[exit.block])
                || preds.get(&nottaken_arm).map(Vec::as_slice) != Some(&[exit.block])
            {
                ic_trace(
                    "arm-has-other-preds",
                    format!(
                        "hdr={:?} taken={:?} preds={:?} nottaken={:?} preds={:?}",
                        exit.block,
                        taken_arm,
                        preds.get(&taken_arm),
                        nottaken_arm,
                        preds.get(&nottaken_arm)
                    ),
                );
                continue;
            }

            // Each arm has exactly one successor, and they reconverge on the
            // SAME join block.
            let taken_succ = func.blocks.get(&taken_arm).map(|b| b.successors.clone());
            let nottaken_succ = func.blocks.get(&nottaken_arm).map(|b| b.successors.clone());
            let (Some([join_t]), Some([join_f])) =
                (taken_succ.as_deref(), nottaken_succ.as_deref())
            else {
                ic_trace(
                    "arm-not-single-successor",
                    format!(
                        "hdr={:?} taken={:?} succ={:?} nottaken={:?} succ={:?}",
                        exit.block, taken_arm, taken_succ, nottaken_arm, nottaken_succ
                    ),
                );
                continue;
            };
            if join_t != join_f {
                ic_trace(
                    "arms-do-not-reconverge",
                    format!(
                        "hdr={:?} join_t={:?} join_f={:?}",
                        exit.block, join_t, join_f
                    ),
                );
                continue;
            }
            let join = *join_t;
            // The join must be a clean 2-in reconvergence (exactly the two
            // arms) — this rejects loop headers / any back-edge or extra
            // predecessor whose merge value must NOT be if-converted.
            match preds.get(&join) {
                Some(p) if p.len() == 2 && p.contains(&taken_arm) && p.contains(&nottaken_arm) => {}
                _ => {
                    ic_trace(
                        "join-not-clean-2in",
                        format!(
                            "hdr={:?} join={:?} preds={:?}",
                            exit.block,
                            join,
                            preds.get(&join)
                        ),
                    );
                    continue;
                }
            }

            // Both arms are all-speculatable bodies (plain movs and/or flag-free
            // LEA/MovRI computes). The unique vreg defined in BOTH is the merge
            // (a second common def => a multi-value merge, out of scope). v3
            // additionally admits flag-writing ALU arms; the guard is re-emitted
            // after the hoists below. v3 is default-ON (opt out with
            // TCG_NO_X86_IFCONV_FLAGWRITE): the hoisted arms mint fresh output
            // vregs so the guard setter's SSA inputs are un-clobbered, and the
            // refreshed guard is placed immediately before the CMOVcc; validated
            // by the diamond corpus (aliasing / 3-level nesting / collatz across
            // O0/O2/O3) plus the full-suite differential.
            let allow_flag_write = std::env::var_os("TCG_NO_X86_IFCONV_FLAGWRITE").is_none();
            let (Some(taken_defs), Some(nottaken_defs)) = (
                arm_speculatable_defs_impl(func, taken_arm, allow_flag_write),
                arm_speculatable_defs_impl(func, nottaken_arm, allow_flag_write),
            ) else {
                ic_trace(
                    "arm-not-all-speculatable",
                    format!(
                        "hdr={:?} taken={:?}[{}] nottaken={:?}[{}]",
                        exit.block,
                        taken_arm,
                        func.blocks
                            .get(&taken_arm)
                            .map(|b| b
                                .insts
                                .iter()
                                .map(|i| format!("{:?}", i.opcode))
                                .collect::<Vec<_>>()
                                .join(","))
                            .unwrap_or_default(),
                        nottaken_arm,
                        func.blocks
                            .get(&nottaken_arm)
                            .map(|b| b
                                .insts
                                .iter()
                                .map(|i| format!("{:?}", i.opcode))
                                .collect::<Vec<_>>()
                                .join(","))
                            .unwrap_or_default()
                    ),
                );
                continue;
            };
            let common: Vec<VReg> = taken_defs
                .iter()
                .filter(|v| nottaken_defs.contains(v))
                .copied()
                .collect();
            let [merge] = common.as_slice() else {
                ic_trace(
                    "common-defs-not-one",
                    format!(
                        "hdr={:?} n={} taken={:?} nottaken={:?}",
                        exit.block,
                        common.len(),
                        taken_defs,
                        nottaken_defs
                    ),
                );
                continue;
            };
            let merge = *merge;

            let Some((mov_op, cmov_op)) = width_ops(merge.class) else {
                continue;
            };

            // Resolve each arm's contribution (mov-alias fast path OR flag-free
            // computed body to hoist). `next_vreg` mints fresh output vregs for
            // hoisted computed arms; snapshot it locally so both arms allocate
            // distinct ids and the real `func.next_vreg` is advanced in `apply`.
            let mut next_vreg = func.next_vreg;
            let mut guard_refresh: Option<X86ISelInst> = None;
            let (taken_spec, nottaken_spec) = match (
                analyze_arm_spec(func, taken_arm, merge, &mut next_vreg),
                analyze_arm_spec(func, nottaken_arm, merge, &mut next_vreg),
            ) {
                (Some(t), Some(nt)) => (t, nt),
                _ if allow_flag_write => {
                    // v3: at least one arm writes flags. Re-analyze BOTH arms
                    // allowing flag-writes and capture their full def sets so
                    // the guard-refresh's inputs can be proven un-clobbered.
                    let mut nv = func.next_vreg;
                    let ta = analyze_arm_spec(func, taken_arm, merge, &mut nv)
                        .map(|s| (s, Vec::new()))
                        .or_else(|| analyze_arm_spec_flagwrite(func, taken_arm, merge, &mut nv));
                    let na = analyze_arm_spec(func, nottaken_arm, merge, &mut nv)
                        .map(|s| (s, Vec::new()))
                        .or_else(|| analyze_arm_spec_flagwrite(func, nottaken_arm, merge, &mut nv));
                    let (Some((ts, tdefs)), Some((ns, ndefs))) = (ta, na) else {
                        continue;
                    };
                    // The guard flag-setter is the instruction immediately
                    // before `jcc; jmp`; it must be a pure flag-setter whose
                    // VReg inputs are NOT written by either arm (so re-emitting
                    // it recomputes the identical predicate).
                    let header = func.blocks.get(&exit.block)?;
                    let hn = header.insts.len();
                    if hn < 3 {
                        continue;
                    }
                    let setter = &header.insts[hn - 3];
                    let Some(reads) = guard_flag_setter_reads(setter) else {
                        continue;
                    };
                    if reads.iter().any(|v| tdefs.contains(v) || ndefs.contains(v)) {
                        continue;
                    }
                    // Also: the guard must NOT read `merge` (its old value is
                    // gone once the cmov writes it) — but the cmov writes merge
                    // AFTER the refreshed guard, so a guard reading merge would
                    // read the stale header value, not the arm result. Reject.
                    if reads.contains(&merge) {
                        continue;
                    }
                    guard_refresh = Some(setter.clone());
                    next_vreg = nv;
                    (ts, ns)
                }
                _ => continue,
            };
            let (taken_val, nottaken_val) = (taken_spec.source, nottaken_spec.source);
            // Both a pure mov-alias select to the SAME header value is a no-op;
            // computed arms always mint distinct fresh vregs so this only fires
            // for the degenerate mov-alias/mov-alias case.
            if taken_val == nottaken_val
                && taken_spec.hoist.is_empty()
                && nottaken_spec.hoist.is_empty()
            {
                continue; // both arms select the same value: no real branch
            }

            // Read the header's `jcc` condition code from the live IR.
            let header = func.blocks.get(&exit.block)?;
            let hn = header.insts.len();
            if hn < 2 {
                continue;
            }
            let jcc = &header.insts[hn - 2];
            let jmp = &header.insts[hn - 1];
            if jcc.opcode != X86Opcode::Jcc || jmp.opcode != X86Opcode::Jmp {
                continue;
            }
            let [X86ISelOperand::CondCode(cc), X86ISelOperand::Block(t)] = jcc.operands.as_slice()
            else {
                continue;
            };
            let [X86ISelOperand::Block(f)] = jmp.operands.as_slice() else {
                continue;
            };
            if *t != taken_arm || *f != nottaken_arm {
                continue;
            }

            // `preds` records predecessor BLOCKS, not edge multiplicity.  A
            // large switch header may target one arm from an earlier Jcc as
            // well as from this terminal pair; deleting that arm would leave
            // the earlier branch dangling.  Side-table references (jump table
            // and EH metadata) are equally live.  Require each arm's terminal
            // branch to be its one and only structural reference.
            if !has_single_deletable_block_reference(func, taken_arm)
                || !has_single_deletable_block_reference(func, nottaken_arm)
            {
                continue;
            }

            // The one semantic obligation: `inverted_cc` is the exact
            // complement of `cc`. A rejection skips this diamond.
            let inverted_cc = cc.invert();
            if !(self.admit_inversion)(*cc, inverted_cc) {
                continue;
            }

            return Some(DiamondPlan {
                header: exit.block,
                taken_arm,
                taken_val,
                taken_hoist: taken_spec.hoist,
                nottaken_arm,
                nottaken_val,
                nottaken_hoist: nottaken_spec.hoist,
                join,
                merge,
                cc: *cc,
                inverted_cc,
                mov_op,
                cmov_op,
                next_vreg,
                guard_refresh,
            });
        }
        None
    }

    /// Apply a validated plan: rewrite the header terminator into
    /// `mov; cmovcc; jmp J`, retarget the header's single successor to the join,
    /// and DELETE the two now-unreachable arm blocks.
    ///
    /// The arms MUST be deleted (not merely orphaned): each still defines the
    /// merge vreg, so leaving them makes `merge` a multi-def merge whose reaching
    /// def at the join is ambiguous — the regalloc's value-flow validator
    /// (correctly) rejects that. After deletion the merge has a SINGLE reaching
    /// def (the header's `cmovcc`) and the join's sole predecessor is the header.
    ///
    /// Deletion leaves a gap in the block-id space; [`run`] restores the gap-free
    /// `0..n` range the regalloc replay requires via
    /// [`renumber_blocks_contiguous`]. Deletion is reference-safe by
    /// construction: each arm's SOLE predecessor is the header (checked in
    /// `find_one`), and the header no longer references it, so no surviving
    /// instruction or successor edge points at a deleted arm.
    ///
    /// [`run`]: X86MachinePass::run
    fn apply(&self, func: &mut X86ISelFunction, plan: &DiamondPlan) {
        // Advance the function vreg counter past any fresh outputs minted for
        // hoisted computed arms (done before the block borrow to keep it simple).
        func.next_vreg = func.next_vreg.max(plan.next_vreg);

        let header = func
            .blocks
            .get_mut(&plan.header)
            .expect("planned header exists (checked in find_one)");
        let n = header.insts.len();
        // Drop the `jcc; jmp` pair; keep everything before it (the flag-setter
        // the cmov depends on stays exactly where it was — the hoisted computes
        // and mov/cmov below are ALL flag-free, so the cmov reads exactly the
        // flags the jcc would).
        header.insts.truncate(n - 2);

        // v2: SPECULATE each arm's flag-free computed body into the header,
        // unconditionally, BEFORE the mov/cmov. Safe because every hoisted op is
        // LEA/LeaSib/MovRI — non-faulting, memory-free, flag-free — and defines a
        // FRESH per-arm vreg (its merge-write redirected in `analyze_arm_spec`),
        // so it neither traps, clobbers a live value, nor disturbs RFLAGS. Order:
        // taken then not-taken; both are pure so relative order is immaterial.
        for inst in plan.taken_hoist.iter().chain(&plan.nottaken_hoist) {
            header.insts.push(inst.clone());
        }

        // v3: the hoisted arm bodies wrote flags, clobbering the header's
        // original guard flags. Re-emit the guard flag-setter (same inputs,
        // proven un-clobbered in `find_one`) so the `cmovcc` below reads the
        // identical predicate the deleted `jcc` did.
        if let Some(refresh) = &plan.guard_refresh {
            header.insts.push(refresh.clone());
        }

        // Complement encoding: default = taken value, overwrite with the
        // not-taken value on `inverted_cc`. Result = cc ? taken : nottaken.
        header.insts.push(X86ISelInst::new(
            plan.mov_op,
            vec![X86ISelOperand::VReg(plan.merge), plan.taken_val.clone()],
        ));
        header.insts.push(X86ISelInst::new(
            plan.cmov_op,
            vec![
                X86ISelOperand::VReg(plan.merge),
                plan.nottaken_val.clone(),
                X86ISelOperand::CondCode(plan.inverted_cc),
            ],
        ));
        header.insts.push(X86ISelInst::new(
            X86Opcode::Jmp,
            vec![X86ISelOperand::Block(plan.join)],
        ));
        header.successors = vec![plan.join];

        // Delete the two unreachable arm blocks. Reference-safe (see doc).
        func.blocks.remove(&plan.taken_arm);
        func.blocks.remove(&plan.nottaken_arm);
        func.block_order
            .retain(|b| *b != plan.taken_arm && *b != plan.nottaken_arm);

        // Structural self-check: header ends `mov; cmovcc(inverted); jmp J`,
        // targets exactly the join, and the arms are gone.
        debug_assert_eq!(plan.inverted_cc, plan.cc.invert());
        let header = func.blocks.get(&plan.header).expect("header present");
        let hn = header.insts.len();
        assert!(
            hn >= 3
                && header.insts[hn - 3].opcode == plan.mov_op
                && header.insts[hn - 2].opcode == plan.cmov_op
                && header.insts[hn - 1].opcode == X86Opcode::Jmp,
            "x86-if-convert: header terminator not rewritten as expected"
        );
        assert_eq!(
            header.successors,
            vec![plan.join],
            "x86-if-convert: header successor set not retargeted to the join"
        );
        assert!(
            !func.blocks.contains_key(&plan.taken_arm)
                && !func.blocks.contains_key(&plan.nottaken_arm),
            "x86-if-convert: arm blocks not deleted"
        );
    }
}

/// Renumber every block to a gap-free `0..n` range following `block_order`,
/// rewriting the block-map keys, `block_order`, per-block successors, every
/// `X86ISelOperand::Block` target, jump-table targets, and EH block metadata.
/// Restores the contiguous-id invariant the x86 regalloc replay requires after
/// if-conversion deletes arm blocks.
///
/// `block_order[0]` (the entry) maps to `Block(0)`, preserving the entry-first
/// convention. Reference-safe: every block a surviving block can reach is itself
/// in `block_order` (deleted arms are unreferenced), so no `Block` operand is
/// left dangling — an unmapped id (which cannot occur) is conservatively left
/// unchanged so the downstream contiguity gate fails closed rather than aliasing.
pub(crate) fn renumber_blocks_contiguous(func: &mut X86ISelFunction) {
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
        new_blocks.insert(remap[old_id], blk);
    }
    for table in &mut func.jump_tables {
        for target in &mut table.targets {
            if let Some(&new_target) = remap.get(target) {
                *target = new_target;
            }
        }
    }
    for pad in &mut func.eh_info.landing_pads {
        if let Some(&new_block) = remap.get(&pad.block) {
            pad.block = new_block;
        }
    }
    for site in &mut func.eh_info.call_sites {
        if let Some(&new_block) = remap.get(&site.call_block) {
            site.call_block = new_block;
        }
        if let Some(&new_block) = remap.get(&site.landing_pad_block) {
            site.landing_pad_block = new_block;
        }
    }
    func.blocks = new_blocks;
    func.block_order = (0..len as u32).map(Block).collect();
}

impl X86MachinePass for X86IfConvert {
    fn name(&self) -> &str {
        "x86-if-convert"
    }

    fn run(&mut self, func: &mut X86ISelFunction) -> bool {
        self.last_run_conversions = 0;
        // Convert diamonds one at a time, re-deriving from the mutated IR each
        // step (handles nested / sequential diamonds and keeps every fact
        // consistent with the live CFG). Bounded by the block count: each
        // conversion deletes two blocks.
        let budget = func.block_order.len() + 1;
        for _ in 0..budget {
            let Some(plan) = self.find_one(func) else {
                break;
            };
            self.apply(func, &plan);
            self.last_run_conversions += 1;
        }
        if self.last_run_conversions > 0 {
            // Deletions above left gaps in the block-id space; restore the
            // gap-free 0..n range the regalloc replay requires.
            renumber_blocks_contiguous(func);
            true
        } else {
            false
        }
    }
}

// ===========================================================================
// Tests
// ===========================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use trust_cg_lower::function::Signature;

    fn admit_exact(original: X86CondCode, inverted: X86CondCode) -> bool {
        original.invert() == inverted
    }

    fn admit_none(_original: X86CondCode, _inverted: X86CondCode) -> bool {
        false
    }

    /// A deliberately WRONG admission: accepts a cc paired with ITSELF (a
    /// non-complement). Models the #3-trap-carriers wrong-cc bug — the pass must
    /// never rewrite under it (find_one always pairs cc with cc.invert(), which
    /// this rejects, and if it somehow received cc==inverted it would be a
    /// silent select inversion).
    fn admit_identity_is_complement(original: X86CondCode, inverted: X86CondCode) -> bool {
        original == inverted
    }

    fn empty_sig() -> Signature {
        Signature {
            params: vec![],
            returns: vec![],
        }
    }

    fn vreg(id: u32) -> VReg {
        VReg::new(id, RegClass::Gpr64)
    }

    fn mov(dst: VReg, src: X86ISelOperand) -> X86ISelInst {
        X86ISelInst::new(X86Opcode::MovRR, vec![X86ISelOperand::VReg(dst), src])
    }

    fn jmp(target: Block) -> X86ISelInst {
        X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(target)])
    }

    fn jcc(cc: X86CondCode, target: Block) -> X86ISelInst {
        X86ISelInst::new(
            X86Opcode::Jcc,
            vec![X86ISelOperand::CondCode(cc), X86ISelOperand::Block(target)],
        )
    }

    /// The canonical value-select diamond (the sel_mini shape):
    ///
    /// ```text
    ///   b0: mov v1, rdi-ish; mov v2, rsi-ish; cmp v3, 0; jcc NE b1; jmp b2
    ///   b1: mov v4, v1; mov v5, v4; jmp b3        (taken: m=v5=v1)
    ///   b2: mov v6, v2; mov v5, v6; jmp b3        (not-taken: m=v5=v2)
    ///   b3: mov rax, v5; ret
    /// ```
    ///
    /// `v1`, `v2` are header-available; `v5` is the merge; the arms are pure
    /// mov chains.
    fn value_select_diamond(cc: X86CondCode) -> X86ISelFunction {
        let mut f = X86ISelFunction::new("sel".to_string(), empty_sig());
        let (b0, b1, b2, b3) = (Block(0), Block(1), Block(2), Block(3));
        for b in [b0, b1, b2, b3] {
            f.ensure_block(b);
        }
        f.next_vreg = 10;
        let (v1, v2, v3, v4, v5, v6) = (vreg(1), vreg(2), vreg(3), vreg(4), vreg(5), vreg(6));

        // header: define v1,v2; compute a cond into v3; cmp; jcc; jmp.
        f.push_inst(
            b0,
            X86ISelInst::new(
                X86Opcode::MovRI,
                vec![X86ISelOperand::VReg(v1), X86ISelOperand::Imm(7)],
            ),
        );
        f.push_inst(
            b0,
            X86ISelInst::new(
                X86Opcode::MovRI,
                vec![X86ISelOperand::VReg(v2), X86ISelOperand::Imm(9)],
            ),
        );
        f.push_inst(
            b0,
            X86ISelInst::new(
                X86Opcode::MovRI,
                vec![X86ISelOperand::VReg(v3), X86ISelOperand::Imm(1)],
            ),
        );
        f.push_inst(
            b0,
            X86ISelInst::new(
                X86Opcode::CmpRI,
                vec![X86ISelOperand::VReg(v3), X86ISelOperand::Imm(0)],
            ),
        );
        f.push_inst(b0, jcc(cc, b1));
        f.push_inst(b0, jmp(b2));

        f.push_inst(b1, mov(v4, X86ISelOperand::VReg(v1)));
        f.push_inst(b1, mov(v5, X86ISelOperand::VReg(v4)));
        f.push_inst(b1, jmp(b3));

        f.push_inst(b2, mov(v6, X86ISelOperand::VReg(v2)));
        f.push_inst(b2, mov(v5, X86ISelOperand::VReg(v6)));
        f.push_inst(b2, jmp(b3));

        f.push_inst(
            b3,
            X86ISelInst::new(X86Opcode::Ret, vec![X86ISelOperand::VReg(v5)]),
        );

        f.blocks.get_mut(&b0).unwrap().successors = vec![b1, b2];
        f.blocks.get_mut(&b1).unwrap().successors = vec![b3];
        f.blocks.get_mut(&b2).unwrap().successors = vec![b3];
        f
    }

    #[test]
    fn converts_value_select_diamond_to_cmov() {
        let mut f = value_select_diamond(X86CondCode::NE);
        let mut pass = X86IfConvert::new(admit_exact);
        assert!(pass.run(&mut f));
        assert_eq!(pass.last_run_conversions, 1);

        // The two arms are deleted; the surviving header + join are renumbered
        // to a gap-free 0..n range (old b0 -> Block(0), old b3 -> Block(1)).
        assert_eq!(f.block_order, vec![Block(0), Block(1)]);

        // Header now ends: mov v5, v1(taken); cmovcc(E=inv NE) v5, v2; jmp J.
        let h = &f.blocks[&Block(0)];
        let n = h.insts.len();
        assert_eq!(h.insts[n - 3].opcode, X86Opcode::MovRR);
        assert_eq!(
            h.insts[n - 3].operands,
            vec![X86ISelOperand::VReg(vreg(5)), X86ISelOperand::VReg(vreg(1))],
            "default = taken value (v1)"
        );
        assert_eq!(h.insts[n - 2].opcode, X86Opcode::Cmovcc);
        assert_eq!(
            h.insts[n - 2].operands,
            vec![
                X86ISelOperand::VReg(vreg(5)),
                X86ISelOperand::VReg(vreg(2)),
                X86ISelOperand::CondCode(X86CondCode::E),
            ],
            "overwrite with not-taken value (v2) on inverted cc"
        );
        assert_eq!(h.insts[n - 1].opcode, X86Opcode::Jmp);
        // The join (old b3) is renumbered to Block(1) and is the sole successor.
        assert_eq!(h.successors, vec![Block(1)]);
        assert_eq!(
            h.insts[n - 1].operands,
            vec![X86ISelOperand::Block(Block(1))]
        );
        // The flag-setter (cmp) the cmov depends on is preserved.
        assert!(h.insts.iter().any(|i| i.opcode == X86Opcode::CmpRI));
    }

    #[test]
    fn conversion_is_idempotent() {
        let mut f = value_select_diamond(X86CondCode::NE);
        let mut pass = X86IfConvert::new(admit_exact);
        assert!(pass.run(&mut f));
        // Second run: the diamond is gone (header ends in a plain jmp), nothing
        // to do — critical for the O3 fixpoint loop.
        assert!(!pass.run(&mut f));
        assert_eq!(pass.last_run_conversions, 0);
    }

    #[test]
    fn every_condition_code_pairs_with_its_complement() {
        use X86CondCode::*;
        for cc in [O, NO, B, AE, E, NE, BE, A, S, NS, P, NP, L, GE, LE, G] {
            let mut f = value_select_diamond(cc);
            let mut pass = X86IfConvert::new(admit_exact);
            assert!(pass.run(&mut f), "cc {cc:?} should convert");
            let h = &f.blocks[&Block(0)];
            let n = h.insts.len();
            let [_, _, X86ISelOperand::CondCode(emitted)] = h.insts[n - 2].operands.as_slice()
            else {
                panic!("cmov shape");
            };
            assert_eq!(*emitted, cc.invert(), "cmov uses the complement of {cc:?}");
        }
    }

    /// REFUTATION: an admission that rejects the (correct) complement pairing
    /// must leave the diamond untouched — the compile proceeds with the correct
    /// two-branch form. This is the fail-closed behavior for a wrong-cc.
    #[test]
    fn rejected_admission_skips_conversion() {
        let mut f = value_select_diamond(X86CondCode::NE);
        let before = f.block_order.clone();
        let mut pass = X86IfConvert::new(admit_none);
        assert!(!pass.run(&mut f), "no admission => no rewrite");
        assert_eq!(f.block_order, before, "diamond preserved");
        assert!(f.blocks.contains_key(&Block(1)) && f.blocks.contains_key(&Block(2)));
    }

    /// REFUTATION: an admission that only accepts the WRONG (identity, i.e.
    /// non-complement) pairing must also skip — the pass only ever offers the
    /// true complement, which this callback rejects. A pass bug that emitted the
    /// original cc as the "inverted" one (a silent select inversion) would
    /// likewise be rejected by the real validator-backed callback.
    #[test]
    fn wrong_complement_admission_skips_conversion() {
        let mut f = value_select_diamond(X86CondCode::L);
        let before = f.block_order.clone();
        let mut pass = X86IfConvert::new(admit_identity_is_complement);
        assert!(!pass.run(&mut f), "only a true complement may be admitted");
        assert_eq!(f.block_order, before);
    }

    /// A computed arm (an `add`, not a plain mov) is out of v1 scope but IS
    /// admitted by v3 (flag-writing arms, default-ON): the ADD is hoisted and
    /// the guard flag-setter re-emitted after it. `TCG_NO_X86_IFCONV_FLAGWRITE`
    /// restores the v1-only refusal.
    #[test]
    fn computed_add_arm_converts_under_v3() {
        let mut f = value_select_diamond(X86CondCode::NE);
        // Replace the taken arm's first mov with an ADD (a flag-writing compute).
        let b1 = f.blocks.get_mut(&Block(1)).unwrap();
        b1.insts[0] = X86ISelInst::new(
            X86Opcode::AddRI,
            vec![
                X86ISelOperand::VReg(vreg(4)),
                X86ISelOperand::VReg(vreg(1)),
                X86ISelOperand::Imm(1),
            ],
        );
        let mut pass = X86IfConvert::new(admit_exact);
        assert!(pass.run(&mut f), "a flag-writing ADD arm converts under v3");
        assert_eq!(pass.last_run_conversions, 1);
        let h = &f.blocks[&Block(0)];
        let n = h.insts.len();
        assert_eq!(h.insts[n - 2].opcode, X86Opcode::Cmovcc);
        assert_eq!(
            h.insts[n - 4].opcode,
            X86Opcode::CmpRI,
            "guard re-emitted before cmov"
        );
        let add_pos = h
            .insts
            .iter()
            .position(|i| i.opcode == X86Opcode::AddRI)
            .expect("add hoisted");
        assert!(
            add_pos < n - 4,
            "guard refreshed after the flag-writing add"
        );
    }

    /// A store in an arm (the `[TCG-PTRSEL-STORE]` hazard) is rejected.
    #[test]
    fn arm_with_store_is_not_converted() {
        let mut f = value_select_diamond(X86CondCode::NE);
        let b2 = f.blocks.get_mut(&Block(2)).unwrap();
        b2.insts[0] = X86ISelInst::new(
            X86Opcode::MovMR,
            vec![X86ISelOperand::VReg(vreg(2)), X86ISelOperand::VReg(vreg(6))],
        );
        let mut pass = X86IfConvert::new(admit_exact);
        assert!(!pass.run(&mut f), "arm store must never be if-converted");
    }

    /// A join reached by a THIRD predecessor (e.g. a loop back-edge) is not a
    /// clean diamond and must be left alone.
    #[test]
    fn join_with_extra_predecessor_is_not_converted() {
        let mut f = value_select_diamond(X86CondCode::NE);
        // Add a stray block b4 that also jumps to the join b3.
        let b4 = Block(4);
        f.ensure_block(b4);
        f.push_inst(b4, jmp(Block(3)));
        f.blocks.get_mut(&b4).unwrap().successors = vec![Block(3)];
        f.block_order.push(b4);
        // Make b4 reachable from the join so it is a real extra predecessor
        // edge in the pred map (edge b4 -> b3).
        let mut pass = X86IfConvert::new(admit_exact);
        assert!(
            !pass.run(&mut f),
            "join with 3 preds is not a clean diamond"
        );
    }

    /// A predecessor SET cannot prove that an arm has only one incoming EDGE:
    /// a switch-like header may name the same target from an earlier Jcc and
    /// again from its terminal diamond pair.  Rewriting only the terminal pair
    /// must not delete the still-referenced arm.
    #[test]
    fn arm_referenced_twice_by_same_header_is_not_converted() {
        let mut f = value_select_diamond(X86CondCode::NE);
        let header = f.blocks.get_mut(&Block(0)).unwrap();
        let terminal_pair = header.insts.len() - 2;
        header
            .insts
            .insert(terminal_pair, jcc(X86CondCode::E, Block(1)));

        let mut pass = X86IfConvert::new(admit_exact);
        assert!(
            !pass.run(&mut f),
            "an arm with another live branch reference must not be deleted"
        );
        assert_eq!(pass.last_run_conversions, 0);
        assert!(f.blocks.contains_key(&Block(1)));
        assert_eq!(
            f.blocks[&Block(0)]
                .insts
                .iter()
                .flat_map(|inst| &inst.operands)
                .filter(|operand| matches!(operand, X86ISelOperand::Block(Block(1))))
                .count(),
            2,
            "both same-header references stay intact"
        );
    }

    #[test]
    fn contiguous_renumber_rewrites_jump_table_and_eh_block_metadata() {
        use trust_cg_lower::function::{EhCallSite, EhLandingPad};
        use trust_cg_lower::x86_64_isel::X86JumpTableData;

        let mut f = X86ISelFunction::new("side_tables".to_string(), empty_sig());
        let (entry, old_target) = (Block(0), Block(2));
        f.ensure_block(entry);
        f.ensure_block(old_target);
        f.push_inst(entry, jmp(old_target));
        f.blocks.get_mut(&entry).unwrap().successors = vec![old_target];
        f.push_inst(old_target, X86ISelInst::new(X86Opcode::Ret, vec![]));
        f.jump_tables.push(X86JumpTableData {
            min_val: 0,
            targets: vec![old_target],
        });
        f.eh_info.landing_pads.push(EhLandingPad {
            block: old_target,
            catch_type_indices: vec![0],
            is_cleanup: false,
        });
        f.eh_info.call_sites.push(EhCallSite {
            call_block: entry,
            landing_pad_block: old_target,
        });

        renumber_blocks_contiguous(&mut f);

        let target = Block(1);
        assert_eq!(f.block_order, vec![entry, target]);
        assert_eq!(f.blocks[&entry].successors, vec![target]);
        assert_eq!(
            f.blocks[&entry].insts[0].operands,
            vec![X86ISelOperand::Block(target)]
        );
        assert_eq!(f.jump_tables[0].targets, vec![target]);
        assert_eq!(f.eh_info.landing_pads[0].block, target);
        assert_eq!(f.eh_info.call_sites[0].call_block, entry);
        assert_eq!(f.eh_info.call_sites[0].landing_pad_block, target);
    }

    /// Two independent diamonds in one function both convert in a single run.
    #[test]
    fn multiple_diamonds_convert_in_one_run() {
        // Build diamond A (b0..b3) then chain a second diamond B (b3 becomes the
        // header of B: b3 -> {b4,b5} -> b6).
        let mut f = value_select_diamond(X86CondCode::NE);
        let (b3, b4, b5, b6) = (Block(3), Block(4), Block(5), Block(6));
        for b in [b4, b5, b6] {
            f.ensure_block(b);
        }
        f.next_vreg = 30;
        let (m, x, y) = (vreg(20), vreg(21), vreg(22));
        // Rebuild b3 as a diamond header: it currently is `ret v5`. Replace with
        // define x,y; cmp; jcc b4; jmp b5.
        let b3b = f.blocks.get_mut(&b3).unwrap();
        b3b.insts.clear();
        b3b.insts.push(X86ISelInst::new(
            X86Opcode::MovRI,
            vec![X86ISelOperand::VReg(x), X86ISelOperand::Imm(3)],
        ));
        b3b.insts.push(X86ISelInst::new(
            X86Opcode::MovRI,
            vec![X86ISelOperand::VReg(y), X86ISelOperand::Imm(4)],
        ));
        b3b.insts.push(X86ISelInst::new(
            X86Opcode::CmpRI,
            vec![X86ISelOperand::VReg(x), X86ISelOperand::Imm(0)],
        ));
        b3b.insts.push(jcc(X86CondCode::E, b4));
        b3b.insts.push(jmp(b5));
        b3b.successors = vec![b4, b5];

        f.push_inst(b4, mov(m, X86ISelOperand::VReg(x)));
        f.push_inst(b4, jmp(b6));
        f.blocks.get_mut(&b4).unwrap().successors = vec![b6];
        f.push_inst(b5, mov(m, X86ISelOperand::VReg(y)));
        f.push_inst(b5, jmp(b6));
        f.blocks.get_mut(&b5).unwrap().successors = vec![b6];
        f.push_inst(
            b6,
            X86ISelInst::new(X86Opcode::Ret, vec![X86ISelOperand::VReg(m)]),
        );

        let mut pass = X86IfConvert::new(admit_exact);
        assert!(pass.run(&mut f));
        assert_eq!(pass.last_run_conversions, 2, "both diamonds convert");
        // Four arm blocks deleted; the surviving header0/header1/join renumber
        // to a gap-free 0..2 (old b0->0, old b3->1, old b6->2).
        assert_eq!(f.block_order, vec![Block(0), Block(1), Block(2)]);
        for (h, j) in [(Block(0), Block(1)), (Block(1), Block(2))] {
            let hb = &f.blocks[&h];
            assert_eq!(hb.successors, vec![j]);
            let last = hb.insts.last().unwrap();
            assert_eq!(last.opcode, X86Opcode::Jmp);
            assert_eq!(last.operands, vec![X86ISelOperand::Block(j)]);
        }
    }

    // =======================================================================
    // v2: flag-free COMPUTED arms (LEA / MovRI immediate)
    // =======================================================================

    fn lea(dst: VReg, base: VReg, disp: i32) -> X86ISelInst {
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

    fn lea_sib(dst: VReg, base: VReg, index: VReg, scale: u8, disp: i32) -> X86ISelInst {
        X86ISelInst::new(
            X86Opcode::LeaSib,
            vec![
                X86ISelOperand::VReg(dst),
                X86ISelOperand::SibMemAddr {
                    base: Box::new(X86ISelOperand::VReg(base)),
                    index: Box::new(X86ISelOperand::VReg(index)),
                    scale,
                    disp,
                },
            ],
        )
    }

    fn movri(dst: VReg, imm: i64) -> X86ISelInst {
        X86ISelInst::new(
            X86Opcode::MovRI,
            vec![X86ISelOperand::VReg(dst), X86ISelOperand::Imm(imm)],
        )
    }

    /// SOUNDNESS PROP (condition 2): every op this pass may speculate is
    /// flag-free AND memory-pure. If a future edit adds a flag-writing or
    /// memory op to `is_speculatable_compute_op`, this fails.
    #[test]
    fn speculatable_ops_are_flag_free_and_pure() {
        for op in [X86Opcode::Lea, X86Opcode::LeaSib, X86Opcode::MovRI] {
            assert!(is_speculatable_compute_op(op), "{op:?} allow-listed");
            assert!(!x86_writes_flags(op), "{op:?} must not write RFLAGS");
            assert_eq!(
                x86_opcode_effect(op),
                MemoryEffect::Pure,
                "{op:?} must be memory-pure (non-faulting)"
            );
        }
        // A representative flag-writing ALU op and a memory op are NOT admitted.
        assert!(!is_speculatable_compute_op(X86Opcode::AddRI));
        assert!(!is_speculatable_compute_op(X86Opcode::ShrRI));
        assert!(!is_speculatable_compute_op(X86Opcode::ImulRRI));
        assert!(!is_speculatable_compute_op(X86Opcode::MovRM));
        assert!(!is_speculatable_compute_op(X86Opcode::MovMR));
    }

    /// A LEA-shaped arm (the `p*3+1`-style computed value) DOES convert: the LEA
    /// is hoisted into the header (flag-free, non-faulting) and the cmov reads
    /// its fresh output vreg. The taken arm computes `v1+8` via LEA; the
    /// not-taken arm is the plain mov of `v2`.
    #[test]
    fn lea_computed_arm_converts_via_hoist() {
        let mut f = value_select_diamond(X86CondCode::NE);
        // Rebuild the taken arm (b1) as: lea v4, [v1+8]; mov v5(merge), v4; jmp.
        let (v1, v4, v5) = (vreg(1), vreg(4), vreg(5));
        let b1 = f.blocks.get_mut(&Block(1)).unwrap();
        b1.insts.clear();
        b1.insts.push(lea(v4, v1, 8));
        b1.insts.push(mov(v5, X86ISelOperand::VReg(v4)));
        b1.insts.push(jmp(Block(3)));

        let mut pass = X86IfConvert::new(admit_exact);
        assert!(pass.run(&mut f), "LEA-computed arm must convert");
        assert_eq!(pass.last_run_conversions, 1);

        // Header (old b0 -> Block(0)) now hoists the LEA, then mov/cmov/jmp.
        let h = &f.blocks[&Block(0)];
        let lea_pos = h
            .insts
            .iter()
            .position(|i| i.opcode == X86Opcode::Lea)
            .expect("LEA hoisted into header");
        let n = h.insts.len();
        // The LEA precedes the mov/cmov terminator triple.
        assert!(lea_pos < n - 3, "LEA hoisted before the mov/cmov");
        assert_eq!(h.insts[n - 3].opcode, X86Opcode::MovRR);
        assert_eq!(h.insts[n - 2].opcode, X86Opcode::Cmovcc);
        assert_eq!(h.insts[n - 1].opcode, X86Opcode::Jmp);
        // The cmov's default (mov) source is the taken arm's fresh LEA output,
        // NOT the merge or v1; the cmov overwrite source is the not-taken v2.
        let [X86ISelOperand::VReg(mov_dst), X86ISelOperand::VReg(mov_src)] =
            h.insts[n - 3].operands.as_slice()
        else {
            panic!("mov shape");
        };
        assert_eq!(*mov_dst, v5, "mov writes the merge");
        // The arm was `lea v4,[v1+8]; mov v5,v4`. Hoisting redirects the
        // merge-write (the mov to v5) to a FRESH vreg; the cmov default reads
        // that fresh output. The LEA still defines its own v4, feeding the
        // redirected mov inside the header.
        assert_ne!(
            *mov_src, v5,
            "cmov default source is the fresh output, not the merge"
        );
        assert_ne!(*mov_src, vreg(4), "fresh output is a newly-minted vreg");
        // The header holds the LEA defining v4 and a redirected `mov <fresh>, v4`.
        let [X86ISelOperand::VReg(lea_dst), _] = h.insts[lea_pos].operands.as_slice() else {
            panic!("lea shape");
        };
        assert_eq!(*lea_dst, vreg(4), "LEA keeps its original destination v4");
        assert!(
            h.insts.iter().any(|i| i.opcode == X86Opcode::MovRR
                && i.operands
                    == vec![
                        X86ISelOperand::VReg(*mov_src),
                        X86ISelOperand::VReg(vreg(4))
                    ]),
            "redirected merge-mov reads the LEA output v4 into the fresh vreg"
        );
    }

    /// BOTH arms computed (LEA vs LEA-SIB): both bodies hoist, each to its own
    /// fresh output, and the cmov selects between them.
    #[test]
    fn both_arms_computed_convert() {
        let mut f = value_select_diamond(X86CondCode::NE);
        let (v1, v2) = (vreg(1), vreg(2));
        let (v4, v5, v6) = (vreg(4), vreg(5), vreg(6));
        // taken b1: lea v4, [v1+1]; mov v5, v4; jmp
        let b1 = f.blocks.get_mut(&Block(1)).unwrap();
        b1.insts.clear();
        b1.insts.push(lea(v4, v1, 1));
        b1.insts.push(mov(v5, X86ISelOperand::VReg(v4)));
        b1.insts.push(jmp(Block(3)));
        // not-taken b2: leasib v6, [v2 + v1*2]; mov v5, v6; jmp
        let b2 = f.blocks.get_mut(&Block(2)).unwrap();
        b2.insts.clear();
        b2.insts.push(lea_sib(v6, v2, v1, 2, 0));
        b2.insts.push(mov(v5, X86ISelOperand::VReg(v6)));
        b2.insts.push(jmp(Block(3)));

        let mut pass = X86IfConvert::new(admit_exact);
        assert!(pass.run(&mut f), "two computed arms must convert");
        let h = &f.blocks[&Block(0)];
        assert_eq!(
            h.insts
                .iter()
                .filter(|i| i.opcode == X86Opcode::Lea)
                .count(),
            1,
            "taken LEA hoisted"
        );
        assert_eq!(
            h.insts
                .iter()
                .filter(|i| i.opcode == X86Opcode::LeaSib)
                .count(),
            1,
            "not-taken LEA-SIB hoisted"
        );
        let n = h.insts.len();
        // Distinct fresh outputs feed the mov/cmov.
        let [_, X86ISelOperand::VReg(default_src)] = h.insts[n - 3].operands.as_slice() else {
            panic!("mov shape");
        };
        let [_, X86ISelOperand::VReg(overwrite_src), _] = h.insts[n - 2].operands.as_slice() else {
            panic!("cmov shape");
        };
        assert_ne!(
            default_src, overwrite_src,
            "each arm has its own fresh output"
        );
    }

    /// A `MovRI` immediate arm (`if c { 5 } else { v2 }`) converts: the immediate
    /// is materialized in the header (MovRI) and the cmov reads that vreg — cmov
    /// cannot take an immediate source directly, so the fresh-vreg hoist is
    /// exactly what makes this legal.
    #[test]
    fn movri_immediate_arm_converts() {
        let mut f = value_select_diamond(X86CondCode::NE);
        let v5 = vreg(5);
        // taken b1: movri v5, 5; jmp   (the merge is the immediate directly)
        let b1 = f.blocks.get_mut(&Block(1)).unwrap();
        b1.insts.clear();
        b1.insts.push(movri(v5, 5));
        b1.insts.push(jmp(Block(3)));
        let mut pass = X86IfConvert::new(admit_exact);
        assert!(pass.run(&mut f), "MovRI immediate arm must convert");
        let h = &f.blocks[&Block(0)];
        // A MovRI materializing 5 into a fresh vreg is hoisted, and the cmov's
        // default source is that fresh vreg (a VReg, never the raw immediate).
        let movri_pos = h
            .insts
            .iter()
            .position(|i| {
                i.opcode == X86Opcode::MovRI
                    && matches!(i.operands.get(1), Some(X86ISelOperand::Imm(5)))
            })
            .expect("MovRI 5 hoisted into header");
        let [X86ISelOperand::VReg(fresh), _] = h.insts[movri_pos].operands.as_slice() else {
            panic!("movri shape");
        };
        let n = h.insts.len();
        let [_, X86ISelOperand::VReg(default_src)] = h.insts[n - 3].operands.as_slice() else {
            panic!("mov shape");
        };
        assert_eq!(
            *default_src, *fresh,
            "cmov default reads the materialized imm vreg"
        );
    }

    /// v3 (flag-writing arms, default-ON): an arm with a flag-writing ALU op
    /// (SHR — the collatz even arm `c>>1`) DOES convert, but only because the
    /// header's guard flag-setter is RE-EMITTED after the hoisted SHR and
    /// immediately before the cmov, so the RFLAGS the cmov reads reflect the
    /// original condition, not the SHR's clobber. Kill switch:
    /// `TCG_NO_X86_IFCONV_FLAGWRITE`.
    #[test]
    fn flag_writing_shr_arm_converts_with_guard_refresh() {
        let mut f = value_select_diamond(X86CondCode::NE);
        let (v4, v5) = (vreg(4), vreg(5));
        // taken b1: shr v4, 1 (writes RFLAGS!); mov v5, v4; jmp
        let b1 = f.blocks.get_mut(&Block(1)).unwrap();
        b1.insts.clear();
        b1.insts.push(X86ISelInst::new(
            X86Opcode::ShrRI,
            vec![
                X86ISelOperand::VReg(v4),
                X86ISelOperand::VReg(vreg(1)),
                X86ISelOperand::Imm(1),
            ],
        ));
        b1.insts.push(mov(v5, X86ISelOperand::VReg(v4)));
        b1.insts.push(jmp(Block(3)));
        let mut pass = X86IfConvert::new(admit_exact);
        assert!(pass.run(&mut f), "a flag-writing SHR arm converts under v3");
        assert_eq!(pass.last_run_conversions, 1);

        let h = &f.blocks[&Block(0)];
        let n = h.insts.len();
        // terminator triple is mov / cmov / jmp
        assert_eq!(h.insts[n - 3].opcode, X86Opcode::MovRR);
        assert_eq!(h.insts[n - 2].opcode, X86Opcode::Cmovcc);
        assert_eq!(h.insts[n - 1].opcode, X86Opcode::Jmp);
        // the guard flag-setter (CmpRI) is re-emitted immediately before the
        // mov/cmov, i.e. AFTER the hoisted flag-clobbering SHR.
        let shr_pos = h
            .insts
            .iter()
            .position(|i| i.opcode == X86Opcode::ShrRI)
            .expect("SHR hoisted into header");
        let refresh_pos = n - 4;
        assert_eq!(
            h.insts[refresh_pos].opcode,
            X86Opcode::CmpRI,
            "guard flag-setter re-emitted before the cmov"
        );
        assert!(
            shr_pos < refresh_pos,
            "guard is refreshed AFTER the flag-clobbering SHR (shr@{shr_pos} < refresh@{refresh_pos})"
        );
    }

    /// v3: the collatz odd arm `c*3+1` as emitted by isel (IMUL $3 then ADD $1 —
    /// both write RFLAGS) converts, with both flag-writing ops hoisted and the
    /// guard re-emitted after them.
    #[test]
    fn imul_add_arm_converts_with_guard_refresh() {
        let mut f = value_select_diamond(X86CondCode::NE);
        let (v1, v4, v5, v7) = (vreg(1), vreg(4), vreg(5), vreg(7));
        // taken b1 (SSA, as isel emits it — distinct temps per def):
        //   imul v4, v1, 3; add v7, v4, 1; mov v5, v7; jmp
        let b1 = f.blocks.get_mut(&Block(1)).unwrap();
        b1.insts.clear();
        b1.insts.push(X86ISelInst::new(
            X86Opcode::ImulRRI,
            vec![
                X86ISelOperand::VReg(v4),
                X86ISelOperand::VReg(v1),
                X86ISelOperand::Imm(3),
            ],
        ));
        b1.insts.push(X86ISelInst::new(
            X86Opcode::AddRI,
            vec![
                X86ISelOperand::VReg(v7),
                X86ISelOperand::VReg(v4),
                X86ISelOperand::Imm(1),
            ],
        ));
        b1.insts.push(mov(v5, X86ISelOperand::VReg(v7)));
        b1.insts.push(jmp(Block(3)));
        let mut pass = X86IfConvert::new(admit_exact);
        assert!(
            pass.run(&mut f),
            "collatz's imul/add odd arm converts under v3"
        );
        assert_eq!(pass.last_run_conversions, 1);

        let h = &f.blocks[&Block(0)];
        let n = h.insts.len();
        assert_eq!(h.insts[n - 3].opcode, X86Opcode::MovRR);
        assert_eq!(h.insts[n - 2].opcode, X86Opcode::Cmovcc);
        assert_eq!(h.insts[n - 1].opcode, X86Opcode::Jmp);
        // both flag-writing ops hoisted, guard re-emitted after the last of them.
        let imul_pos = h
            .insts
            .iter()
            .position(|i| i.opcode == X86Opcode::ImulRRI)
            .expect("imul hoisted");
        let add_pos = h
            .insts
            .iter()
            .position(|i| i.opcode == X86Opcode::AddRI)
            .expect("add hoisted");
        let refresh_pos = n - 4;
        assert_eq!(
            h.insts[refresh_pos].opcode,
            X86Opcode::CmpRI,
            "guard re-emitted before cmov"
        );
        assert!(
            imul_pos < refresh_pos && add_pos < refresh_pos,
            "guard refreshed after both flag-writing hoists"
        );
    }

    /// REFUTATION (condition 1): a LEA whose result then feeds a LOAD in the same
    /// arm must NOT convert — the load can fault, and speculating it is the
    /// `[TCG-PTRSEL-STORE]`-class hazard. The load op fails `speculatable_def`.
    #[test]
    fn lea_then_load_arm_is_not_converted() {
        let mut f = value_select_diamond(X86CondCode::NE);
        let (v1, v4, v5) = (vreg(1), vreg(4), vreg(5));
        // taken b1: lea v4, [v1+8]; mov v5, [v4] (a LOAD — may fault); jmp
        let b1 = f.blocks.get_mut(&Block(1)).unwrap();
        b1.insts.clear();
        b1.insts.push(lea(v4, v1, 8));
        b1.insts.push(X86ISelInst::new(
            X86Opcode::MovRM,
            vec![
                X86ISelOperand::VReg(v5),
                X86ISelOperand::MemAddr {
                    base: Box::new(X86ISelOperand::VReg(v4)),
                    disp: 0,
                },
            ],
        ));
        b1.insts.push(jmp(Block(3)));
        let mut pass = X86IfConvert::new(admit_exact);
        assert!(
            !pass.run(&mut f),
            "a LEA feeding a faultable load must never if-convert"
        );
    }

    /// REFUTATION (condition 3): a value defined in BOTH arms other than the
    /// merge (so a hoisted def would clobber a value the other path also writes /
    /// that is live at the join) blocks the merge. `find_one`'s single-common-def
    /// guard rejects it.
    #[test]
    fn second_common_def_blocks_conversion() {
        let mut f = value_select_diamond(X86CondCode::NE);
        let (v1, v2, v4, v5, v6) = (vreg(1), vreg(2), vreg(4), vreg(5), vreg(6));
        // Both arms additionally compute the SAME vreg v7 via LEA — a second
        // common def besides the merge v5.
        let v7 = vreg(7);
        let b1 = f.blocks.get_mut(&Block(1)).unwrap();
        b1.insts.clear();
        b1.insts.push(lea(v7, v1, 1));
        b1.insts.push(mov(v4, X86ISelOperand::VReg(v1)));
        b1.insts.push(mov(v5, X86ISelOperand::VReg(v4)));
        b1.insts.push(jmp(Block(3)));
        let b2 = f.blocks.get_mut(&Block(2)).unwrap();
        b2.insts.clear();
        b2.insts.push(lea(v7, v2, 1));
        b2.insts.push(mov(v6, X86ISelOperand::VReg(v2)));
        b2.insts.push(mov(v5, X86ISelOperand::VReg(v6)));
        b2.insts.push(jmp(Block(3)));
        let mut pass = X86IfConvert::new(admit_exact);
        assert!(
            !pass.run(&mut f),
            "a second vreg defined in both arms is a multi-value merge, not convertible"
        );
    }

    /// A computed arm is still gated on the inversion admission: with a rejecting
    /// callback the LEA diamond is preserved (fail-closed, no speculation).
    #[test]
    fn computed_arm_respects_inversion_admission() {
        let mut f = value_select_diamond(X86CondCode::NE);
        let (v1, v4, v5) = (vreg(1), vreg(4), vreg(5));
        let b1 = f.blocks.get_mut(&Block(1)).unwrap();
        b1.insts.clear();
        b1.insts.push(lea(v4, v1, 8));
        b1.insts.push(mov(v5, X86ISelOperand::VReg(v4)));
        b1.insts.push(jmp(Block(3)));
        let before = f.block_order.clone();
        let mut pass = X86IfConvert::new(admit_none);
        assert!(
            !pass.run(&mut f),
            "no admission => no rewrite even for computed arms"
        );
        assert_eq!(f.block_order, before, "computed diamond preserved");
    }
}
