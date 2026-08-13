// trust-cg-opt - SOUND aarch64 counted-strided-store partial-unroll (x4)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! # Counted-strided-store partial-unroll (`strided-store-unroll`)
//!
//! Partially unrolls (x4) an innermost, counted, single-strided-store marking
//! loop of the shape
//!
//! ```text
//! let mut q = q0;
//! while q <u N { base[q] = value; q += stride; }
//! ```
//!
//! with a COMPILE-TIME-CONSTANT bound `N`, a loop-invariant `base`, a
//! loop-invariant stored `value`, and a loop-invariant REGISTER `stride` (the one
//! generalization over `neon_fill`, which requires the unit `+1` step). The body
//! reads NO memory (exactly one store, zero loads) so there is no aliasing
//! question. This is exactly the p7 sieve's `while q < M { comp[q] = 1; q += p }`
//! marking loop, which LLVM 4x-unrolls; this pass matches it.
//!
//! ## Lowering (partial-unroll-with-pre-guard; mirrors `neon_fill`)
//!
//! The pass is PURELY ADDITIVE: it splices a guarded, 4x-unrolled MAIN loop in
//! FRONT of the scalar loop and NEVER edits the scalar loop's instructions. The
//! scalar loop is left byte-for-byte intact as the exact `trip mod 4` remainder
//! handler. Six fresh blocks are inserted before the scalar header; let
//! `s=stride`, `q=iv`, `base`, `val`, `N`:
//!
//! * `g1` (guard `s <u N`): `Cmp s, N; B.HS -> scalar` — a runtime `s >= N`
//!   bails; then `s < N` so all of `3s`/`4s` below are `< 4N < 2^64` and cannot
//!   wrap. `B -> g2`.
//! * `g2` (guard `s != 0`): `Cbz s -> scalar` — a non-advancing `s == 0` loop
//!   bails (it is the original loop's own infinite/immediate behavior, unchanged).
//!   `B -> g3`.
//! * `g3` (compute limit, guard room): `t3 = s+s+s` (two `AddRR`, NO multiply);
//!   `lim = N - t3` (one `SubRR`, materialized unconditionally — dead & harmlessly
//!   wrapped on the bail path, exactly `neon_fill`'s `main_bound` trick);
//!   `Cmp t3, N; B.HS -> scalar` (no room for 4 stores). `B -> mh`.
//! * `mh` (entry guard, once): `Cmp q, lim; B.LO -> mb` (`q <u lim = N-3s` => the
//!   four indices `q, q+s, q+2s, q+3s` are each `< N`); else fall through to the
//!   scalar remainder.
//! * `mb` (body + bottom test — a single-block BOTTOM-TESTED loop): the scalar
//!   body replicated 4x (identical store opcode/value/order) at `base+q`,
//!   `base+q+s`, `base+q+2s`, `base+q+3s`; then advance the SHARED iv `q += 4s`
//!   IN-PLACE and re-test `q <u lim` at the bottom — self-loop on continue, fall
//!   through to the scalar remainder on exit. One branch per iteration, matching
//!   LLVM's single-block sieve loop.
//! * COMMIT (point of no return): redirect the preheader terminator `scalar ->
//!   g1`.
//!
//! ## Why this is SOUND (no division, no multiply, wrap-free)
//!
//! `N` is a compile-time constant restricted to `[1, u32::MAX]`. The `s <u N`
//! pre-guard makes `t3 = 3s < 3N < 2^34` wrap-free; the `3s <u N` guard makes
//! `lim = N - 3s` underflow-free (`lim in [1, N)`); the `q <u lim` header guard
//! gives `q + 3s < N < 2^32` (no address wrap). Every one of the four unrolled
//! indices is `<= q+3s < N <= comp.len()` and is ALSO an index the untouched
//! scalar loop stores (it visits `q0 + k*s` while `< N`), so each is in-bounds by
//! the SAME argument that makes the scalar store safe. The main and scalar store
//! sequences are disjoint consecutive prefixes of the original strided sequence
//! (main consumes exactly 4 at a time and advances the shared iv by `4s`;
//! remainder is the `0..3` tail), so post-transform memory is byte-for-byte equal
//! to scalar-only. `s == 0` and `s >= N` and `3s >= N` all route to the scalar
//! loop, so the main loop never runs on a degenerate/out-of-room configuration.
//!
//! Every emitted opcode (`AddRR`, `SubRR`, `CmpRR`, `Cbz`, `BCond`, `B`, `MovR`,
//! `Movz`/`Movk` to materialize `N`, and the replicated store) is ALREADY emitted
//! by the surrounding scalar sieve loop — no new emittable opcode, NO udiv, NO
//! multiply, no new proof obligation. The replicated store shares the SAME
//! whole-backend store debt the scalar store already incurs.
//!
//! Default-ON at O2/O3 (never O0/O1). Compile-time kill switch:
//! `TCG_NO_STRIDED_STORE_UNROLL` (run() becomes a no-op). Per-pass bisect:
//! `TRUST_CG_DISABLE_PASSES=strided_store_unroll`.

use std::collections::{HashMap, HashSet};

use trust_cg_ir::{
    AArch64Opcode, BlockId, InstId, MachFunction, MachInst, MachOperand, RegClass, VReg,
};

use crate::dom::DomTree;
use crate::loops::LoopAnalysis;
use crate::pass_manager::{AnalysisCache, MachinePass};

#[cfg(test)]
mod tests;

/// AArch64 condition code for unsigned lower (`LO`) — the main header's
/// `q <u lim` guard and (with LT) the native `iv < N` continue test.
const CC_LO: i64 = 3;
/// AArch64 condition code for signed less-than (`LT`) — accepted alongside `LO`
/// as a native forward `iv < N` continue test.
const CC_LT: i64 = 11;
/// AArch64 condition code for unsigned higher-or-same (`HS`/`CS`) — the pre-guard
/// bails (`s >= N`, `3s >= N`).
const CC_HS: i64 = 2;

/// Compile-time kill switch: set `TCG_NO_STRIDED_STORE_UNROLL` (any value) to
/// disable the pass (run() is a no-op). Default ON at O2/O3.
fn ssu_enabled() -> bool {
    std::env::var_os("TCG_NO_STRIDED_STORE_UNROLL").is_none()
}

/// A/B kill switch for the multi-def loop-invariance fix (this file's change).
/// Set `TCG_SSU_LEGACY_INVARIANCE` (any value) to restore the ORIGINAL single-def
/// / last-index-wins dominance check, which spuriously REJECTS a multi-def stride
/// register — e.g. an enclosing scan loop's induction variable, whose `def` map
/// entry resolves to the outer-latch writeback that does NOT dominate the inner
/// preheader. Default: the corrected all-defs scan (see `is_loop_invariant`).
fn legacy_invariance() -> bool {
    std::env::var_os("TCG_SSU_LEGACY_INVARIANCE").is_some()
}

// ---------------------------------------------------------------------------
// Pass
// ---------------------------------------------------------------------------

/// The `strided-store-unroll` machine pass.
#[derive(Default)]
pub struct StridedStoreUnroll {
    fired: usize,
}

impl StridedStoreUnroll {
    pub fn new() -> Self {
        Self { fired: 0 }
    }
    /// Loops partially unrolled in the last `run`.
    pub fn fired(&self) -> usize {
        self.fired
    }
}

impl MachinePass for StridedStoreUnroll {
    fn name(&self) -> &str {
        "strided-store-unroll"
    }

    fn run(&mut self, func: &mut MachFunction) -> bool {
        if !ssu_enabled() {
            return false;
        }
        let dom = DomTree::compute(func);
        let loops = LoopAnalysis::compute(func, &dom);
        self.run_core(func, &dom, &loops)
    }

    fn run_with_analyses(&mut self, func: &mut MachFunction, analyses: &mut AnalysisCache) -> bool {
        if !ssu_enabled() {
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

impl StridedStoreUnroll {
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
            if let Some(rec) =
                Recognized::recognize(func, dom, &def_map, lp.header, lp.latch, &lp.body)
            {
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
        if changed && std::env::var("TRUST_CG_DUMP_SSU").is_ok() {
            eprintln!(
                "[strided-store-unroll] fn={} unrolled={}",
                func.name, self.fired
            );
        }
        changed
    }
}

// ---------------------------------------------------------------------------
// Recognition
// ---------------------------------------------------------------------------

struct Recognized {
    header: BlockId,
    preheader: BlockId,
    preheader_term: InstId,
    /// The `Gpr64` induction, loop-carried by `iv = MovR(iv + stride)`.
    iv: VReg,
    /// The loop-invariant `Gpr64` step register (NOT an immediate — the
    /// generalization over `neon_fill`'s `+1`).
    stride: VReg,
    /// Loop-invariant store base pointer.
    base: VReg,
    /// The compile-time-constant loop bound `N`.
    n: i64,
    /// The single store's opcode (`StrbRI` / `StrhRI` / `StrRI`).
    store_opcode: AArch64Opcode,
    /// The single store's value operand (loop-invariant); replicated verbatim.
    value_op: MachOperand,
    /// The single store's offset immediate (required `== 0`).
    store_imm: i64,
}

impl Recognized {
    fn recognize(
        func: &MachFunction,
        dom: &DomTree,
        def: &HashMap<u32, InstId>,
        header: BlockId,
        latch: BlockId,
        body: &HashSet<BlockId>,
    ) -> Option<Self> {
        let dump = std::env::var("TRUST_CG_DUMP_SSU").is_ok();
        macro_rules! bail {
            ($($t:tt)*) => {{
                if dump {
                    eprintln!("[strided-store-unroll] bail@{}: {}", func.name, format!($($t)*));
                }
                return None;
            }};
        }
        if header == latch || body.is_empty() {
            bail!("degenerate loop");
        }
        // `def` is supplied by the caller, built ONCE per recognition sweep.
        // Measured as ~99% of this pass's entire cost when it was rebuilt inside
        // every per-loop attempt.

        // (2) Closed-world opcode whitelist over the ENTIRE body. Loads, calls,
        // atomics, division, multiply, and anything unmodeled are NOT whitelisted
        // -> BAIL. Require EXACTLY ONE store and ZERO loads (the whitelist has no
        // load opcode), so the loop reads no memory: no aliasing question.
        let mut loop_insts = HashSet::new();
        let mut stores: Vec<InstId> = Vec::new();
        for &b in body {
            for &id in &func.block(b).insts {
                let op = func.inst(id).opcode;
                if !allowed_loop_op(op) {
                    bail!("disallowed body op {:?}", op);
                }
                if is_store(op) {
                    stores.push(id);
                }
                loop_insts.insert(id);
            }
        }
        if stores.len() != 1 {
            bail!("expected exactly one store, found {}", stores.len());
        }
        let store_id = stores[0];

        // (1) Header preds == exactly {preheader, latch}; single latch.
        let hpreds = &func.block(header).preds;
        if hpreds.len() != 2 || !hpreds.contains(&latch) {
            bail!("header preds != {{latch, preheader}}: {:?}", hpreds);
        }
        let preheader = *hpreds.iter().find(|&&b| b != latch)?;
        let Some(&preheader_term) = func
            .block(preheader)
            .insts
            .iter()
            .rev()
            .find(|&&id| branch_targets(func.inst(id)).contains(&header))
        else {
            bail!("no preheader->header branch");
        };

        // (3) The strided Gpr64 induction, from the latch: `iv = MovR/Copy(next)`
        // with `next = AddRR(iv, stride)`; stride = the non-iv addend.
        let Some((iv, stride)) = find_strided_induction(func, &def, latch) else {
            bail!("no `iv = MovR(iv + strideReg)` writeback in latch");
        };
        if iv.class != RegClass::Gpr64 {
            bail!("iv class not Gpr64 (iv={:?})", iv.class);
        }
        // (4) stride is a single Gpr64 register, loop-invariant.
        if stride.class != RegClass::Gpr64 {
            bail!("stride class not Gpr64 (stride={:?})", stride.class);
        }
        if stride == iv {
            bail!("stride aliases iv");
        }
        if !is_loop_invariant(func, &def, dom, &loop_insts, preheader, stride) {
            bail!("stride not loop-invariant");
        }

        // (5) Store shape: `base[iv] = value` (byte address `AddRR(base, iv)`),
        // base loop-invariant, base != iv, value a loop-invariant register.
        let Some((base, value_op, store_imm)) = store_shape(func, &def, &loop_insts, iv, store_id)
        else {
            bail!("store is not base+iv byte-address unit-stride");
        };
        if base == iv {
            bail!("base aliases iv");
        }
        if !is_loop_invariant(func, &def, dom, &loop_insts, preheader, base) {
            bail!("base not loop-invariant");
        }
        let MachOperand::VReg(value_reg) = value_op else {
            bail!("store value operand is not a register");
        };
        if !is_loop_invariant(func, &def, dom, &loop_insts, preheader, value_reg) {
            bail!("stored value not loop-invariant (reg={:?})", value_reg);
        }
        let store_opcode = func.inst(store_id).opcode;

        // (1 cont. / 6) NATIVE, COMPILE-TIME-CONSTANT bound: the `iv <u N`
        // continue test lives in the HEADER with the exit = header's non-body
        // successor. Rotated/do-while or runtime/multi-valued N => BAIL.
        let Some(n) = recognize_native_const_bound(func, &def, body, header, iv) else {
            bail!("no NATIVE forward iv<const-N continue test in header");
        };
        // Wrap-freedom + materializability: N in [1, u32::MAX] makes 3s < 3N and
        // q+3s < N all < 2^34 (no wrap) and lets Movz/Movk materialize N.
        if !(1..=i64::from(u32::MAX)).contains(&n) {
            bail!("const bound {} out of [1, u32::MAX]", n);
        }

        if dump {
            eprintln!(
                "[strided-store-unroll] RECOGNIZED@{} iv={:?} stride={:?} base={:?} N={} store={:?}",
                func.name, iv, stride, base, n, store_opcode
            );
        }
        Some(Recognized {
            header,
            preheader,
            preheader_term,
            iv,
            stride,
            base,
            n,
            store_opcode,
            value_op,
            store_imm,
        })
    }
}

/// Find the strided `Gpr64` induction in the latch: `iv = MovR/Copy(next)` with
/// `next = AddRR(iv, stride)` (symmetric addend match), or the in-place
/// `iv = AddRR(iv, stride)`. Returns `(iv, stride)` where `stride` is the non-iv
/// operand.
fn find_strided_induction(
    func: &MachFunction,
    def: &HashMap<u32, InstId>,
    latch: BlockId,
) -> Option<(VReg, VReg)> {
    // (1) Phi-copy form `iv = MovR/Copy(next)`, `next = AddRR(iv, stride)`.
    for &id in &func.block(latch).insts {
        let Some((d, s)) = copy_like(func.inst(id)) else {
            continue;
        };
        if d.class != RegClass::Gpr64 {
            continue;
        }
        let Some(&sdef) = def.get(&s.id) else {
            continue;
        };
        let si = func.inst(sdef);
        if si.opcode == AArch64Opcode::AddRR && si.operands.len() == 3 {
            let a = vreg_of(&si.operands[1])?;
            let b = vreg_of(&si.operands[2])?;
            if a == d {
                return Some((d, b));
            }
            if b == d {
                return Some((d, a));
            }
        }
    }
    // (2) In-place form `iv = AddRR(iv, stride)`.
    for &id in &func.block(latch).insts {
        let inst = func.inst(id);
        if inst.opcode == AArch64Opcode::AddRR && inst.operands.len() == 3 {
            let d = vreg_of(&inst.operands[0])?;
            if d.class != RegClass::Gpr64 {
                continue;
            }
            let a = vreg_of(&inst.operands[1])?;
            let b = vreg_of(&inst.operands[2])?;
            if a == d {
                return Some((d, b));
            }
            if b == d {
                return Some((d, a));
            }
        }
    }
    None
}

/// Extract `(base, value_operand, offset_imm)` from the single store, requiring a
/// `Str{b,h,}RI [value, addr, #0]` with `addr == AddRR(base, iv)` (byte stride,
/// unit-element index `iv`, `base != iv`).
fn store_shape(
    func: &MachFunction,
    def: &HashMap<u32, InstId>,
    loop_insts: &HashSet<InstId>,
    iv: VReg,
    store_id: InstId,
) -> Option<(VReg, MachOperand, i64)> {
    let inst = func.inst(store_id);
    match inst.opcode {
        AArch64Opcode::StrbRI | AArch64Opcode::StrhRI | AArch64Opcode::StrRI => {
            if inst.operands.len() != 3 {
                return None;
            }
            let imm = imm_of(&inst.operands[2])?;
            if imm != 0 {
                return None;
            }
            let value_op = inst.operands[0].clone();
            let addr = vreg_of(&inst.operands[1])?;
            let base = resolve_addr_base(func, def, loop_insts, iv, addr)?;
            Some((base, value_op, imm))
        }
        // StrRO (register-offset) is whitelisted for the closed-world scan but not
        // replicated here -> BAIL (fail-safe).
        _ => None,
    }
}

/// Resolve a store address register to its base, requiring `addr == base + iv`
/// via `AddRR(base, iv)` (byte stride).
fn resolve_addr_base(
    func: &MachFunction,
    def: &HashMap<u32, InstId>,
    loop_insts: &HashSet<InstId>,
    iv: VReg,
    addr: VReg,
) -> Option<VReg> {
    let &ad = def.get(&addr.id)?;
    if !loop_insts.contains(&ad) {
        return None;
    }
    let inst = func.inst(ad);
    if inst.opcode == AArch64Opcode::AddRR && inst.operands.len() == 3 {
        let a = vreg_of(&inst.operands[1])?;
        let b = vreg_of(&inst.operands[2])?;
        if same_as_iv(func, def, a, iv) {
            return Some(b);
        }
        if same_as_iv(func, def, b, iv) {
            return Some(a);
        }
    }
    None
}

/// The `iv < bound` compare found in a block, as `(lhs, imm-rhs, reg-rhs)`.
type CmpParts = (VReg, Option<i64>, Option<VReg>);

/// The single `CmpRR/CmpRI` in `blk` whose lhs is the iv (through copies).
fn find_iv_cmp(
    func: &MachFunction,
    def: &HashMap<u32, InstId>,
    blk: BlockId,
    iv: VReg,
) -> Option<CmpParts> {
    let mut found: Option<CmpParts> = None;
    for &id in &func.block(blk).insts {
        let inst = func.inst(id);
        let parts = match inst.opcode {
            AArch64Opcode::CmpRR if inst.operands.len() == 2 => (
                vreg_of(&inst.operands[0])?,
                None,
                vreg_of(&inst.operands[1]),
            ),
            AArch64Opcode::CmpRI if inst.operands.len() == 2 => {
                (vreg_of(&inst.operands[0])?, imm_of(&inst.operands[1]), None)
            }
            _ => continue,
        };
        if same_as_iv(func, def, parts.0, iv) {
            found = Some(parts);
        }
    }
    found
}

/// Recognize the NATIVE forward `iv < N` continue test with a COMPILE-TIME
/// CONSTANT bound. The test is in the `header`; its taken `BCond LT/LO` enters a
/// body block and the header has a non-body successor (the exit). Returns the
/// constant `N`. A rotated/do-while loop (no header test), a reversed compare, or
/// a runtime/non-const bound all yield `None` (BAIL).
fn recognize_native_const_bound(
    func: &MachFunction,
    def: &HashMap<u32, InstId>,
    body: &HashSet<BlockId>,
    header: BlockId,
    iv: VReg,
) -> Option<i64> {
    let (_, imm_rhs, reg_rhs) = find_iv_cmp(func, def, header, iv)?;
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
    // The header must have a non-body successor (the true exit) — confirms a
    // pre-tested native loop rather than an unconditional fall-through.
    func.block(header)
        .succs
        .iter()
        .find(|s| !body.contains(s))?;
    // Resolve the bound to a compile-time constant.
    if let Some(n) = imm_rhs {
        return Some(n);
    }
    let rhs = reg_rhs?;
    const_value(func, def, rhs)
}

/// A register is loop-invariant (w.r.t. the INNER loop being unrolled) iff:
///
/// * (a) INVARIANCE — it is NOT defined by any instruction in the inner loop
///   body, so its value is stable across every inner iteration; AND
/// * (b) AVAILABILITY — it is defined before the loop is entered.
///
/// Availability is checked by scanning ALL defs of `v` (NOT the single-def /
/// last-index-wins `def` map): `v` is available at the preheader iff SOME def of
/// `v` dominates the preheader. This is the fix for a MULTI-DEF stride such as an
/// enclosing scan loop's induction variable, which has an init def (in the outer
/// preheader, DOMINATING the inner preheader) *and* a latch writeback def (which
/// does NOT). The single-def map resolves to the latter and spuriously fails (b);
/// but the value is genuinely inner-loop-invariant because NONE of its defs lie
/// in the inner body (checked by (a)), and the unrolled main loop is spliced onto
/// the exact preheader->header path where the scalar loop already read `v`, so it
/// observes the identical per-entry value. A later, non-dominating outer def is
/// irrelevant to invariance (it is outside the body) AND to availability. A
/// never-defined pre-colored register (a function parameter) is available by ABI.
/// Fail-safe: anything else returns `false`.
fn is_loop_invariant(
    func: &MachFunction,
    def: &HashMap<u32, InstId>,
    dom: &DomTree,
    loop_insts: &HashSet<InstId>,
    preheader: BlockId,
    v: VReg,
) -> bool {
    // (a) INVARIANCE: not defined by ANY instruction in the inner loop body.
    for &id in loop_insts {
        let inst = func.inst(id);
        if produces_def(inst.opcode) && inst.operands.first().and_then(vreg_of) == Some(v) {
            return false;
        }
    }
    if legacy_invariance() {
        return legacy_available(func, def, dom, preheader, v);
    }
    // (b) AVAILABILITY: SOME def of `v` dominates the preheader — scanning ALL
    // defs (never the single-def map). A vreg with no def anywhere in the body
    // is available iff it is defined on the entry-side of the loop.
    let mut any_def = false;
    for (idx, inst) in func.insts.iter().enumerate() {
        if produces_def(inst.opcode) && inst.operands.first().and_then(vreg_of) == Some(v) {
            any_def = true;
            if let Some(db) = block_of_inst(func, InstId(idx as u32))
                && dom.dominates(db, preheader)
            {
                return true;
            }
        }
    }
    // No def at all => a pre-colored parameter register (available by ABI).
    !any_def
}

/// The ORIGINAL single-def / last-index-wins dominance availability check,
/// retained behind `TCG_SSU_LEGACY_INVARIANCE` for A/B bisection of the multi-def
/// fix. It resolves `v` to its (unique last) def and requires that one block to
/// dominate the preheader — which is exactly what fails on a multi-def stride.
fn legacy_available(
    func: &MachFunction,
    def: &HashMap<u32, InstId>,
    dom: &DomTree,
    preheader: BlockId,
    v: VReg,
) -> bool {
    let Some(&d) = def.get(&v.id) else {
        return !func.insts.iter().any(|inst| {
            produces_def(inst.opcode) && inst.operands.first().and_then(vreg_of) == Some(v)
        });
    };
    let Some(db) = block_of_inst(func, d) else {
        return false;
    };
    dom.dominates(db, preheader)
}

/// Opcodes permitted anywhere in the loop body. Loads, calls, atomics, division,
/// multiply, and any unmodeled effect are absent -> they BAIL (closed-world).
fn allowed_loop_op(op: AArch64Opcode) -> bool {
    use AArch64Opcode::*;
    matches!(
        op,
        AddRR | AddRI | SubRR | SubRI | MovR | Copy | Movz | Movk | Movn | CmpRR | CmpRI | BCond
            | B
            // Exactly one of these appears (checked separately). No LOAD opcode
            // is whitelisted, so any read BAILs.
            | StrbRI | StrhRI | StrRI | StrRO
    )
}

fn is_store(op: AArch64Opcode) -> bool {
    use AArch64Opcode::*;
    matches!(op, StrbRI | StrhRI | StrRI | StrRO)
}

// ---------------------------------------------------------------------------
// Transformation (partial-unroll-in-front; additive, never edits the scalar loop)
// ---------------------------------------------------------------------------

fn apply(func: &mut MachFunction, rec: &Recognized) -> bool {
    let s = rec.stride;
    let q = rec.iv;
    let base = rec.base;
    let scalar = rec.header;

    // Fresh blocks: g1 (s<N), g2 (s!=0), g3 (limit+room), mh (entry guard, once),
    // mb (the 4x body + bottom continuation test — a single-block BOTTOM-TESTED
    // loop, matching LLVM's one-branch-per-iteration sieve).
    let g1 = func.create_block();
    let g2 = func.create_block();
    let g3 = func.create_block();
    let mh = func.create_block();
    let mb = func.create_block();
    insert_new_blocks_before(func, scalar, &[g1, g2, g3, mh, mb]);

    // Internal edges (the preheader redirect is deferred to COMMIT so a failure
    // cannot break the CFG). Each bail block edges to the scalar header. `mb`
    // self-loops on its bottom `q <u lim` test and exits (falls through) to the
    // scalar remainder.
    func.add_edge(g1, scalar);
    func.add_edge(g1, g2);
    func.add_edge(g2, scalar);
    func.add_edge(g2, g3);
    func.add_edge(g3, scalar);
    func.add_edge(g3, mh);
    func.add_edge(mh, mb);
    func.add_edge(mh, scalar);
    func.add_edge(mb, mb);
    func.add_edge(mb, scalar);

    // --- g1: materialize N; bail if `s >=u N`.
    let nreg = materialize_in(func, g1, rec.n);
    emit(func, g1, AArch64Opcode::CmpRR, vec![vreg(s), vreg(nreg)]);
    emit(
        func,
        g1,
        AArch64Opcode::BCond,
        vec![imm(CC_HS), block(scalar)],
    );
    emit(func, g1, AArch64Opcode::B, vec![block(g2)]);

    // --- g2: bail if `s == 0` (non-advancing; original loop's own behavior).
    emit(func, g2, AArch64Opcode::Cbz, vec![vreg(s), block(scalar)]);
    emit(func, g2, AArch64Opcode::B, vec![block(g3)]);

    // --- g3: the loop-invariant stride multiples 2s/3s/4s (chained adds, NO
    // multiply), computed ONCE per loop entry; lim = N - 3s (dead & harmlessly
    // wrapped on the bail path); bail if `3s >=u N` (no room for four stores).
    let t2 = alloc(func, RegClass::Gpr64); // 2s
    emit(
        func,
        g3,
        AArch64Opcode::AddRR,
        vec![vreg(t2), vreg(s), vreg(s)],
    );
    let t3 = alloc(func, RegClass::Gpr64); // 3s
    emit(
        func,
        g3,
        AArch64Opcode::AddRR,
        vec![vreg(t3), vreg(t2), vreg(s)],
    );
    let t4 = alloc(func, RegClass::Gpr64); // 4s (the per-iteration iv step)
    emit(
        func,
        g3,
        AArch64Opcode::AddRR,
        vec![vreg(t4), vreg(t3), vreg(s)],
    );
    let lim = alloc(func, RegClass::Gpr64);
    emit(
        func,
        g3,
        AArch64Opcode::SubRR,
        vec![vreg(lim), vreg(nreg), vreg(t3)],
    );
    emit(func, g3, AArch64Opcode::CmpRR, vec![vreg(t3), vreg(nreg)]);
    emit(
        func,
        g3,
        AArch64Opcode::BCond,
        vec![imm(CC_HS), block(scalar)],
    );
    emit(func, g3, AArch64Opcode::B, vec![block(mh)]);

    // --- mh: entry guard — `q <u lim` admits a full block of four in-bounds
    // stores; otherwise fall straight through to the scalar remainder.
    emit(func, mh, AArch64Opcode::CmpRR, vec![vreg(q), vreg(lim)]);
    emit(func, mh, AArch64Opcode::BCond, vec![imm(CC_LO), block(mb)]);
    emit(func, mh, AArch64Opcode::B, vec![block(scalar)]);

    // --- mb: the scalar body replicated 4x (identical store opcode/value/order),
    // addresses base+q, base+q+s, base+q+2s, base+q+3s. A single running address
    // `ptr = base + q` is formed once, and the other three are `ptr + s`,
    // `ptr + 2s`, `ptr + 3s` from the precomputed stride multiples — so the four
    // address computations are INDEPENDENT (no serial chain). The SHARED iv `q` is
    // advanced by 4s IN-PLACE and the loop re-tests `q <u lim` at the BOTTOM, so
    // each iteration is a single block with one branch (matching LLVM's sieve).
    // k = 0: addr = base + q (the running address `ptr`).
    let ptr = alloc(func, RegClass::Gpr64);
    emit(
        func,
        mb,
        AArch64Opcode::AddRR,
        vec![vreg(ptr), vreg(base), vreg(q)],
    );
    emit_store(func, mb, rec, ptr);
    // k = 1: addr = ptr + s = base + q + s.
    let a1 = alloc(func, RegClass::Gpr64);
    emit(
        func,
        mb,
        AArch64Opcode::AddRR,
        vec![vreg(a1), vreg(ptr), vreg(s)],
    );
    emit_store(func, mb, rec, a1);
    // k = 2: addr = ptr + 2s = base + q + 2s.
    let a2 = alloc(func, RegClass::Gpr64);
    emit(
        func,
        mb,
        AArch64Opcode::AddRR,
        vec![vreg(a2), vreg(ptr), vreg(t2)],
    );
    emit_store(func, mb, rec, a2);
    // k = 3: addr = ptr + 3s = base + q + 3s.
    let a3 = alloc(func, RegClass::Gpr64);
    emit(
        func,
        mb,
        AArch64Opcode::AddRR,
        vec![vreg(a3), vreg(ptr), vreg(t3)],
    );
    emit_store(func, mb, rec, a3);
    // Advance the SHARED iv by 4s IN-PLACE (all reads of `q` above are complete),
    // then re-test `q <u lim` at the bottom: continue (self-loop) or fall through
    // to the scalar remainder.
    emit(
        func,
        mb,
        AArch64Opcode::AddRR,
        vec![vreg(q), vreg(q), vreg(t4)],
    );
    emit(func, mb, AArch64Opcode::CmpRR, vec![vreg(q), vreg(lim)]);
    emit(func, mb, AArch64Opcode::BCond, vec![imm(CC_LO), block(mb)]);
    emit(func, mb, AArch64Opcode::B, vec![block(scalar)]);

    // --- COMMIT: splice the main loop in front of the scalar loop. Point of no
    // return; runs only after all emission succeeded.
    if !rewrite_block_target(func.inst_mut(rec.preheader_term), scalar, g1) {
        return false;
    }
    remove_cfg_edge(func, rec.preheader, scalar);
    func.add_edge(rec.preheader, g1);
    true
}

/// Emit a replicated store: `store_opcode [value_op, addr, #store_imm]` — the
/// EXACT scalar store with only the address register substituted.
fn emit_store(func: &mut MachFunction, blk: BlockId, rec: &Recognized, addr: VReg) {
    emit(
        func,
        blk,
        rec.store_opcode,
        vec![rec.value_op.clone(), vreg(addr), imm(rec.store_imm)],
    );
}

/// Materialize a `[1, u32::MAX]` constant into a fresh `Gpr64` via `Movz` + `Movk`
/// chunks, APPENDED to `blk`. Returns the register.
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
// Small local IR helpers (independent copies, as in the sibling neon_* passes)
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

/// `v` equals `iv` up through `MovR`/`Copy` chains.
fn same_as_iv(func: &MachFunction, def: &HashMap<u32, InstId>, v: VReg, iv: VReg) -> bool {
    strip_copies(func, def, v) == strip_copies(func, def, iv)
}

/// Follow `MovR`/`Copy` chains to the underlying value.
fn strip_copies(func: &MachFunction, def: &HashMap<u32, InstId>, mut v: VReg) -> VReg {
    for _ in 0..16 {
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
        AArch64Opcode::Movz => {
            let (dst, value) = crate::reaching_const::movz_value(inst)?;
            if dst != v {
                return None;
            }
            i64::try_from(value).ok()
        }
        AArch64Opcode::Movk => {
            let blk = block_of_inst(func, id)?;
            let insts = &func.block(blk).insts;
            let pos = insts.iter().position(|&i| i == id)?;
            // Accumulate every earlier Movz/Movk on the same reg in this block.
            let mut acc: Option<u64> = None;
            for &pid in insts[..pos].iter() {
                let pi = func.inst(pid);
                if pi.operands.first().and_then(vreg_of) != Some(v) {
                    continue;
                }
                match pi.opcode {
                    AArch64Opcode::Movz => {
                        let (dst, value) = crate::reaching_const::movz_value(pi)?;
                        if dst != v {
                            return None;
                        }
                        acc = Some(value);
                    }
                    AArch64Opcode::Movk => {
                        acc = Some(crate::reaching_const::apply_movk(pi, v, acc?)?);
                    }
                    _ if produces_def(pi.opcode) => return None,
                    _ => {}
                }
            }
            let value = crate::reaching_const::apply_movk(inst, v, acc?)?;
            i64::try_from(value).ok()
        }
        _ => None,
    }
}

/// Conservative "operand 0 is a written def" predicate (compares/branches/guard
/// carriers do NOT define a fresh vreg).
fn produces_def(op: AArch64Opcode) -> bool {
    use AArch64Opcode::*;
    !matches!(
        op,
        CmpRR
            | CmpRI
            | BCond
            | B
            | Cbz
            | Cbnz
            | StrbRI
            | StrhRI
            | StrRI
            | StrRO
            | TrapBoundsCheckExact
            | TrapBoundsCheck
            | TrapOverflow
            | TrapOverflowExact
            | TrapNull
            | TrapNullIfZero
            | TrapDivZero
            | TrapDivZeroIfZero
            | TrapShiftRange
            | TrapShiftRangeIfOOB
    )
}

pub(crate) static STRIDED_NANOS: std::sync::atomic::AtomicU64 =
    std::sync::atomic::AtomicU64::new(0);
pub(crate) static STRIDED_CALLS: std::sync::atomic::AtomicU64 =
    std::sync::atomic::AtomicU64::new(0);

fn build_def_map(func: &MachFunction) -> HashMap<u32, InstId> {
    if crate::neon_array::boi_timing_enabled() {
        let t = std::time::Instant::now();
        let r = build_def_map_inner(func);
        STRIDED_NANOS.fetch_add(
            t.elapsed().as_nanos() as u64,
            std::sync::atomic::Ordering::Relaxed,
        );
        STRIDED_CALLS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        return r;
    }
    build_def_map_inner(func)
}

fn build_def_map_inner(func: &MachFunction) -> HashMap<u32, InstId> {
    let mut map = HashMap::new();
    for (idx, inst) in func.insts.iter().enumerate() {
        if let Some(MachOperand::VReg(v)) = inst.operands.first()
            && produces_def(inst.opcode)
        {
            map.insert(v.id, InstId(idx as u32));
        }
    }
    map
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
