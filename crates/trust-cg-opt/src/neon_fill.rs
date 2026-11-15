// trust-cg-opt - NEON constant/invariant array-fill store vectorizer (aarch64)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! # NEON array-fill store vectorizer (`neon-fill`)
//!
//! Vectorizes an innermost, counted, contiguous unit-element store-fill loop of
//! the shape
//!
//! ```text
//! for i in 0..bound { base[i*sz] = value }
//! ```
//!
//! with a loop-invariant `base`, a `const`-OR-loop-invariant stored `value`,
//! ZERO loads, and no other memory/effectful op. The recognizer is SHAPE-based
//! (never symbol-name-based), admitting supported compiled array-fill helpers
//! and inline constant/invariant fills. Runtime values use the DUP path.
//!
//! ## Lowering (vector-loop-in-front; mirrors `neon_bytesum`/`neon_map`)
//!
//! The pass is PURELY ADDITIVE: it inserts a NEON main loop in front of the
//! scalar loop and leaves its body intact. `WIDTH_ELEMS = 64 / elem_size`
//! elements are stored per vector iteration (two 32-byte paired stores):
//!
//! * PREHEADER (once per loop entry): build a broadcast Q register `qb` holding
//!   `value` in every `elem_size`-byte lane —
//!   * runtime-invariant `value` v: `NeonDupGen qb, v, elem_size` (element-size
//!     code 1/2/4/8 = B/H/S/D);
//!   * a `const` whose every byte equals `b`: `NeonMovi qb.16B, #b` (byte-form
//!     only — the encoder's sole `MOVI` form is `encode_movi_byte`, so every one
//!     of the 16 byte lanes is `b`, i.e. every `elem_size`-byte element is the
//!     value);
//!   * a general `const k`: `Movz/Movk w, k` then `NeonDupGen qb, w, elem_size`.
//!     Then a running store pointer `p = base + iv*elem_size` (`Madd` / `AddRR` for
//!     bytes).
//! * PRECHECK (runtime bound `n` only): `main_bound = n - (WIDTH_ELEMS-1)` and a
//!   signed `n < WIDTH_ELEMS` skip to the scalar loop (so the wrapped
//!   `main_bound` is dead for small/negative-as-signed `n`). Const bound `N`:
//!   `main_bound = N - (WIDTH_ELEMS-1)` materialized directly (no precheck; we
//!   fire only when `N >= WIDTH_ELEMS`).
//! * VH: `CmpRR iv, main_bound; BCond LO -> vb; B -> vx`.
//! * VB: two `NeonStpQPost [qb, qb, p, #32]` instructions write 64 identical
//!   bytes, advancing `p` by 64 in total; `B -> vl`.
//! * VL: `AddRI iv, iv, WIDTH_ELEMS; B -> vh`.
//! * VX: return to the scalar header; rotated loops first test whether a tail
//!   remains and otherwise branch to their true exit.
//! * SPLICE: redirect the preheader terminator and CFG edge to the vector entry.
//!   Shared candidate construction publishes only after every fallible step
//!   succeeds; exhaustion or missing anchors discard the whole candidate.
//!
//! ## Memory-equivalence argument for the recognized shape
//!
//! The scalar loop stores `value` to every address in `[base, base +
//! bound*elem_size)` in ascending order and reads NOTHING. The vector store set
//! is a SUBSET of that set: the vector body runs only while `iv <u main_bound =
//! bound-(WIDTH_ELEMS-1)`, so each 64-byte block `[base+iv*es, base+iv*es+64)`
//! spans elements `iv .. iv+WIDTH_ELEMS-1`, every one `< bound` — an address the
//! scalar loop also writes, with the SAME broadcast value, in ascending order.
//! So post-transform memory (vector prefix + untouched scalar tail) is
//! byte-for-byte identical to scalar-only. The loop reads nothing, so there is
//! no aliasing question. `p == base + iv*elem_size` at every header eval because
//! `64 == WIDTH_ELEMS*elem_size` (the paired stores advance `p` by 64 while the latch
//! steps `iv` by `WIDTH_ELEMS`).
//!
//! This argument is not opcode-wide or end-to-end proof authority. Existing
//! verification gates still decide whether the emitted instructions and the
//! particular transformation have sufficient evidence under the active policy.
//!
//! Default-ON at O2/Os/O3 (never O0/O1). Disable with
//! `TRUST_CG_DISABLE_PASSES=neon_fill`.

use crate::candidate::{
    alloc, commit_covered, commit_covered_all, emit, emit_before, insert_new_blocks_before,
    splice_edge,
};
use crate::fast_hash::{FxHashMap as HashMap, FxHashSet as HashSet};
use crate::loop_contract::{
    CoveredLoop, ExitPlan, GuardBound, Handoff, InductionGuards, Lanes, LoopLocality,
    LoopStateIndex, Remainder,
};
use crate::mach_util::{branch_targets, copied_const, copy_like, strip_copies};

use trust_cg_ir::{AArch64Opcode, BlockId, InstId, MachFunction, MachOperand, RegClass, VReg};

use crate::dom::DomTree;
use crate::loops::LoopAnalysis;
use crate::pass_manager::{AnalysisCache, MachinePass};

#[cfg(test)]
mod tests;

/// Bytes written by one paired store of two 128-bit Q registers.
const BYTES_PER_ITER: i64 = 32;

/// Store-pair instructions issued per vector iteration. Two `STP qb, qb`
/// write 64 bytes. The vector header admits only
/// `iv <u bound - (BLOCK_ELEMS - 1)`, so every element of the whole
/// 64-byte block is `< bound`.
const STORE_PAIRS_PER_ITER: i64 = 2;

/// AArch64 condition code for unsigned lower (`LO`) — the vector header's
/// `iv <u main_bound` guard.
const CC_LO: i64 = 3;
/// AArch64 condition code for signed less-than (`LT`) — the scalar helper's
/// signed `i < count` header test and the runtime-bound `n < WIDTH` precheck.
const CC_LT: i64 = 11;
/// AArch64 condition code for unsigned higher-or-same (`HS`/`CS`) — the rotated
/// do-while exit guard's `iv >=u bound` true-exit test.
const CC_HS: i64 = 2;

// ---------------------------------------------------------------------------
// Pass
// ---------------------------------------------------------------------------

/// The `neon-fill` machine pass.
#[derive(Default)]
pub struct NeonFillPass {
    fired: usize,
}

impl NeonFillPass {
    pub fn new() -> Self {
        Self { fired: 0 }
    }
    /// Loops vectorized in the last `run`.
    pub fn fired(&self) -> usize {
        self.fired
    }
}

impl MachinePass for NeonFillPass {
    fn name(&self) -> &str {
        "neon-fill"
    }

    fn run(&mut self, func: &mut MachFunction) -> bool {
        let dom = DomTree::compute(func);
        let loops = LoopAnalysis::compute(func, &dom);
        self.run_core(func, &dom, &loops)
    }

    fn run_with_analyses(&mut self, func: &mut MachFunction, analyses: &mut AnalysisCache) -> bool {
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

impl NeonFillPass {
    fn run_core(&mut self, func: &mut MachFunction, dom: &DomTree, loops: &LoopAnalysis) -> bool {
        self.fired = 0;
        // Recognize first (read-only); applying a plan only ADDS blocks (never
        // renumbers ids or edits other loops), so recognized data for other
        // loops stays valid.
        let mut plans = Vec::new();
        let def_map = build_def_map(func);
        // Every recognition below reads this one function state, so their
        // loop-state checks share one index of it (`LoopStateIndex`).
        let loop_state = LoopStateIndex::amortized(&*func);
        for lp in loops.all_loops() {
            // innermost only: no other loop's header lies inside this body.
            let is_innermost = loops
                .all_loops()
                .all(|other| other.header == lp.header || !lp.body.contains(&other.header));
            if !is_innermost {
                continue;
            }
            if let Some(rec) = Recognized::recognize(
                func,
                dom,
                &def_map,
                &loop_state,
                lp.header,
                lp.latch,
                &lp.body,
            ) {
                plans.push(rec);
            }
        }
        let mut changed = false;
        if apply_all(func, &plans) {
            self.fired = plans.len();
            changed = true;
        } else {
            for rec in plans {
                if apply(func, &rec) {
                    self.fired += 1;
                    changed = true;
                }
            }
        }
        changed
    }
}

// ---------------------------------------------------------------------------
// Recognition
// ---------------------------------------------------------------------------

/// The recognized loop bound: a compile-time constant or a runtime-invariant
/// register.
#[derive(Clone, Copy, Debug)]
enum Bound {
    Const(i64),
    Runtime(VReg),
}

/// How to build the broadcast Q register for the stored value.
#[derive(Clone, Copy, Debug)]
enum ValueSrc {
    /// A constant whose every `elem_size` byte equals `b` -> `MOVI Vd.16B, #b`.
    ConstByteRepl(i64),
    /// A general constant `k` -> `Movz/Movk w,k` + `NeonDupGen qb, w, es`.
    ConstGeneral(i64),
    /// A runtime-invariant register -> `NeonDupGen qb, v, es`.
    Invariant(VReg),
}

struct Recognized {
    header: BlockId,
    preheader: BlockId,
    preheader_term: InstId,
    /// The `Gpr64` induction (`iv += 1`).
    iv: VReg,
    /// The loop bound (const `N` or runtime-invariant `n`).
    bound: Bound,
    /// Loop-invariant store base pointer.
    base: VReg,
    /// Store element size in bytes (1/2/4/8 = B/H/S/D).
    elem_size: i64,
    /// The stored value's broadcast source.
    value: ValueSrc,
    /// Whether the loop is ROTATED (do-while): the `iv < bound` continue test
    /// lives in the LATCH and the `header` is the body (no pre-test). The scalar
    /// tail therefore needs a `rotated_exit` guard at the vector exit so control
    /// re-tests `iv < bound` before entering the body. In the NATIVE shape the
    /// test lives in the header (which re-tests on its own).
    rotated: bool,
    /// The loop's true exit block (the test's non-loop successor). Used by the
    /// `rotated_exit` guard.
    exit: BlockId,
    /// The loop-state contract (`crate::loop_contract`) passed for
    /// `[iv]`, with the loop its iteration-coverage clause checks the vector
    /// loop against. The plan cannot be built without it.
    scope: CoveredLoop<BlockId>,
}

impl Recognized {
    fn recognize(
        func: &MachFunction,
        dom: &DomTree,
        def: &DefIndex,
        loop_state: &LoopStateIndex<'_, MachFunction>,
        header: BlockId,
        latch: BlockId,
        body: &HashSet<BlockId>,
    ) -> Option<Self> {
        macro_rules! bail {
            ($($t:tt)*) => {{
                return None;
            }};
        }
        if header == latch || body.is_empty() {
            bail!("degenerate loop");
        }
        // `def` is supplied by the caller, built ONCE per recognition sweep.
        // Measured as ~99% of this pass's entire cost when it was rebuilt inside
        // every per-loop attempt.

        // Whitelist every opcode in the loop body. Loads (Ldr*), calls, atomics,
        // and anything unmodeled are NOT whitelisted -> BAIL (closed-world). This
        // is the ZERO-loads / single-store guarantee's first line.
        let mut loop_insts = HashSet::default();
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

        // Preheader: the single non-latch predecessor of the header.
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

        // The `+1` Gpr64 induction, from the latch.
        let Some(iv) = find_induction(func, def, latch) else {
            bail!("no +1 iv writeback in latch");
        };
        if iv.class != RegClass::Gpr64 {
            bail!("iv class not Gpr64 (iv={:?})", iv.class);
        }

        // IDEMPOTENCE: `apply` keeps the scalar loop as the remainder of the
        // vector loop it builds, advancing the SAME iv by `block_elems` in the
        // vector latch and branching from the vector exit into the scalar
        // header, so that exit becomes the scalar loop's new preheader. Without
        // this guard the remainder loop was recognized again on every fixpoint
        // iteration and each iteration nested one more zero-trip vector loop
        // (v2_memfill: +8 instructions per iteration, never converging). An iv
        // that is advanced by more than one within a few blocks upstream of the
        // preheader is exactly that remainder shape.
        if crate::vector_remainder::iv_is_vector_advanced_upstream(func, &loop_insts, preheader, iv)
        {
            bail!("remainder loop of an already-vectorized loop");
        }

        // Store shape: `base[iv*elem_size] = value`, elem_size == store width.
        let Some((base, elem_size, value_reg)) = store_info(func, def, &loop_insts, iv, store_id)
        else {
            bail!("store is not base+iv*elem_size unit-stride");
        };
        if base == iv {
            bail!("base aliases iv");
        }

        // `base` loop-invariant: NOT defined in the loop, and its def dominates
        // the preheader (fail-safe).
        if !is_loop_invariant(func, def, dom, &loop_insts, preheader, base) {
            bail!("base not loop-invariant");
        }

        // Stored value source: a constant (through copies/Movz/Movk), or a
        // runtime-invariant register. A value defined INSIDE the loop, multi-def,
        // or iv-dependent BAILs (broadcasting a stale value would miscompile).
        let value = if let Some(k) = copied_const(func, &def, value_reg) {
            if byte_replicable(k, elem_size) {
                ValueSrc::ConstByteRepl(low_byte(k))
            } else {
                ValueSrc::ConstGeneral(k)
            }
        } else if is_loop_invariant(func, def, dom, &loop_insts, preheader, value_reg) {
            ValueSrc::Invariant(value_reg)
        } else {
            bail!(
                "stored value neither const nor loop-invariant (reg={:?})",
                value_reg
            );
        };

        // The loop-continue test: a forward `iv < bound` compare either in the
        // header (NATIVE) or in the latch with a matching preheader entry guard
        // (ROTATED do-while). Yields the bound, the rotated flag, and the exit.
        let Some((bound, rotated, exit)) = recognize_loop_test(
            func,
            def,
            dom,
            &loop_insts,
            body,
            preheader,
            header,
            latch,
            iv,
        ) else {
            bail!("no forward iv<bound loop-continue test");
        };

        // Vector-benefit / wrap-freedom: fire only when at least one full
        // iteration block (STORE_PAIRS_PER_ITER * 32 bytes) can exist. Const
        // `N >= BLOCK_ELEMS`; runtime `n` is guarded by the `n < BLOCK_ELEMS`
        // precheck at apply time.
        let width_elems = BYTES_PER_ITER / elem_size;
        let block_elems = STORE_PAIRS_PER_ITER * width_elems;
        if let Bound::Const(n) = bound {
            if n < block_elems {
                bail!("const bound {} < BLOCK_ELEMS {}", n, block_elems);
            }
            // main_bound = N-(block-1) is materialized directly; keep it inside
            // the range our const materializer handles cleanly.
            let mb = n - (block_elems - 1);
            if !(0..=i64::from(u32::MAX)).contains(&mb) {
                bail!("const main_bound {} out of materializable range", mb);
            }
        }

        // LOOP STATE (`crate::loop_contract`): the vector loop runs only
        // iterations the `iv < bound` test continues, and reproduces only `iv`.
        // Any other way the loop can leave (a `break`, a `return`, a bounds
        // check against another length) would be run past: before the control
        // clause this pass filled to `n` past a `break` at 40, and stored 896
        // bytes past a 64-byte slice before the bounds-check panic (aarch64,
        // O2/O3). A register the loop also carries (`t += i` beside the fill)
        // or leaves live at an exit (`last = i`) would keep its pre-loop value;
        // both were measured wrong on aarch64 at O2/O3.
        // A bounds check on `iv` against a bound at least the loop's own (an
        // `a[i]` over an array of the loop's length) is the one other exit the
        // contract admits, by its own rule.
        let test_block = if rotated { latch } else { header };
        let at_most_iv = |v: VReg| same_as_iv(func, def, v, iv);
        let covers_loop_bound = |guard: GuardBound| match (guard, bound) {
            (GuardBound::Imm(n), Bound::Const(limit)) => (n as u64) >= (limit as u64),
            (GuardBound::Reg(r), Bound::Const(limit)) => {
                copied_const(func, def, r).is_some_and(|n| (n as u64) >= (limit as u64))
            }
            (GuardBound::Reg(r), Bound::Runtime(limit)) => strip_copies(func, def, r) == limit,
            (GuardBound::Imm(_), Bound::Runtime(_)) => false,
        };
        let exits = ExitPlan::loop_test(test_block, exit).and_induction_guards_in(
            loop_state,
            body.iter().copied(),
            header,
            &InductionGuards {
                iv,
                at_most_iv: &at_most_iv,
                covers_loop_bound: &covers_loop_bound,
            },
        );
        let scope = match LoopLocality::check_covered_in(
            loop_state,
            body.iter().copied(),
            header,
            preheader,
            &exits,
            Handoff::HeaderOrExit,
            &[iv],
        ) {
            Ok(scope) => scope,
            Err(_escape) => bail!("loop state escapes: {:?}", _escape),
        };
        Some(Recognized {
            scope,
            header,
            preheader,
            preheader_term,
            iv,
            bound,
            base,
            elem_size,
            value,
            rotated,
            exit,
        })
    }
}

/// Find the `+1` Gpr64 induction writeback in the latch. Handles both the
/// in-place `AddRI(iv, iv, 1)` form and the phi-copy form `iv = MovR(next)` with
/// `next = AddRI(iv, iv, 1)` / `AddRR(iv, const-1)`.
fn find_induction(func: &MachFunction, def: &DefIndex, latch: BlockId) -> Option<VReg> {
    // (1) In-place `AddRI(iv, iv, 1)` / `AddRR(iv, iv, one)`.
    for &id in &func.block(latch).insts {
        let inst = func.inst(id);
        match inst.opcode {
            AArch64Opcode::AddRI
                if inst.operands.len() == 3 && inst.operands[2].as_imm() == Some(1) =>
            {
                let d = inst.operands[0].as_vreg()?;
                let s = inst.operands[1].as_vreg()?;
                if d == s && d.class == RegClass::Gpr64 {
                    return Some(d);
                }
            }
            AArch64Opcode::AddRR if inst.operands.len() == 3 => {
                let d = inst.operands[0].as_vreg()?;
                let a = inst.operands[1].as_vreg()?;
                let b = inst.operands[2].as_vreg()?;
                if d.class == RegClass::Gpr64
                    && ((a == d && copied_const(func, def, b) == Some(1))
                        || (b == d && copied_const(func, def, a) == Some(1)))
                {
                    return Some(d);
                }
            }
            _ => {}
        }
    }
    // (2) Phi-copy form `iv = MovR/Copy(next)` with `next = AddRI/AddRR(iv, ., 1)`.
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
        match si.opcode {
            AArch64Opcode::AddRI
                if si.operands.len() == 3
                    && si.operands[1].as_vreg() == Some(d)
                    && si.operands[2].as_imm() == Some(1) =>
            {
                return Some(d);
            }
            AArch64Opcode::AddRR if si.operands.len() == 3 => {
                let a = si.operands[1].as_vreg()?;
                let b = si.operands[2].as_vreg()?;
                if (a == d && copied_const(func, def, b) == Some(1))
                    || (b == d && copied_const(func, def, a) == Some(1))
                {
                    return Some(d);
                }
            }
            _ => {}
        }
    }
    None
}

/// Extract `(base, elem_size, value)` from the single store, requiring the
/// address to be `base + iv*elem_size` with `elem_size` == the store width and a
/// contiguous unit-element stride (`index == iv`, `base != iv`).
fn store_info(
    func: &MachFunction,
    def: &DefIndex,
    loop_insts: &HashSet<InstId>,
    iv: VReg,
    store_id: InstId,
) -> Option<(VReg, i64, VReg)> {
    let inst = func.inst(store_id);
    // FAIL-CLOSED: the transfer register (operand 0) must be a GENERAL-PURPOSE
    // register. Emission derives TWO things from it that recognition would
    // otherwise never constrain:
    //   * the access WIDTH for the full-width `StrRI`/`StrRO` forms — the
    //     encoder takes it from the transfer class (`Fpr128`->16, `Fpr64`->8,
    //     `Fpr32`->4, `Fpr16`->2), while the arms below read "not `Gpr64`" as
    //     4 bytes. An `Fpr16` (`str h`, 2 bytes) or `Fpr64` (`str d`, 8 bytes)
    //     transfer therefore mis-sizes the element, and the vector fill writes
    //     the wrong number of bytes per element.
    //   * the DUP broadcast SOURCE — `ValueSrc::Invariant` feeds this exact
    //     register to `NeonDupGen qb, v, es`, i.e. `DUP Vd.<T>, Rn`, whose Rn
    //     field is a GPR. `preg_hw` writes an FP register's hw number into that
    //     GPR field with no bank check, so a `V5` value silently broadcasts
    //     `W5` — the wrong register file. (Same hazard the `AtomicLoad`
    //     integer-only gate in trust-cg-lower documents for `LDAR`.)
    // A `Gpr32`/`Gpr64` transfer makes both derivations exact. Everything else
    // BAILS. (Mirrors the `value.class != RegClass::Gpr32` gate in the sibling
    // `neon_iota_fill::store_info`.)
    let transfer = inst.operands.first()?.as_vreg()?;
    if !matches!(transfer.class, RegClass::Gpr32 | RegClass::Gpr64) {
        return None;
    }
    match inst.opcode {
        AArch64Opcode::StrbRI | AArch64Opcode::StrhRI | AArch64Opcode::StrRI => {
            if inst.operands.len() != 3 || inst.operands[2].as_imm() != Some(0) {
                return None;
            }
            let value = inst.operands[0].as_vreg()?;
            let addr = inst.operands[1].as_vreg()?;
            let elem_size = match inst.opcode {
                AArch64Opcode::StrbRI => 1,
                AArch64Opcode::StrhRI => 2,
                // StrRI: width from the transfer register class.
                _ => {
                    if value.class == RegClass::Gpr64 {
                        8
                    } else {
                        4
                    }
                }
            };
            let base = resolve_addr_base(func, def, loop_insts, iv, addr, elem_size)?;
            Some((base, elem_size, value))
        }
        AArch64Opcode::StrRO => {
            // [Rt(value), Rn(base), Rm(index), Imm((option<<1)|S)]. Byte address =
            // base + (index << S*log2(size)). For a contiguous unit-element stride
            // the index must be `iv` and the shift must equal log2(elem_size).
            if inst.operands.len() != 4 {
                return None;
            }
            let value = inst.operands[0].as_vreg()?;
            let base = inst.operands[1].as_vreg()?;
            let index = inst.operands[2].as_vreg()?;
            let enc = inst.operands[3].as_imm()?;
            let elem_size: i64 = if value.class == RegClass::Gpr64 { 8 } else { 4 };
            if !same_as_iv(func, def, index, iv) {
                return None;
            }
            // S bit must scale the index by log2(elem_size); anything else is not
            // the unit-element stride we require.
            let s = enc & 1;
            let log2es = elem_size.trailing_zeros() as i64;
            if (s == 1 && log2es != 0) || (s == 0 && log2es == 0) {
                // ok: either scaled by the right log2, or byte (no scaling).
                Some((base, elem_size, value))
            } else {
                None
            }
        }
        _ => None,
    }
}

/// Resolve an `StrbRI/StrhRI/StrRI` address register to its base, requiring
/// `addr == base + iv*elem_size`: `AddRR(base, iv)` (byte stride) or
/// `Madd(iv, elem_size, base)`.
fn resolve_addr_base(
    func: &MachFunction,
    def: &DefIndex,
    loop_insts: &HashSet<InstId>,
    iv: VReg,
    addr: VReg,
    elem_size: i64,
) -> Option<VReg> {
    let &ad = def.get(&addr.id)?;
    if !loop_insts.contains(&ad) {
        return None;
    }
    let inst = func.inst(ad);
    match inst.opcode {
        AArch64Opcode::AddRR if inst.operands.len() == 3 && elem_size == 1 => {
            let a = inst.operands[1].as_vreg()?;
            let b = inst.operands[2].as_vreg()?;
            if same_as_iv(func, def, a, iv) {
                Some(b)
            } else if same_as_iv(func, def, b, iv) {
                Some(a)
            } else {
                None
            }
        }
        AArch64Opcode::Madd if inst.operands.len() == 4 => {
            // addr = f1*f2 + f3; want iv*elem_size + base.
            let f1 = inst.operands[1].as_vreg()?;
            let f2 = inst.operands[2].as_vreg()?;
            let base = inst.operands[3].as_vreg()?;
            let es = |f: VReg| copied_const(func, def, f) == Some(elem_size);
            if (same_as_iv(func, def, f1, iv) && es(f2))
                || (same_as_iv(func, def, f2, iv) && es(f1))
            {
                Some(base)
            } else {
                None
            }
        }
        _ => None,
    }
}

/// The `iv < bound` compare found in a block, as `(lhs, imm-rhs, reg-rhs)`.
type CmpParts = (VReg, Option<i64>, Option<VReg>);

/// The single `CmpRR/CmpRI` in `blk` whose lhs is the iv (through copies).
fn find_iv_cmp(func: &MachFunction, def: &DefIndex, blk: BlockId, iv: VReg) -> Option<CmpParts> {
    let mut found: Option<CmpParts> = None;
    for &id in &func.block(blk).insts {
        let inst = func.inst(id);
        let parts = match inst.opcode {
            AArch64Opcode::CmpRR if inst.operands.len() == 2 => (
                inst.operands[0].as_vreg()?,
                None,
                inst.operands[1].as_vreg(),
            ),
            AArch64Opcode::CmpRI if inst.operands.len() == 2 => {
                (inst.operands[0].as_vreg()?, inst.operands[1].as_imm(), None)
            }
            _ => continue,
        };
        if same_as_iv(func, def, parts.0, iv) {
            found = Some(parts);
        }
    }
    found
}

/// A forward `BCond LT/LO -> want` in `blk` (the loop-continue direction).
fn has_forward_branch_to(func: &MachFunction, blk: BlockId, want: BlockId) -> bool {
    for &id in &func.block(blk).insts {
        let inst = func.inst(id);
        if inst.opcode == AArch64Opcode::BCond && inst.operands.len() == 2 {
            let Some(cc) = inst.operands[0].as_imm() else {
                continue;
            };
            if (cc == CC_LT || cc == CC_LO) && branch_targets(inst).first() == Some(&want) {
                return true;
            }
        }
    }
    false
}

/// Resolve a compare's `(imm-rhs, reg-rhs)` to a `Bound`.
fn bound_of(
    func: &MachFunction,
    def: &DefIndex,
    dom: &DomTree,
    loop_insts: &HashSet<InstId>,
    preheader: BlockId,
    imm_rhs: Option<i64>,
    reg_rhs: Option<VReg>,
) -> Option<Bound> {
    if let Some(n) = imm_rhs {
        return Some(Bound::Const(n));
    }
    let rhs = reg_rhs?;
    if let Some(n) = copied_const(func, def, rhs) {
        return Some(Bound::Const(n));
    }
    let canon = strip_copies(func, def, rhs);
    if is_loop_invariant(func, def, dom, loop_insts, preheader, canon) {
        return Some(Bound::Runtime(canon));
    }
    None
}

/// Recognize the forward `iv < bound` loop-continue test. Two shapes:
///
/// * NATIVE: the test is in the `header`; its taken-`BCond LT/LO` enters the loop
///   body and its fallthrough leaves. The header re-tests on its own, so the
///   scalar tail needs no extra guard. Exit = the header's non-loop successor.
/// * ROTATED (do-while): the test is in the `latch` (`BCond LT/LO -> header`) and
///   the `preheader` carries a MATCHING entry guard (`BCond LT/LO -> header` on
///   the same iv-vs-bound compare). The `header` is the body (no pre-test), so
///   the scalar tail needs a `rotated_exit` guard. Exit = the latch's non-header
///   successor (must equal the preheader guard's non-header successor).
///
/// Returns `(bound, rotated, exit)`. A reversed / `!=` / non-forward compare, or
/// a rotated loop lacking the entry guard, BAILS.
#[allow(clippy::too_many_arguments)]
fn recognize_loop_test(
    func: &MachFunction,
    def: &DefIndex,
    dom: &DomTree,
    loop_insts: &HashSet<InstId>,
    body: &HashSet<BlockId>,
    preheader: BlockId,
    header: BlockId,
    latch: BlockId,
    iv: VReg,
) -> Option<(Bound, bool, BlockId)> {
    // --- NATIVE: the continue-test is in the header.
    if let Some((_, imm_rhs, reg_rhs)) = find_iv_cmp(func, def, header, iv) {
        // A forward BCond whose taken-target is a body block, plus a fallthrough
        // leaving the loop.
        let mut taken: Option<BlockId> = None;
        for &id in &func.block(header).insts {
            let inst = func.inst(id);
            if inst.opcode == AArch64Opcode::BCond && inst.operands.len() == 2 {
                let cc = inst.operands[0].as_imm()?;
                let tgt = *branch_targets(inst).first()?;
                if (cc == CC_LT || cc == CC_LO) && body.contains(&tgt) {
                    taken = Some(tgt);
                }
            }
        }
        // NATIVE additionally requires the CANONICAL top-tested shape: the
        // latch must return to the header UNCONDITIONALLY. Only then does the
        // header's test legitimately observe every post-increment iv
        // (including failing ones), making its non-body successor the loop's
        // LIVE exit. A loop whose latch back-branches CONDITIONALLY (a
        // rotated do-while whose header carries a residual in-loop check)
        // filters iv >= bound away from the header: the header's "exit"
        // successor is dead in the original execution — e.g. a bounds
        // check's abort arm — and routing the vector residual into it
        // manufactures a state the original program never reaches
        // (2026-08-13 v2_memfill/v3_popcount wrong-abort, caught by the
        // 72-program exit-status gate). Such loops fall through to the
        // ROTATED arm below, whose `rotated_exit` guard re-enters via the
        // latch test's live exit instead.
        let latch_backedge_unconditional = func.block(latch).insts.last().is_some_and(|&id| {
            let t = func.inst(id);
            t.opcode == AArch64Opcode::B && branch_targets(t).contains(&header)
        });
        if taken.is_some() && latch_backedge_unconditional {
            // The exit is the header successor that is NOT in the loop body.
            if let Some(&exit) = func.block(header).succs.iter().find(|s| !body.contains(s))
                && let Some(bound) =
                    bound_of(func, def, dom, loop_insts, preheader, imm_rhs, reg_rhs)
            {
                return Some((bound, false, exit));
            }
        }
    }

    // --- ROTATED: the continue-test is in the latch; the preheader is a matching
    // entry guard.
    let (_, imm_rhs, reg_rhs) = find_iv_cmp(func, def, latch, iv)?;
    if !has_forward_branch_to(func, latch, header) {
        return None;
    }
    // The preheader must carry a matching entry guard on the same iv-vs-bound
    // compare that forward-branches to the header. This makes entering the header
    // (the body) always guarded by `iv < bound` at loop entry.
    let (_, g_imm, g_reg) = find_iv_cmp(func, def, preheader, iv)?;
    if !has_forward_branch_to(func, preheader, header) {
        return None;
    }
    // The entry guard and latch test must compare against the SAME bound.
    if g_imm != imm_rhs
        || g_reg.map(|v| strip_copies(func, def, v)) != reg_rhs.map(|v| strip_copies(func, def, v))
    {
        return None;
    }
    // Exit = latch's non-header successor; must match the preheader's non-header
    // successor (the shared true-exit).
    let latch_exit = func
        .block(latch)
        .succs
        .iter()
        .copied()
        .find(|&s| s != header);
    let pre_exit = func
        .block(preheader)
        .succs
        .iter()
        .copied()
        .find(|&s| s != header);
    let (Some(exit), Some(pre_exit)) = (latch_exit, pre_exit) else {
        return None;
    };
    if exit != pre_exit {
        return None;
    }
    let bound = bound_of(func, def, dom, loop_insts, preheader, imm_rhs, reg_rhs)?;
    Some((bound, true, exit))
}

/// A register is loop-invariant iff it is NOT defined anywhere in the loop body
/// and its (unique last) def dominates the preheader. Fail-safe: anything else
/// returns `false`.
fn is_loop_invariant(
    func: &MachFunction,
    def: &DefIndex,
    dom: &DomTree,
    loop_insts: &HashSet<InstId>,
    preheader: BlockId,
    v: VReg,
) -> bool {
    // Not defined inside the loop.
    for &id in loop_insts {
        if crate::effects::inst_defines_vreg(func.inst(id), v) {
            return false;
        }
    }
    // Its def dominates the preheader.
    let Some(&d) = def.get(&v.id) else {
        // No def found (e.g. a function parameter pre-colored register): treat as
        // invariant only if it is truly never defined in the function body.
        return !def.defined_in_layout(func, v);
    };
    let Some(db) = def.block_of_inst(func, d) else {
        return false;
    };
    dom.dominates(db, preheader)
}

/// Whether a constant's every `elem_size`-byte lane collapses to one repeated
/// byte (so `MOVI Vd.16B, #b` fills each element with the value).
fn byte_replicable(value: i64, elem_size: i64) -> bool {
    let b = (value as u64) & 0xFF;
    for k in 0..elem_size {
        if ((value as u64) >> (8 * k)) & 0xFF != b {
            return false;
        }
    }
    true
}

fn low_byte(value: i64) -> i64 {
    (value as u64 & 0xFF) as i64
}

/// Opcodes permitted anywhere in the loop body. Loads, calls, atomics, division,
/// and any unmodeled effect are absent -> they BAIL (closed-world).
fn allowed_loop_op(op: AArch64Opcode) -> bool {
    use AArch64Opcode::*;
    matches!(
        op,
        AddRR | AddRI | SubRR | SubRI | MulRR | Madd | AndRR | AndRI | OrrRR | OrrRI | EorRR
            | LsrRI | LslRI | AsrRI | Movz | Movk | Movn | MovR | Copy | CmpRR | CmpRI | BCond | B
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
// Transformation (vector-loop-in-front; additive, never edits the scalar loop)
// ---------------------------------------------------------------------------

/// Apply one plan, published only when the loop-state contract's
/// iteration-coverage clause admits it: each trip through the vector latch
/// runs `BLOCK_ELEMS` iterations, and the scalar loop runs the rest.
fn apply(func: &mut MachFunction, rec: &Recognized) -> bool {
    commit_covered(func, &rec.scope, |candidate| {
        apply_candidate(candidate, rec)
    })
}

#[cfg(test)]
thread_local! {
    /// Tests set this to take the one-plan-at-a-time path on every run.
    static FORCE_PER_PLAN: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Every plan applied, in order, to ONE private candidate, published only if
/// every one succeeds; `false` (nothing published) as soon as one declines,
/// and the caller then applies them one [`apply`] at a time.
///
/// When every plan succeeds this is exactly the per-plan path: plan `k` runs
/// on the function the first `k - 1` plans left, in both, and the vreg
/// counter synchronization `commit` makes before each plan is a no-op after
/// the first (every register a plan adds comes from the counter). What it
/// saves is the whole-function clone and counter scan per plan, which made a
/// function with many fill loops quadratic in them (L14-P6).
fn apply_all(func: &mut MachFunction, plans: &[Recognized]) -> bool {
    #[cfg(test)]
    if FORCE_PER_PLAN.with(std::cell::Cell::get) {
        return false;
    }
    if plans.len() < 2 {
        return false;
    }
    let scopes: Vec<&CoveredLoop<BlockId>> = plans.iter().map(|rec| &rec.scope).collect();
    commit_covered_all(func, &scopes, |candidate| {
        plans
            .iter()
            .map(|rec| apply_candidate(candidate, rec))
            .collect()
    })
}

/// Build the vector loop for `rec` on `func`; returns how it counts: the
/// vector latch, entered once per trip of `BLOCK_ELEMS` iterations, and the
/// scalar loop as the remainder.
fn apply_candidate(func: &mut MachFunction, rec: &Recognized) -> Option<Lanes<BlockId>> {
    let width_elems = BYTES_PER_ITER / rec.elem_size;
    let block_elems = STORE_PAIRS_PER_ITER * width_elems;

    // Fresh blocks: an optional runtime-bound precheck, then vh/vb/vl/vx.
    let pv = match rec.bound {
        Bound::Runtime(_) => Some(func.try_create_block()?),
        Bound::Const(_) => None,
    };
    let vh = func.try_create_block()?;
    let vb = func.try_create_block()?;
    let vl = func.try_create_block()?;
    let vx = func.try_create_block()?;
    let mut fresh: Vec<BlockId> = Vec::new();
    if let Some(pv) = pv {
        fresh.push(pv);
    }
    fresh.extend([vh, vb, vl, vx]);
    insert_new_blocks_before(func, rec.header, &fresh)?;

    // Internal edges among fresh blocks only; the preheader redirect is deferred
    // to the COMMIT so a lowering failure cannot break the CFG.
    if let Some(pv) = pv {
        func.add_edge(pv, vh);
        func.add_edge(pv, rec.header);
    }
    func.add_edge(vh, vb);
    func.add_edge(vh, vx);
    func.add_edge(vb, vl);
    func.add_edge(vl, vh);

    let pre = rec.preheader_term;

    // --- Preheader: build the broadcast Q register `qb`.
    let qb = alloc(func, RegClass::Fpr128)?;
    match rec.value {
        ValueSrc::ConstByteRepl(b) => {
            // MOVI Vd.16B, #b — every one of the 16 byte lanes is `b`, so every
            // elem_size-byte element equals the value.
            emit_before(func, pre, AArch64Opcode::NeonMovi, vec![vreg(qb), imm(b)])?;
        }
        ValueSrc::ConstGeneral(k) => {
            let w = materialize_before(func, pre, k)?;
            emit_before(
                func,
                pre,
                AArch64Opcode::NeonDupGen,
                vec![vreg(qb), vreg(w), imm(rec.elem_size)],
            )?;
        }
        ValueSrc::Invariant(v) => {
            emit_before(
                func,
                pre,
                AArch64Opcode::NeonDupGen,
                vec![vreg(qb), vreg(v), imm(rec.elem_size)],
            )?;
        }
    }

    // --- Preheader: running store pointer `p = base + iv*elem_size`.
    let p = alloc(func, RegClass::Gpr64)?;
    if rec.elem_size == 1 {
        emit_before(
            func,
            pre,
            AArch64Opcode::AddRR,
            vec![vreg(p), vreg(rec.base), vreg(rec.iv)],
        )?;
    } else {
        let c_es = alloc(func, RegClass::Gpr64)?;
        emit_before(
            func,
            pre,
            AArch64Opcode::Movz,
            vec![vreg(c_es), imm(rec.elem_size)],
        )?;
        emit_before(
            func,
            pre,
            AArch64Opcode::Madd,
            vec![vreg(p), vreg(rec.iv), vreg(c_es), vreg(rec.base)],
        )?;
    }

    // --- main_bound = bound - (WIDTH_ELEMS-1). Runtime bound: compute in a
    // precheck block that skips the vector loop for `n < WIDTH_ELEMS` (so the
    // wrapped main_bound is dead). Const bound: materialize directly.
    let main_bound = alloc(func, RegClass::Gpr64)?;
    match rec.bound {
        Bound::Runtime(n) => {
            let pv = pv?;
            emit(
                func,
                pv,
                AArch64Opcode::SubRI,
                vec![vreg(main_bound), vreg(n), imm(block_elems - 1)],
            )?;
            emit(
                func,
                pv,
                AArch64Opcode::CmpRI,
                vec![vreg(n), imm(block_elems)],
            )?;
            emit(
                func,
                pv,
                AArch64Opcode::BCond,
                vec![imm(CC_LT), block(rec.header)],
            )?;
            emit(func, pv, AArch64Opcode::B, vec![block(vh)])?;
        }
        Bound::Const(n) => {
            let mb = materialize_before(func, pre, n - (block_elems - 1))?;
            emit_before(
                func,
                pre,
                AArch64Opcode::MovR,
                vec![vreg(main_bound), vreg(mb)],
            )?;
        }
    }

    // --- Vector header: `iv <u main_bound` admits only full in-bounds blocks.
    emit(
        func,
        vh,
        AArch64Opcode::CmpRR,
        vec![vreg(rec.iv), vreg(main_bound)],
    )?;
    emit(func, vh, AArch64Opcode::BCond, vec![imm(CC_LO), block(vb)])?;
    emit(func, vh, AArch64Opcode::B, vec![block(vx)])?;

    // --- Vector body: STORE_PAIRS_PER_ITER paired post-index stores
    // `STP qb, qb, [p], #32` — each 32 identical bytes; the block covers
    // BLOCK_ELEMS elements, all the broadcast value.
    for _ in 0..STORE_PAIRS_PER_ITER {
        emit(
            func,
            vb,
            AArch64Opcode::NeonStpQPost,
            vec![vreg(qb), vreg(qb), vreg(p), imm(BYTES_PER_ITER)],
        )?;
    }
    emit(func, vb, AArch64Opcode::B, vec![block(vl)])?;

    // --- Vector latch: advance the scalar induction by BLOCK_ELEMS (p is
    // advanced 32 bytes by EACH store's post-index, keeping p == base+iv*es).
    emit(
        func,
        vl,
        AArch64Opcode::AddRI,
        vec![vreg(rec.iv), vreg(rec.iv), imm(block_elems)],
    )?;
    emit(func, vl, AArch64Opcode::B, vec![block(vh)])?;

    // --- Vector exit: hand off to the scalar loop for the [iv, bound) remainder.
    //   * NATIVE: the header re-tests `iv < bound`, so branch there directly.
    //   * ROTATED (do-while): the header is the body (no pre-test). If the vector
    //     consumed everything (`iv >=u bound`), entering the body would store one
    //     element PAST the end. Guard with `iv >=u bound -> true exit`; otherwise
    //     fall into the body, which writes the disjoint tail `[iv, bound)`.
    if rec.rotated {
        match rec.bound {
            Bound::Runtime(n) => {
                emit(func, vx, AArch64Opcode::CmpRR, vec![vreg(rec.iv), vreg(n)])?;
            }
            Bound::Const(n) => {
                let nb = materialize_before(func, pre, n)?;
                emit(func, vx, AArch64Opcode::CmpRR, vec![vreg(rec.iv), vreg(nb)])?;
            }
        }
        emit(
            func,
            vx,
            AArch64Opcode::BCond,
            vec![imm(CC_HS), block(rec.exit)],
        )?;
        emit(func, vx, AArch64Opcode::B, vec![block(rec.header)])?;
    } else {
        emit(func, vx, AArch64Opcode::B, vec![block(rec.header)])?;
    }

    // Finish the private candidate's entry edge; publication happens in commit.
    let entry = pv.unwrap_or(vh);
    splice_edge(func, rec.preheader, rec.preheader_term, rec.header, entry)?;
    func.add_edge(vx, rec.header);
    if rec.rotated {
        func.add_edge(vx, rec.exit);
    }
    Some(Lanes {
        blocks: vec![(vl, block_elems as u64)],
        remainder: Remainder::ScalarLoop,
        copies: Vec::new(),
    })
}

/// Materialize a (non-negative, fits-u32 or full-u64) constant into a fresh
/// `Gpr64` via `Movz` + `Movk` chunks, before `before`. Returns the register.
fn materialize_before(func: &mut MachFunction, before: InstId, value: i64) -> Option<VReg> {
    let d = alloc(func, RegClass::Gpr64)?;
    let bits = value as u64;
    // Low 16 via Movz, then any nonzero higher halfwords via Movk.
    emit_before(
        func,
        before,
        AArch64Opcode::Movz,
        vec![vreg(d), imm((bits & 0xFFFF) as i64)],
    )?;
    for hw in 1..4u32 {
        let chunk = (bits >> (hw * 16)) & 0xFFFF;
        if chunk != 0 {
            emit_before(
                func,
                before,
                AArch64Opcode::Movk,
                vec![vreg(d), imm(chunk as i64), imm((hw * 16) as i64)],
            )?;
        }
    }
    Some(d)
}

// ---------------------------------------------------------------------------
// Local operand/recognition helpers; checked mutation lives in candidate.rs
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

/// `v` equals `iv` up through `MovR`/`Copy` chains.
fn same_as_iv(func: &MachFunction, def: &DefIndex, v: VReg, iv: VReg) -> bool {
    strip_copies(func, def, v) == strip_copies(func, def, iv)
}

pub(crate) static FILL_NANOS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
pub(crate) static FILL_CALLS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

/// The def facts recognition reads, built ONCE per recognition sweep.
///
/// Recognition is read-only (every plan is applied after every loop has been
/// recognized), so these whole-function facts are exact for the whole sweep.
/// Each used to be recomputed per question by a whole-function scan
/// (`effects::live_def_count` inside `strip_copies` and `const_value`,
/// `block_of_inst`, and the no-def fallback of `is_loop_invariant`), which
/// made recognizing the loops of a function with many loops quadratic in
/// them (L14-P6: 72 ms of a 120-loop function, 1.14 s at 480 loops).
///
/// The first [`LITERAL_QUESTIONS`] questions of each kind are still answered
/// by those scans: most functions ask only a few (most loops are declined
/// before any is asked), and for them one scan per question costs less than
/// building the index. A function that asks more pays one build.
pub(crate) struct DefIndex {
    /// `effects::build_reaching_def_map`: the last def of each id in layout.
    reaching: HashMap<u32, InstId>,
    /// Built once more than [`LITERAL_QUESTIONS`] questions needed them.
    layout: std::cell::OnceCell<LayoutDefs>,
    block_of: std::cell::OnceCell<HashMap<InstId, BlockId>>,
    /// Questions answered by a literal scan so far, per index.
    layout_questions: std::cell::Cell<u32>,
    block_questions: std::cell::Cell<u32>,
}

/// Questions of one kind a [`DefIndex`] answers by the literal
/// whole-function scan before it builds that kind's index.
const LITERAL_QUESTIONS: u32 = 4;

/// Whether `asked` (the literal answers given so far) still allows one more:
/// counts this question when it does.
fn literal_allowed(asked: &std::cell::Cell<u32>) -> bool {
    let n = asked.get();
    if n >= LITERAL_QUESTIONS {
        return false;
    }
    asked.set(n + 1);
    true
}

/// Whole-layout def facts of a [`DefIndex`].
struct LayoutDefs {
    /// `effects::live_def_count` of every id that has a def in layout.
    live_defs: HashMap<u32, usize>,
    /// Every vreg some instruction in layout defines (`inst_defines_vreg`).
    defined: HashSet<VReg>,
}

impl crate::mach_util::DefLookup for DefIndex {
    fn last_def(&self, id: u32) -> Option<InstId> {
        self.reaching.get(&id).copied()
    }

    /// [`DefIndex::live_def_count`]: the layout index once it is built, a
    /// literal scan for the first questions.
    fn indexed_def_count(&self, func: &MachFunction, id: u32) -> Option<usize> {
        Some(self.live_def_count(func, id))
    }
}

impl DefIndex {
    fn build(func: &MachFunction) -> Self {
        Self {
            reaching: crate::effects::build_reaching_def_map(func),
            layout: std::cell::OnceCell::new(),
            block_of: std::cell::OnceCell::new(),
            layout_questions: std::cell::Cell::new(0),
            block_questions: std::cell::Cell::new(0),
        }
    }

    /// The whole-layout def facts, or `None` while literal scans are still
    /// allowed (see [`LITERAL_QUESTIONS`]).
    fn layout_facts(&self, func: &MachFunction) -> Option<&LayoutDefs> {
        if self.layout.get().is_none() && literal_allowed(&self.layout_questions) {
            return None;
        }
        Some(self.layout.get_or_init(|| Self::layout_defs(func)))
    }

    fn layout_defs(func: &MachFunction) -> LayoutDefs {
        let mut live_defs: HashMap<u32, usize> = HashMap::default();
        let mut defined: HashSet<VReg> = HashSet::default();
        let mut ids: Vec<u32> = Vec::new();
        for &b in &func.block_order {
            for &i in &func.block(b).insts {
                // `live_def_count` counts defining INSTRUCTIONS: an id defined
                // at several positions of one instruction counts once.
                ids.clear();
                crate::effects::for_each_inst_def(func.inst(i), |d| {
                    defined.insert(d);
                    if !ids.contains(&d.id) {
                        ids.push(d.id);
                    }
                });
                for &id in &ids {
                    *live_defs.entry(id).or_insert(0) += 1;
                }
            }
        }
        LayoutDefs { live_defs, defined }
    }

    fn block_index(func: &MachFunction) -> HashMap<InstId, BlockId> {
        let mut block_of: HashMap<InstId, BlockId> = HashMap::default();
        for (idx, blk) in func.blocks.iter().enumerate() {
            let Ok(idx) = u32::try_from(idx) else {
                break;
            };
            for &i in &blk.insts {
                block_of.entry(i).or_insert(BlockId(idx));
            }
        }
        block_of
    }

    /// The reaching (last-in-layout) def of `id`.
    fn get(&self, id: &u32) -> Option<&InstId> {
        self.reaching.get(id)
    }

    /// `effects::live_def_count(func, id)`, where `func` is the function
    /// the index was built from (recognition does not change it).
    fn live_def_count(&self, func: &MachFunction, id: u32) -> usize {
        match self.layout_facts(func) {
            Some(layout) => layout.live_defs.get(&id).copied().unwrap_or(0),
            None => crate::effects::live_def_count(func, id),
        }
    }

    /// `block_of_inst(func, id)`.
    fn block_of_inst(&self, func: &MachFunction, id: InstId) -> Option<BlockId> {
        if self.block_of.get().is_none() && literal_allowed(&self.block_questions) {
            return block_of_inst(func, id);
        }
        let block_of = self.block_of.get_or_init(|| Self::block_index(func));
        block_of.get(&id).copied()
    }

    /// Whether some instruction in layout defines `v`.
    fn defined_in_layout(&self, func: &MachFunction, v: VReg) -> bool {
        match self.layout_facts(func) {
            Some(layout) => layout.defined.contains(&v),
            None => func.block_order.iter().any(|&bid| {
                func.block(bid)
                    .insts
                    .iter()
                    .any(|&id| crate::effects::inst_defines_vreg(func.inst(id), v))
            }),
        }
    }
}

fn build_def_map(func: &MachFunction) -> DefIndex {
    if crate::neon_array::boi_timing_enabled() {
        let t = std::time::Instant::now();
        let r = build_def_map_inner(func);
        FILL_NANOS.fetch_add(
            t.elapsed().as_nanos() as u64,
            std::sync::atomic::Ordering::Relaxed,
        );
        FILL_CALLS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        return r;
    }
    build_def_map_inner(func)
}

fn build_def_map_inner(func: &MachFunction) -> DefIndex {
    DefIndex::build(func)
}

/// The first block, in `func.blocks` order, listing `target`: the scan
/// [`DefIndex::block_of_inst`] answers from its index.
fn block_of_inst(func: &MachFunction, target: InstId) -> Option<BlockId> {
    for (idx, blk) in func.blocks.iter().enumerate() {
        if blk.insts.contains(&target) {
            return u32::try_from(idx).ok().map(BlockId);
        }
    }
    None
}
