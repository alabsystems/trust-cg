// trust-cg-opt - SOUND NEON constant/invariant array-fill store vectorizer (aarch64)
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
//! (never symbol-name-based), so it fires on the compiled
//! `__trustcg_array_fill_iN(dst, value, count)` helper — where `value`/`count`/
//! `dst` are runtime-invariant arguments, so the DUP path covers p7's
//! `comp = [0u8; 1024]` (60000 reps, one shared out-of-line helper) — AND on any
//! inline const/invariant fill.
//!
//! ## Lowering (vector-loop-in-front; mirrors `neon_bytesum`/`neon_map`)
//!
//! The pass is PURELY ADDITIVE: it inserts a NEON main loop in front of the
//! scalar loop and NEVER edits the scalar loop's instructions. `WIDTH_ELEMS =
//! 32 / elem_size` elements are stored per vector iteration:
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
//! * VB: `NeonStpQPost [qb, qb, p, #32]` (one instruction, 32 identical bytes =
//!   `WIDTH_ELEMS` elements, post-index `p += 32`); `B -> vl`.
//! * VL: `AddRI iv, iv, WIDTH_ELEMS; B -> vh`.
//! * VX: `B -> scalar-header`.
//! * COMMIT: redirect the preheader terminator from the scalar header to the
//!   vector entry (the precheck or vh). Point of no return.
//!
//! ## Why this is SOUND
//!
//! The scalar loop stores `value` to every address in `[base, base +
//! bound*elem_size)` in ascending order and reads NOTHING. The vector store set
//! is a SUBSET of that set: the vector body runs only while `iv <u main_bound =
//! bound-(WIDTH_ELEMS-1)`, so each 32-byte block `[base+iv*es, base+iv*es+32)`
//! spans elements `iv .. iv+WIDTH_ELEMS-1`, every one `< bound` — an address the
//! scalar loop also writes, with the SAME broadcast value, in ascending order.
//! So post-transform memory (vector prefix + untouched scalar tail) is
//! byte-for-byte identical to scalar-only. The loop reads nothing, so there is
//! no aliasing question. `p == base + iv*elem_size` at every header eval because
//! `32 == WIDTH_ELEMS*elem_size` (the post-index steps `p` by 32 while the latch
//! steps `iv` by `WIDTH_ELEMS`).
//!
//! Every opcode emitted (`NeonDupGen`, `NeonMovi`, `NeonStpQPost`, `Movz`,
//! `Movk`, `Madd`, `AddRR`, `AddRI`, `SubRI`, `CmpRR`, `CmpRI`, `BCond`, `B`) is
//! already coverage-credited — no new emittable opcode, no new proof. The pass
//! removes NO bounds check (the helper carries none), so it adds no debt and
//! creates no obligation.
//!
//! Default-ON at O2/Os/O3 (never O0/O1). Disable with
//! `TRUST_CG_DISABLE_PASSES=neon_fill`.

use std::collections::{HashMap, HashSet};

use trust_cg_ir::{
    AArch64Opcode, BlockId, InstId, MachFunction, MachInst, MachOperand, RegClass, VReg,
};

use crate::dom::DomTree;
use crate::loops::LoopAnalysis;
use crate::pass_manager::{AnalysisCache, MachinePass};

#[cfg(test)]
mod tests;

/// Bytes per 128-bit Q register / per NEON store lane group. The paired
/// `NeonStpQPost` writes `2 * 16 = 32` bytes per iteration.
const BYTES_PER_ITER: i64 = 32;

/// Store-pair instructions issued per vector iteration. Two `STP qb, qb`
/// (64 bytes) halves the loop overhead per byte relative to the original
/// single pair — glibc's hand-tuned `memset` (what LLVM lowers this shape
/// to) runs a 64-byte inner loop, and the measured v2_memfill gap (1.104x
/// vs LLVM) was the 32-byte kernel's extra add/cmp/branch per block. The
/// in-bounds license scales unchanged: the vector header admits only
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
        if changed && std::env::var("TRUST_CG_DUMP_NEONFILL").is_ok() {
            eprintln!("[neon-fill] fn={} vectorized={}", func.name, self.fired);
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
        let dump = std::env::var("TRUST_CG_DUMP_NEONFILL").is_ok();
        macro_rules! bail {
            ($($t:tt)*) => {{
                if dump {
                    eprintln!("[neon-fill] bail@{}: {}", func.name, format!($($t)*));
                }
                return None;
            }};
        }
        if dump {
            eprintln!(
                "[neon-fill] consider@{} header={:?} latch={:?} body={}",
                func.name,
                header,
                latch,
                body.len()
            );
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
        let Some(iv) = find_induction(func, &def, latch) else {
            bail!("no +1 iv writeback in latch");
        };
        if iv.class != RegClass::Gpr64 {
            bail!("iv class not Gpr64 (iv={:?})", iv.class);
        }

        // Store shape: `base[iv*elem_size] = value`, elem_size == store width.
        let Some((base, elem_size, value_reg)) = store_info(func, &def, &loop_insts, iv, store_id)
        else {
            bail!("store is not base+iv*elem_size unit-stride");
        };
        if base == iv {
            bail!("base aliases iv");
        }

        // `base` loop-invariant: NOT defined in the loop, and its def dominates
        // the preheader (fail-safe).
        if !is_loop_invariant(func, &def, dom, &loop_insts, preheader, base) {
            bail!("base not loop-invariant");
        }

        // Stored value source: a constant (through copies/Movz/Movk), or a
        // runtime-invariant register. A value defined INSIDE the loop, multi-def,
        // or iv-dependent BAILs (broadcasting a stale value would miscompile).
        let value = if let Some(k) = const_value(func, &def, value_reg) {
            if byte_replicable(k, elem_size) {
                ValueSrc::ConstByteRepl(low_byte(k))
            } else {
                ValueSrc::ConstGeneral(k)
            }
        } else if is_loop_invariant(func, &def, dom, &loop_insts, preheader, value_reg) {
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
            &def,
            dom,
            &loop_insts,
            body,
            preheader,
            header,
            latch,
            iv,
            dump,
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

        if dump {
            eprintln!(
                "[neon-fill] RECOGNIZED@{} iv={:?} base={:?} elem_size={} bound={:?} value={:?}",
                func.name, iv, base, elem_size, bound, value
            );
        }
        Some(Recognized {
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
fn find_induction(func: &MachFunction, def: &HashMap<u32, InstId>, latch: BlockId) -> Option<VReg> {
    // (1) In-place `AddRI(iv, iv, 1)` / `AddRR(iv, iv, one)`.
    for &id in &func.block(latch).insts {
        let inst = func.inst(id);
        match inst.opcode {
            AArch64Opcode::AddRI
                if inst.operands.len() == 3 && imm_of(&inst.operands[2]) == Some(1) =>
            {
                let d = vreg_of(&inst.operands[0])?;
                let s = vreg_of(&inst.operands[1])?;
                if d == s && d.class == RegClass::Gpr64 {
                    return Some(d);
                }
            }
            AArch64Opcode::AddRR if inst.operands.len() == 3 => {
                let d = vreg_of(&inst.operands[0])?;
                let a = vreg_of(&inst.operands[1])?;
                let b = vreg_of(&inst.operands[2])?;
                if d.class == RegClass::Gpr64
                    && ((a == d && const_value(func, def, b) == Some(1))
                        || (b == d && const_value(func, def, a) == Some(1)))
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
                    && vreg_of(&si.operands[1]) == Some(d)
                    && imm_of(&si.operands[2]) == Some(1) =>
            {
                return Some(d);
            }
            AArch64Opcode::AddRR if si.operands.len() == 3 => {
                let a = vreg_of(&si.operands[1])?;
                let b = vreg_of(&si.operands[2])?;
                if (a == d && const_value(func, def, b) == Some(1))
                    || (b == d && const_value(func, def, a) == Some(1))
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
    def: &HashMap<u32, InstId>,
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
    let transfer = vreg_of(inst.operands.first()?)?;
    if !matches!(transfer.class, RegClass::Gpr32 | RegClass::Gpr64) {
        return None;
    }
    match inst.opcode {
        AArch64Opcode::StrbRI | AArch64Opcode::StrhRI | AArch64Opcode::StrRI => {
            if inst.operands.len() != 3 || imm_of(&inst.operands[2]) != Some(0) {
                return None;
            }
            let value = vreg_of(&inst.operands[0])?;
            let addr = vreg_of(&inst.operands[1])?;
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
            let value = vreg_of(&inst.operands[0])?;
            let base = vreg_of(&inst.operands[1])?;
            let index = vreg_of(&inst.operands[2])?;
            let enc = imm_of(&inst.operands[3])?;
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
    def: &HashMap<u32, InstId>,
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
            let a = vreg_of(&inst.operands[1])?;
            let b = vreg_of(&inst.operands[2])?;
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
            let f1 = vreg_of(&inst.operands[1])?;
            let f2 = vreg_of(&inst.operands[2])?;
            let base = vreg_of(&inst.operands[3])?;
            let es = |f: VReg| const_value(func, def, f) == Some(elem_size);
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

/// A forward `BCond LT/LO -> want` in `blk` (the loop-continue direction).
fn has_forward_branch_to(func: &MachFunction, blk: BlockId, want: BlockId) -> bool {
    for &id in &func.block(blk).insts {
        let inst = func.inst(id);
        if inst.opcode == AArch64Opcode::BCond && inst.operands.len() == 2 {
            let Some(cc) = imm_of(&inst.operands[0]) else {
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
    def: &HashMap<u32, InstId>,
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
    if let Some(n) = const_value(func, def, rhs) {
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
    def: &HashMap<u32, InstId>,
    dom: &DomTree,
    loop_insts: &HashSet<InstId>,
    body: &HashSet<BlockId>,
    preheader: BlockId,
    header: BlockId,
    latch: BlockId,
    iv: VReg,
    dump: bool,
) -> Option<(Bound, bool, BlockId)> {
    // --- NATIVE: the continue-test is in the header.
    if let Some((_, imm_rhs, reg_rhs)) = find_iv_cmp(func, def, header, iv) {
        // A forward BCond whose taken-target is a body block, plus a fallthrough
        // leaving the loop.
        let mut taken: Option<BlockId> = None;
        for &id in &func.block(header).insts {
            let inst = func.inst(id);
            if inst.opcode == AArch64Opcode::BCond && inst.operands.len() == 2 {
                let cc = imm_of(&inst.operands[0])?;
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
    let Some((_, imm_rhs, reg_rhs)) = find_iv_cmp(func, def, latch, iv) else {
        if dump {
            eprintln!("[neon-fill] test-bail: no iv compare in header or latch");
        }
        return None;
    };
    if !has_forward_branch_to(func, latch, header) {
        if dump {
            eprintln!("[neon-fill] test-bail: latch has no forward LT/LO back-branch to header");
        }
        return None;
    }
    // The preheader must carry a matching entry guard on the same iv-vs-bound
    // compare that forward-branches to the header. This makes entering the header
    // (the body) always guarded by `iv < bound` at loop entry.
    let Some((_, g_imm, g_reg)) = find_iv_cmp(func, def, preheader, iv) else {
        if dump {
            eprintln!("[neon-fill] test-bail: rotated loop lacks a preheader entry-guard compare");
        }
        return None;
    };
    if !has_forward_branch_to(func, preheader, header) {
        if dump {
            eprintln!("[neon-fill] test-bail: preheader entry guard is not a forward LT/LO branch");
        }
        return None;
    }
    // The entry guard and latch test must compare against the SAME bound.
    if g_imm != imm_rhs
        || g_reg.map(|v| strip_copies(func, def, v)) != reg_rhs.map(|v| strip_copies(func, def, v))
    {
        if dump {
            eprintln!("[neon-fill] test-bail: entry guard bound differs from latch bound");
        }
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
        if dump {
            eprintln!("[neon-fill] test-bail: cannot determine rotated exit");
        }
        return None;
    };
    if exit != pre_exit {
        if dump {
            eprintln!("[neon-fill] test-bail: latch/preheader exits disagree");
        }
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
    def: &HashMap<u32, InstId>,
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
        return !func.block_order.iter().any(|&bid| {
            func.block(bid)
                .insts
                .iter()
                .any(|&id| crate::effects::inst_defines_vreg(func.inst(id), v))
        });
    };
    let Some(db) = block_of_inst(func, d) else {
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

fn apply(func: &mut MachFunction, rec: &Recognized) -> bool {
    let width_elems = BYTES_PER_ITER / rec.elem_size;
    let block_elems = STORE_PAIRS_PER_ITER * width_elems;

    // Fresh blocks: an optional runtime-bound precheck, then vh/vb/vl/vx.
    let pv = matches!(rec.bound, Bound::Runtime(_)).then(|| func.create_block());
    let vh = func.create_block();
    let vb = func.create_block();
    let vl = func.create_block();
    let vx = func.create_block();
    let mut fresh: Vec<BlockId> = Vec::new();
    if let Some(pv) = pv {
        fresh.push(pv);
    }
    fresh.extend([vh, vb, vl, vx]);
    insert_new_blocks_before(func, rec.header, &fresh);

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
    let qb = alloc(func, RegClass::Fpr128);
    match rec.value {
        ValueSrc::ConstByteRepl(b) => {
            // MOVI Vd.16B, #b — every one of the 16 byte lanes is `b`, so every
            // elem_size-byte element equals the value.
            emit_before(func, pre, AArch64Opcode::NeonMovi, vec![vreg(qb), imm(b)]);
        }
        ValueSrc::ConstGeneral(k) => {
            let w = materialize_before(func, pre, k);
            emit_before(
                func,
                pre,
                AArch64Opcode::NeonDupGen,
                vec![vreg(qb), vreg(w), imm(rec.elem_size)],
            );
        }
        ValueSrc::Invariant(v) => {
            emit_before(
                func,
                pre,
                AArch64Opcode::NeonDupGen,
                vec![vreg(qb), vreg(v), imm(rec.elem_size)],
            );
        }
    }

    // --- Preheader: running store pointer `p = base + iv*elem_size`.
    let p = alloc(func, RegClass::Gpr64);
    if rec.elem_size == 1 {
        emit_before(
            func,
            pre,
            AArch64Opcode::AddRR,
            vec![vreg(p), vreg(rec.base), vreg(rec.iv)],
        );
    } else {
        let c_es = alloc(func, RegClass::Gpr64);
        emit_before(
            func,
            pre,
            AArch64Opcode::Movz,
            vec![vreg(c_es), imm(rec.elem_size)],
        );
        emit_before(
            func,
            pre,
            AArch64Opcode::Madd,
            vec![vreg(p), vreg(rec.iv), vreg(c_es), vreg(rec.base)],
        );
    }

    // --- main_bound = bound - (WIDTH_ELEMS-1). Runtime bound: compute in a
    // precheck block that skips the vector loop for `n < WIDTH_ELEMS` (so the
    // wrapped main_bound is dead). Const bound: materialize directly.
    let main_bound = alloc(func, RegClass::Gpr64);
    match rec.bound {
        Bound::Runtime(n) => {
            let pv = pv.expect("runtime bound -> precheck block");
            emit(
                func,
                pv,
                AArch64Opcode::SubRI,
                vec![vreg(main_bound), vreg(n), imm(block_elems - 1)],
            );
            emit(
                func,
                pv,
                AArch64Opcode::CmpRI,
                vec![vreg(n), imm(block_elems)],
            );
            emit(
                func,
                pv,
                AArch64Opcode::BCond,
                vec![imm(CC_LT), block(rec.header)],
            );
            emit(func, pv, AArch64Opcode::B, vec![block(vh)]);
        }
        Bound::Const(n) => {
            let mb = materialize_before(func, pre, n - (block_elems - 1));
            emit_before(
                func,
                pre,
                AArch64Opcode::MovR,
                vec![vreg(main_bound), vreg(mb)],
            );
        }
    }

    // --- Vector header: `iv <u main_bound` admits only full in-bounds blocks.
    emit(
        func,
        vh,
        AArch64Opcode::CmpRR,
        vec![vreg(rec.iv), vreg(main_bound)],
    );
    emit(func, vh, AArch64Opcode::BCond, vec![imm(CC_LO), block(vb)]);
    emit(func, vh, AArch64Opcode::B, vec![block(vx)]);

    // --- Vector body: STORE_PAIRS_PER_ITER paired post-index stores
    // `STP qb, qb, [p], #32` — each 32 identical bytes; the block covers
    // BLOCK_ELEMS elements, all the broadcast value.
    for _ in 0..STORE_PAIRS_PER_ITER {
        emit(
            func,
            vb,
            AArch64Opcode::NeonStpQPost,
            vec![vreg(qb), vreg(qb), vreg(p), imm(BYTES_PER_ITER)],
        );
    }
    emit(func, vb, AArch64Opcode::B, vec![block(vl)]);

    // --- Vector latch: advance the scalar induction by BLOCK_ELEMS (p is
    // advanced 32 bytes by EACH store's post-index, keeping p == base+iv*es).
    emit(
        func,
        vl,
        AArch64Opcode::AddRI,
        vec![vreg(rec.iv), vreg(rec.iv), imm(block_elems)],
    );
    emit(func, vl, AArch64Opcode::B, vec![block(vh)]);

    // --- Vector exit: hand off to the scalar loop for the [iv, bound) remainder.
    //   * NATIVE: the header re-tests `iv < bound`, so branch there directly.
    //   * ROTATED (do-while): the header is the body (no pre-test). If the vector
    //     consumed everything (`iv >=u bound`), entering the body would store one
    //     element PAST the end. Guard with `iv >=u bound -> true exit`; otherwise
    //     fall into the body, which writes the disjoint tail `[iv, bound)`.
    if rec.rotated {
        match rec.bound {
            Bound::Runtime(n) => {
                emit(func, vx, AArch64Opcode::CmpRR, vec![vreg(rec.iv), vreg(n)]);
            }
            Bound::Const(n) => {
                let nb = materialize_before(func, pre, n);
                emit(func, vx, AArch64Opcode::CmpRR, vec![vreg(rec.iv), vreg(nb)]);
            }
        }
        emit(
            func,
            vx,
            AArch64Opcode::BCond,
            vec![imm(CC_HS), block(rec.exit)],
        );
        emit(func, vx, AArch64Opcode::B, vec![block(rec.header)]);
    } else {
        emit(func, vx, AArch64Opcode::B, vec![block(rec.header)]);
    }

    // --- COMMIT: splice the fresh blocks in front of the scalar loop. Point of
    // no return; runs only after all emission succeeded.
    let entry = pv.unwrap_or(vh);
    if !rewrite_block_target(func.inst_mut(rec.preheader_term), rec.header, entry) {
        return false;
    }
    remove_cfg_edge(func, rec.preheader, rec.header);
    func.add_edge(rec.preheader, entry);
    func.add_edge(vx, rec.header);
    if rec.rotated {
        func.add_edge(vx, rec.exit);
    }
    true
}

/// Materialize a (non-negative, fits-u32 or full-u64) constant into a fresh
/// `Gpr64` via `Movz` + `Movk` chunks, before `before`. Returns the register.
fn materialize_before(func: &mut MachFunction, before: InstId, value: i64) -> VReg {
    let d = alloc(func, RegClass::Gpr64);
    let bits = value as u64;
    // Low 16 via Movz, then any nonzero higher halfwords via Movk.
    emit_before(
        func,
        before,
        AArch64Opcode::Movz,
        vec![vreg(d), imm((bits & 0xFFFF) as i64)],
    );
    for hw in 1..4u32 {
        let chunk = (bits >> (hw * 16)) & 0xFFFF;
        if chunk != 0 {
            emit_before(
                func,
                before,
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
        // A vreg with several live defs has no single reaching definition: the
        // map is last-wins over the emitted layout, so it names whichever def
        // comes last, which need not be the one that reaches THIS use. Stop
        // rather than resolve through it. The frontend lowers every block
        // parameter to one copy per predecessor into the SAME vreg, so an
        // `if`/`match` value is multi-def by construction.
        if crate::effects::live_def_count(func, v.id) != 1 {
            return v;
        }
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
            // Same hazard as in `strip_copies`, reached directly rather than
            // through a copy chain: for a merge vreg the map names the arm that
            // comes last in layout order. Broadcasting that arm's constant
            // across the whole fill is wrong on every other path. (The `Movk`
            // arm below is not reachable for a merge vreg — its def is a copy,
            // not a `Movk` — and does its own same-block accumulation, so a
            // legitimate `Movz`+`Movk` materialization is unaffected.)
            if crate::effects::live_def_count(func, v.id) != 1 {
                return None;
            }
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
                if !crate::effects::inst_defines_vreg(pi, v) {
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
                    _ => return None,
                }
            }
            let value = crate::reaching_const::apply_movk(inst, v, acc?)?;
            i64::try_from(value).ok()
        }
        _ => None,
    }
}

pub(crate) static FILL_NANOS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
pub(crate) static FILL_CALLS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

fn build_def_map(func: &MachFunction) -> HashMap<u32, InstId> {
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

fn build_def_map_inner(func: &MachFunction) -> HashMap<u32, InstId> {
    crate::effects::build_reaching_def_map(func)
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

fn emit_before(
    func: &mut MachFunction,
    before: InstId,
    op: AArch64Opcode,
    operands: Vec<MachOperand>,
) -> InstId {
    let id = func.push_inst(MachInst::new(op, operands));
    insert_before_inst(func, before, &[id]);
    id
}

fn insert_before_inst(func: &mut MachFunction, before: InstId, new_insts: &[InstId]) -> bool {
    for block in &mut func.blocks {
        if let Some(pos) = block.insts.iter().position(|&id| id == before) {
            for (off, &id) in new_insts.iter().enumerate() {
                block.insts.insert(pos + off, id);
            }
            return true;
        }
    }
    false
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
