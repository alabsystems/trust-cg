// trust-cg-opt - SOUND NEON affine iota-fill store vectorizer (aarch64)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! # NEON affine iota-fill store vectorizer (`neon-iota-fill`)
//!
//! Vectorizes an innermost, counted, contiguous i32 store loop of the shape
//!
//! ```text
//! for iv in start..bound { base[iv] = trunc32(iv) + inv }   // i32 elements
//! ```
//!
//! where `inv` is a loop-invariant `Gpr32` register, a constant, or absent
//! (`base[iv] = trunc32(iv)`), with a loop-invariant `base`, ZERO loads, and no
//! other memory/effectful op. This is the affine sibling of `neon_fill` (which
//! requires an iteration-INVARIANT stored value and so BAILS on this shape):
//! the canonical source is `a[i] = (i as u32).wrapping_add(r)`.
//!
//! ## Lowering (vector-loop-in-front; mirrors `neon_fill`)
//!
//! PURELY ADDITIVE: a NEON main loop is spliced in FRONT of the scalar loop;
//! the scalar loop is NEVER edited and runs the `[iv, bound)` remainder.
//! 16 elements (64 bytes) are stored per vector iteration:
//!
//! * PREHEADER (once per loop entry, before the preheader terminator):
//!   * IOTA constant: a fresh 16-byte stack slot receives the two 64-bit
//!     halves `0x0000000100000000` / `0x0000000300000002` (i32 lanes
//!     `{0,1,2,3}` little-endian) via `Movz/Movk` + `StrRI`, then
//!     `NeonLd1Post` loads `q_iota.4S = {0,1,2,3}`.
//!   * `w0 = trunc32(iv) + inv` (`MovR w,x` + `AddRR`; const `inv` is
//!     materialized; absent `inv` uses the bare trunc), then
//!     `NeonDupGen qb.4S, w0` and `v0 = qb + q_iota` — lane `k` of `v0` is
//!     `V(iv+k)` where `V(j) = trunc32(j) + inv (mod 2^32)`.
//!   * Splat step vectors `c4/c8/c12/c16` (`Movz` + `NeonDupGen`).
//!   * Running store pointer `p = base + iv*4` (`Movz` + `Madd`).
//!   * `main_bound = bound - 15` (const bound: materialized directly; runtime
//!     bound `n`: computed in a precheck block that first skips to the scalar
//!     loop when `n <s 16`, so the wrapped subtraction is dead).
//! * VH (entry guard): `iv <u main_bound` else scalar header.
//! * VB (single-block, bottom-tested):
//!   `v1=v0+c4; v2=v0+c8; v3=v0+c12;`
//!   `STP q(v0),q(v1),[p],#32; STP q(v2),q(v3),[p],#32;`
//!   `v0+=c16; iv+=16; iv <u main_bound -> VB` else scalar header.
//!
//! ## Why this is SOUND
//!
//! * STORE SET: the vector body runs only while `iv <u main_bound = bound-15`,
//!   so the 64-byte block it stores spans elements `iv..iv+15`, every one
//!   `< bound` — a PREFIX SUBSET of the scalar loop's store set, written in the
//!   same ascending order. The loop reads nothing, so there is no aliasing
//!   question and no observable difference in intermediate states.
//! * VALUES: the scalar stores `V(j) = trunc32(j) + inv (mod 2^32)` at element
//!   `j` (`Gpr32` arithmetic is mod `2^32`). By the induction in the module
//!   text, lane `k` of the stored quad at `iv` is `V(iv+k)`: `trunc32` is a
//!   ring homomorphism (`trunc32(j+16) = trunc32(j)+16 mod 2^32`) and
//!   `NeonAddV.4S` is lane-wise wrapping i32 addition — byte-identical memory.
//! * IV HANDOFF: the vector latch keeps `iv` exact (`+16` per 16 elements), so
//!   the untouched scalar loop stores exactly the `[iv, bound)` tail. The
//!   scalar header re-tests `iv < bound` itself (NATIVE loops only; rotated
//!   do-while loops BAIL).
//! * REGISTER STATE: recognition REQUIRES every vreg defined in the loop body
//!   (other than `iv`) to be single-def and never used outside the loop, so
//!   skipping scalar iterations cannot leave a stale value that anything
//!   observes. The body whitelist admits no call/trap/load, so no skipped
//!   iteration could have trapped.
//! * STRICT IV WALK: both the store index and the trunc operand must reach the
//!   iv register ITSELF through plain copies (`MovR`/`Copy`/`AddRI #0`) — a
//!   chain that reaches the latch's incremented `iv+1` value instead does NOT
//!   match (the canonicalizing compare used by the invariant-fill pass would
//!   conflate the two; this pass refuses the ambiguity outright).
//!
//! Every opcode emitted (`NeonDupGen`, `NeonAddV`, `NeonLd1Post`,
//! `NeonStpQPost`, `AddPCRel`, `Movz`, `Movk`, `MovR`, `AddRR`, `AddRI`,
//! `SubRI`, `Madd`, `StrRI`, `CmpRR`, `CmpRI`, `BCond`, `B`) is already
//! coverage-credited — no new emittable opcode, no new proof obligation. The
//! pass removes NO bounds check.
//!
//! Default-ON at O2/Os/O3 (never O0/O1). Disable with
//! `TRUST_CG_DISABLE_PASSES=neon_iota_fill`.

use std::collections::{HashMap, HashSet};

use trust_cg_ir::{
    AArch64Opcode, BlockId, InstId, MachFunction, MachInst, MachOperand, RegClass, StackSlot, VReg,
    regs::SP,
};

use crate::dom::DomTree;
use crate::loops::LoopAnalysis;
use crate::pass_manager::{AnalysisCache, MachinePass};

/// i32 element size in bytes (`.4S` lanes only).
const ELEM_SIZE: i64 = 4;
/// Elements stored per vector iteration (4 Q registers = 64 bytes).
const WIDTH_ELEMS: i64 = 16;
/// `.4S` arrangement code (shared NEON operand convention).
const ARR_S4: i64 = 5;

/// AArch64 condition code for unsigned lower (`LO`).
const CC_LO: i64 = 3;
/// AArch64 condition code for signed less-than (`LT`).
const CC_LT: i64 = 11;

// ---------------------------------------------------------------------------
// Pass
// ---------------------------------------------------------------------------

/// The `neon-iota-fill` machine pass.
#[derive(Default)]
pub struct NeonIotaFillPass {
    fired: usize,
}

impl NeonIotaFillPass {
    pub fn new() -> Self {
        Self { fired: 0 }
    }
    /// Loops vectorized in the last `run`.
    pub fn fired(&self) -> usize {
        self.fired
    }
}

impl MachinePass for NeonIotaFillPass {
    fn name(&self) -> &str {
        "neon-iota-fill"
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

impl NeonIotaFillPass {
    fn run_core(&mut self, func: &mut MachFunction, dom: &DomTree, loops: &LoopAnalysis) -> bool {
        self.fired = 0;
        // Recognize first (read-only); applying a plan only ADDS blocks (never
        // renumbers ids or edits other loops), so recognized data for other
        // loops stays valid.
        let mut plans = Vec::new();
        // One whole-arena def map for the sweep; recognition is read-only and
        // plans are applied afterwards.
        let def_map = build_def_map(func);
        for lp in loops.all_loops() {
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
        if changed && std::env::var("TRUST_CG_DUMP_NEONIOTAFILL").is_ok() {
            eprintln!(
                "[neon-iota-fill] fn={} vectorized={}",
                func.name, self.fired
            );
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

/// The loop-invariant addend applied to `trunc32(iv)`.
#[derive(Clone, Copy, Debug)]
enum Addend {
    /// `base[iv] = trunc32(iv)` (no addend).
    None,
    /// A loop-invariant `Gpr32` register.
    Invariant(VReg),
    /// A compile-time constant.
    Const(i64),
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
    /// The loop-invariant addend in `base[iv] = trunc32(iv) + addend`.
    addend: Addend,
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
        let dump = std::env::var("TRUST_CG_DUMP_NEONIOTAFILL").is_ok();
        macro_rules! bail {
            ($($t:tt)*) => {{
                if dump {
                    eprintln!("[neon-iota-fill] bail@{}: {}", func.name, format!($($t)*));
                }
                return None;
            }};
        }
        if dump {
            eprintln!(
                "[neon-iota-fill] consider@{} header={:?} latch={:?} body={}",
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
        // It was rebuilt inside every per-loop attempt — the same defect
        // measured at ~99% of eight sibling passes this session.

        // Whitelist every opcode in the loop body. Loads, calls, traps,
        // atomics, and anything unmodeled are NOT whitelisted -> BAIL
        // (closed-world). This is the ZERO-loads / no-skipped-trap guarantee.
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

        // SINGLE-EXIT structure: the ONLY way out of the loop is the header's
        // bound test. Any other body block branching outside (a side exit —
        // e.g. an abort/trap diamond) would let the vector prefix SKIP that
        // test's iterations -> BAIL. The header must have exactly one non-body
        // successor and one body successor.
        for &b in body {
            let succs = &func.block(b).succs;
            if b == header {
                if succs.len() != 2
                    || succs.iter().filter(|s| body.contains(s)).count() != 1
                    || succs.iter().filter(|s| !body.contains(s)).count() != 1
                {
                    bail!("header exit structure not a single bound-test exit");
                }
            } else if succs.iter().any(|s| !body.contains(s)) {
                bail!("side exit from body block {:?}", b);
            }
        }
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

        // Def discipline: every vreg defined inside the loop must be
        // single-def in the WHOLE function, except `iv` (exactly two defs: the
        // latch writeback + one init OUTSIDE the loop). This removes any
        // stale-def / def-map ambiguity and, combined with the external-use
        // scan below, guarantees no loop-defined value is observable after the
        // loop.
        // NOTE: all scans below walk BLOCK-RESIDENT instructions only —
        // `func.insts` also holds detached ghosts (e.g. a bounds-check-elim'd
        // carrier) that are no longer part of the program.
        let live_ids: Vec<InstId> = func
            .blocks
            .iter()
            .flat_map(|blk| blk.insts.iter().copied())
            .collect();
        let mut def_counts: HashMap<u32, usize> = HashMap::new();
        for &id in &live_ids {
            let inst = func.inst(id);
            if produces_def(inst.opcode)
                && let Some(MachOperand::VReg(v)) = inst.operands.first()
            {
                *def_counts.entry(v.id).or_insert(0) += 1;
            }
        }
        let mut body_defs: HashSet<u32> = HashSet::new();
        for &id in &loop_insts {
            let inst = func.inst(id);
            if produces_def(inst.opcode)
                && let Some(MachOperand::VReg(v)) = inst.operands.first()
            {
                body_defs.insert(v.id);
            }
        }
        for &vid in &body_defs {
            let n = def_counts.get(&vid).copied().unwrap_or(0);
            if vid == iv.id {
                // The latch writeback + exactly one out-of-loop init.
                let in_loop = live_ids
                    .iter()
                    .filter(|&&id| {
                        let inst = func.inst(id);
                        produces_def(inst.opcode)
                            && inst.operands.first().and_then(vreg_of).map(|v| v.id) == Some(vid)
                            && loop_insts.contains(&id)
                    })
                    .count();
                if n != 2 || in_loop != 1 {
                    bail!(
                        "iv def discipline violated (defs={}, in-loop={})",
                        n,
                        in_loop
                    );
                }
            } else if n != 1 {
                bail!("multi-def loop vreg v{} (defs={})", vid, n);
            }
        }
        // No external uses of loop-defined vregs (other than `iv`): skipping
        // scalar iterations must not leave an observable stale register.
        for &id in &live_ids {
            if loop_insts.contains(&id) {
                continue;
            }
            for op in &func.inst(id).operands {
                if let MachOperand::VReg(v) = op
                    && v.id != iv.id
                    && body_defs.contains(&v.id)
                {
                    bail!("loop-defined v{} used outside the loop", v.id);
                }
            }
        }

        // Store shape: `StrRI w,[addr,#0]` with `addr = Madd(iv, 4, base)`, or
        // `StrRO w,[base, iv, lsl #2]`. STRICT iv walk (copies only, must
        // reach `iv` itself).
        let Some((base, value_reg)) = store_info(func, &def, &loop_insts, iv, store_id) else {
            bail!("store is not base + iv*4 with a Gpr32 value");
        };
        if base == iv {
            bail!("base aliases iv");
        }
        if !is_loop_invariant(func, &def, dom, &loop_insts, preheader, base) {
            bail!("base not loop-invariant");
        }

        // Stored value: `trunc32(iv)` (+ invariant Gpr32 | + const).
        let Some(addend) = value_shape(func, &def, dom, &loop_insts, preheader, iv, value_reg)
        else {
            bail!("stored value is not trunc32(iv) [+ invariant/const]");
        };

        // The NATIVE loop-continue test `iv < bound` in the header (rotated
        // do-while loops BAIL: the scalar tail could not re-test on entry).
        let Some(bound) =
            recognize_native_test(func, &def, dom, &loop_insts, body, preheader, header, iv)
        else {
            bail!("no NATIVE forward iv<bound header test");
        };

        // Vector-benefit / wrap-freedom: at least one full 64-byte block.
        if let Bound::Const(n) = bound {
            if n < WIDTH_ELEMS {
                bail!("const bound {} < {}", n, WIDTH_ELEMS);
            }
            let mb = n - (WIDTH_ELEMS - 1);
            if !(0..=i64::from(u32::MAX)).contains(&mb) {
                bail!("const main_bound {} out of materializable range", mb);
            }
        }

        if dump {
            eprintln!(
                "[neon-iota-fill] RECOGNIZED@{} iv={:?} base={:?} bound={:?} addend={:?}",
                func.name, iv, base, bound, addend
            );
        }
        Some(Recognized {
            header,
            preheader,
            preheader_term,
            iv,
            bound,
            base,
            addend,
        })
    }
}

/// Find the `+1` Gpr64 induction writeback in the latch (in-place
/// `AddRI(iv, iv, 1)` or the phi-copy form `iv = MovR(next)`,
/// `next = AddRI(iv, 1)`).
fn find_induction(func: &MachFunction, def: &HashMap<u32, InstId>, latch: BlockId) -> Option<VReg> {
    for &id in &func.block(latch).insts {
        let inst = func.inst(id);
        if inst.opcode == AArch64Opcode::AddRI
            && inst.operands.len() == 3
            && imm_of(&inst.operands[2]) == Some(1)
        {
            let d = vreg_of(&inst.operands[0])?;
            let s = vreg_of(&inst.operands[1])?;
            if d == s && d.class == RegClass::Gpr64 {
                return Some(d);
            }
        }
    }
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
        if si.opcode == AArch64Opcode::AddRI
            && si.operands.len() == 3
            && vreg_of(&si.operands[1]) == Some(d)
            && imm_of(&si.operands[2]) == Some(1)
        {
            return Some(d);
        }
    }
    None
}

/// STRICT copy walk: `v` reaches EXACTLY the register `target` through
/// `MovR`/`Copy`/`AddRI #0` copies (class transitions allowed — every copy
/// preserves the low 32 bits, the only bits this pass consumes; use ONLY where
/// the consumer truncates to 32 bits anyway, i.e. the stored VALUE). Unlike
/// the canonicalizing `strip_copies` compare, a chain that resolves to the
/// incremented `iv+1` value does NOT match.
fn reaches_reg(func: &MachFunction, def: &HashMap<u32, InstId>, mut v: VReg, target: VReg) -> bool {
    for _ in 0..16 {
        if v == target {
            return true;
        }
        let Some(&d) = def.get(&v.id) else {
            return false;
        };
        match copy_like(func.inst(d)) {
            Some((dst, src)) if dst == v => v = src,
            _ => return false,
        }
    }
    false
}

/// STRICT FULL-WIDTH copy walk: like [`reaches_reg`] but every register in the
/// chain (including `v` itself) must be `Gpr64`. REQUIRED for anything with
/// 64-bit semantics — the store INDEX, `Madd` address factors, and the loop
/// bound compare — where a truncating `w <- x` copy in the chain would make
/// the scalar loop consume only the low 32 bits of the iv while the vector
/// path uses the full 64-bit value (divergent for `iv >= 2^32`; fail-closed).
fn reaches_reg64(
    func: &MachFunction,
    def: &HashMap<u32, InstId>,
    mut v: VReg,
    target: VReg,
) -> bool {
    if target.class != RegClass::Gpr64 {
        return false;
    }
    for _ in 0..16 {
        if v.class != RegClass::Gpr64 {
            return false;
        }
        if v == target {
            return true;
        }
        let Some(&d) = def.get(&v.id) else {
            return false;
        };
        match copy_like(func.inst(d)) {
            Some((dst, src)) if dst == v => v = src,
            _ => return false,
        }
    }
    false
}

/// Extract `(base, value)` from the single store, requiring the address to be
/// `base + iv*4` and the transfer register to be `Gpr32` (i32 elements only).
fn store_info(
    func: &MachFunction,
    def: &HashMap<u32, InstId>,
    loop_insts: &HashSet<InstId>,
    iv: VReg,
    store_id: InstId,
) -> Option<(VReg, VReg)> {
    let inst = func.inst(store_id);
    match inst.opcode {
        AArch64Opcode::StrRI => {
            if inst.operands.len() != 3 || imm_of(&inst.operands[2]) != Some(0) {
                return None;
            }
            let value = vreg_of(&inst.operands[0])?;
            if value.class != RegClass::Gpr32 {
                return None;
            }
            let addr = vreg_of(&inst.operands[1])?;
            let &ad = def.get(&addr.id)?;
            if !loop_insts.contains(&ad) {
                return None;
            }
            let ai = func.inst(ad);
            if ai.opcode != AArch64Opcode::Madd || ai.operands.len() != 4 {
                return None;
            }
            // addr = f1*f2 + f3; want iv*4 + base. FULL-WIDTH factor walk: a
            // truncated (Gpr32) iv factor would address base + trunc32(iv)*4.
            let f1 = vreg_of(&ai.operands[1])?;
            let f2 = vreg_of(&ai.operands[2])?;
            let b = vreg_of(&ai.operands[3])?;
            let es = |f: VReg| {
                f.class == RegClass::Gpr64 && const_value(func, def, f) == Some(ELEM_SIZE)
            };
            if (reaches_reg64(func, def, f1, iv) && es(f2))
                || (reaches_reg64(func, def, f2, iv) && es(f1))
            {
                Some((b, value))
            } else {
                None
            }
        }
        AArch64Opcode::StrRO => {
            // [Rt(value), Rn(base), Rm(index), Imm((option<<1)|S)]; want a
            // 32-bit transfer addressed `[base, Xindex, LSL #2]` EXACTLY:
            // packed extend == (LSL=0b011)<<1 | S=1. The UXTW/SXTW option
            // forms take a 32-bit index (address = base + ext32(index)*4) and
            // must NOT match — a truncated-iv index diverges from the vector
            // path's `base + iv*4` for `iv >= 2^32` (fail-closed).
            if inst.operands.len() != 4 {
                return None;
            }
            let value = vreg_of(&inst.operands[0])?;
            if value.class != RegClass::Gpr32 {
                return None;
            }
            let b = vreg_of(&inst.operands[1])?;
            let index = vreg_of(&inst.operands[2])?;
            let enc = imm_of(&inst.operands[3])?;
            if !reaches_reg64(func, def, index, iv) {
                return None;
            }
            if enc == 0b0111 {
                Some((b, value))
            } else {
                None
            }
        }
        _ => None,
    }
}

/// Recognize the stored value as `trunc32(iv) [+ invariant Gpr32 | + const]`.
fn value_shape(
    func: &MachFunction,
    def: &HashMap<u32, InstId>,
    dom: &DomTree,
    loop_insts: &HashSet<InstId>,
    preheader: BlockId,
    iv: VReg,
    value: VReg,
) -> Option<Addend> {
    if value.class != RegClass::Gpr32 {
        return None;
    }
    // Bare truncating copy of the iv.
    if reaches_reg(func, def, value, iv) {
        return Some(Addend::None);
    }
    let &vd = def.get(&value.id)?;
    if !loop_insts.contains(&vd) {
        return None;
    }
    let inst = func.inst(vd);
    match inst.opcode {
        AArch64Opcode::AddRR if inst.operands.len() == 3 => {
            let a = vreg_of(&inst.operands[1])?;
            let b = vreg_of(&inst.operands[2])?;
            let classify = |t: VReg, o: VReg| -> Option<Addend> {
                if !reaches_reg(func, def, t, iv) {
                    return None;
                }
                if let Some(k) = const_value(func, def, o) {
                    return Some(Addend::Const(k));
                }
                if o.class == RegClass::Gpr32
                    && is_loop_invariant(func, def, dom, loop_insts, preheader, o)
                {
                    return Some(Addend::Invariant(o));
                }
                None
            };
            classify(a, b).or_else(|| classify(b, a))
        }
        AArch64Opcode::AddRI if inst.operands.len() == 3 => {
            let s = vreg_of(&inst.operands[1])?;
            let k = imm_of(&inst.operands[2])?;
            if reaches_reg(func, def, s, iv) {
                Some(Addend::Const(k))
            } else {
                None
            }
        }
        _ => None,
    }
}

/// Recognize the NATIVE loop-continue test: a `CmpRR/CmpRI` on the FULL-WIDTH
/// iv in the header whose flags feed a forward `BCond LT/LO` into the body
/// (the compare must be the LAST flag-setter before that `BCond` — a stray
/// non-iv compare in between would mean the branch tests something else
/// entirely). Returns the bound.
#[allow(clippy::too_many_arguments)]
fn recognize_native_test(
    func: &MachFunction,
    def: &HashMap<u32, InstId>,
    dom: &DomTree,
    loop_insts: &HashSet<InstId>,
    body: &HashSet<BlockId>,
    preheader: BlockId,
    header: BlockId,
    iv: VReg,
) -> Option<Bound> {
    // Walk the header in order, tracking the LAST flag-setting instruction;
    // when the qualifying `BCond LT/LO -> body` appears, the flags it consumes
    // are exactly that instruction's. Every flag-setter the body whitelist
    // admits is CmpRR/CmpRI (no adds-with-flags), so tracking compares is
    // complete; an unmodeled flag-setter cannot appear here because the whole
    // body (header included) already passed `allowed_loop_op`.
    let mut last_cmp: Option<(VReg, Option<i64>, Option<VReg>)> = None;
    let mut cmp: Option<(Option<i64>, Option<VReg>)> = None;
    for &id in &func.block(header).insts {
        let inst = func.inst(id);
        match inst.opcode {
            AArch64Opcode::CmpRR if inst.operands.len() == 2 => {
                last_cmp = Some((
                    vreg_of(&inst.operands[0])?,
                    None,
                    vreg_of(&inst.operands[1]),
                ));
            }
            AArch64Opcode::CmpRI if inst.operands.len() == 2 => {
                last_cmp = Some((vreg_of(&inst.operands[0])?, imm_of(&inst.operands[1]), None));
            }
            AArch64Opcode::BCond if inst.operands.len() == 2 => {
                let cc = imm_of(&inst.operands[0])?;
                let tgt = *branch_targets(inst).first()?;
                if (cc == CC_LT || cc == CC_LO) && body.contains(&tgt) {
                    // FULL-WIDTH lhs walk: a Gpr32 compare would test only
                    // `trunc32(iv)` — different loop semantics for
                    // `iv >= 2^32` (fail-closed).
                    let (lhs, imm_rhs, reg_rhs) = last_cmp?;
                    if !reaches_reg64(func, def, lhs, iv) {
                        return None;
                    }
                    cmp = Some((imm_rhs, reg_rhs));
                }
            }
            _ => {}
        }
    }
    let (imm_rhs, reg_rhs) = cmp?;
    // The header must also have a non-loop exit successor (it re-tests for the
    // scalar tail).
    func.block(header)
        .succs
        .iter()
        .find(|s| !body.contains(s))?;
    if let Some(n) = imm_rhs {
        return Some(Bound::Const(n));
    }
    let rhs = reg_rhs?;
    if rhs.class != RegClass::Gpr64 {
        return None;
    }
    if let Some(n) = const_value(func, def, rhs) {
        return Some(Bound::Const(n));
    }
    let canon = strip_copies(func, def, rhs);
    if canon.class != RegClass::Gpr64 {
        return None;
    }
    if is_loop_invariant(func, def, dom, loop_insts, preheader, canon) {
        return Some(Bound::Runtime(canon));
    }
    None
}

/// A register is loop-invariant iff it is NOT defined anywhere in the loop
/// body and its (unique last) def dominates the preheader. Fail-safe.
fn is_loop_invariant(
    func: &MachFunction,
    def: &HashMap<u32, InstId>,
    dom: &DomTree,
    loop_insts: &HashSet<InstId>,
    preheader: BlockId,
    v: VReg,
) -> bool {
    for &id in loop_insts {
        let inst = func.inst(id);
        if produces_def(inst.opcode) && inst.operands.first().and_then(vreg_of) == Some(v) {
            return false;
        }
    }
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

/// Opcodes permitted anywhere in the loop body. Loads, calls, traps, atomics,
/// and any unmodeled effect are absent -> they BAIL (closed-world).
fn allowed_loop_op(op: AArch64Opcode) -> bool {
    use AArch64Opcode::*;
    matches!(
        op,
        AddRR | AddRI | SubRR | SubRI | MulRR | Madd | AndRR | AndRI | OrrRR | OrrRI | EorRR
            | LsrRI | LslRI | AsrRI | Movz | Movk | Movn | MovR | Copy | CmpRR | CmpRI | BCond | B
            // Exactly one store (checked separately). No LOAD opcode is
            // whitelisted, so any read BAILs.
            | StrRI | StrRO
    )
}

fn is_store(op: AArch64Opcode) -> bool {
    matches!(op, AArch64Opcode::StrRI | AArch64Opcode::StrRO)
}

// ---------------------------------------------------------------------------
// Transformation (vector-loop-in-front; additive, never edits the scalar loop)
// ---------------------------------------------------------------------------

fn apply(func: &mut MachFunction, rec: &Recognized) -> bool {
    // Fresh blocks: an optional runtime-bound precheck, the entry guard, and
    // the single-block bottom-tested vector body.
    let pv = matches!(rec.bound, Bound::Runtime(_)).then(|| func.create_block());
    let vh = func.create_block();
    let vb = func.create_block();
    let mut fresh: Vec<BlockId> = Vec::new();
    if let Some(pv) = pv {
        fresh.push(pv);
    }
    fresh.extend([vh, vb]);
    insert_new_blocks_before(func, rec.header, &fresh);

    // Internal edges among fresh blocks only; the preheader redirect is
    // deferred to the COMMIT so a lowering failure cannot break the CFG.
    if let Some(pv) = pv {
        func.add_edge(pv, vh);
        func.add_edge(pv, rec.header);
    }
    func.add_edge(vh, vb);
    func.add_edge(vh, rec.header);
    func.add_edge(vb, vb);
    func.add_edge(vb, rec.header);

    let pre = rec.preheader_term;

    // --- Preheader: IOTA constant {0,1,2,3} via a fresh 16-byte stack slot.
    let slot = func.alloc_stack_slot(StackSlot::new(16, 16));
    let slot_addr = alloc(func, RegClass::Gpr64);
    emit_before(
        func,
        pre,
        AArch64Opcode::AddPCRel,
        vec![
            vreg(slot_addr),
            MachOperand::PReg(SP),
            MachOperand::StackSlot(slot),
        ],
    );
    // Little-endian i32 lanes: [0,1] then [2,3].
    let t0 = materialize_before(func, pre, 0x0000_0001_0000_0000);
    let t1 = materialize_before(func, pre, 0x0000_0003_0000_0002);
    emit_before(
        func,
        pre,
        AArch64Opcode::StrRI,
        vec![vreg(t0), vreg(slot_addr), imm(0)],
    );
    emit_before(
        func,
        pre,
        AArch64Opcode::StrRI,
        vec![vreg(t1), vreg(slot_addr), imm(8)],
    );
    // LD1 post-indexes its base; use a scratch copy so `slot_addr` stays dead
    // afterwards either way.
    let ld_addr = alloc(func, RegClass::Gpr64);
    emit_before(
        func,
        pre,
        AArch64Opcode::MovR,
        vec![vreg(ld_addr), vreg(slot_addr)],
    );
    let q_iota = alloc(func, RegClass::Fpr128);
    emit_before(
        func,
        pre,
        AArch64Opcode::NeonLd1Post,
        vec![vreg(q_iota), vreg(ld_addr), imm(ARR_S4)],
    );

    // --- Preheader: w0 = trunc32(iv) + addend; v0 = dup(w0) + iota.
    let tr = alloc(func, RegClass::Gpr32);
    emit_before(func, pre, AArch64Opcode::MovR, vec![vreg(tr), vreg(rec.iv)]);
    let w0 = match rec.addend {
        Addend::None => tr,
        Addend::Invariant(v) => {
            let d = alloc(func, RegClass::Gpr32);
            emit_before(
                func,
                pre,
                AArch64Opcode::AddRR,
                vec![vreg(d), vreg(tr), vreg(v)],
            );
            d
        }
        Addend::Const(k) => {
            let c = alloc(func, RegClass::Gpr32);
            let bits = (k as u64) & 0xFFFF_FFFF;
            emit_before(
                func,
                pre,
                AArch64Opcode::Movz,
                vec![vreg(c), imm((bits & 0xFFFF) as i64)],
            );
            if (bits >> 16) & 0xFFFF != 0 {
                emit_before(
                    func,
                    pre,
                    AArch64Opcode::Movk,
                    vec![vreg(c), imm(((bits >> 16) & 0xFFFF) as i64), imm(16)],
                );
            }
            let d = alloc(func, RegClass::Gpr32);
            emit_before(
                func,
                pre,
                AArch64Opcode::AddRR,
                vec![vreg(d), vreg(tr), vreg(c)],
            );
            d
        }
    };
    let qb = alloc(func, RegClass::Fpr128);
    emit_before(
        func,
        pre,
        AArch64Opcode::NeonDupGen,
        vec![vreg(qb), vreg(w0), imm(ELEM_SIZE)],
    );
    let v0 = alloc(func, RegClass::Fpr128);
    emit_before(
        func,
        pre,
        AArch64Opcode::NeonAddV,
        vec![vreg(v0), vreg(qb), vreg(q_iota), imm(ARR_S4)],
    );

    // --- Preheader: splat step vectors c4/c8/c12/c16.
    let splat = |func: &mut MachFunction, k: i64| -> VReg {
        let g = alloc(func, RegClass::Gpr32);
        emit_before(func, pre, AArch64Opcode::Movz, vec![vreg(g), imm(k)]);
        let q = alloc(func, RegClass::Fpr128);
        emit_before(
            func,
            pre,
            AArch64Opcode::NeonDupGen,
            vec![vreg(q), vreg(g), imm(ELEM_SIZE)],
        );
        q
    };
    let c4 = splat(func, 4);
    let c8 = splat(func, 8);
    let c12 = splat(func, 12);
    let c16 = splat(func, 16);

    // --- Preheader: running store pointer p = base + iv*4.
    let c_es = alloc(func, RegClass::Gpr64);
    emit_before(
        func,
        pre,
        AArch64Opcode::Movz,
        vec![vreg(c_es), imm(ELEM_SIZE)],
    );
    let p = alloc(func, RegClass::Gpr64);
    emit_before(
        func,
        pre,
        AArch64Opcode::Madd,
        vec![vreg(p), vreg(rec.iv), vreg(c_es), vreg(rec.base)],
    );

    // --- main_bound = bound - 15. Runtime bound: computed in the precheck
    // block that skips the vector loop for `n <s 16` (so the wrapped
    // subtraction is dead). Const bound: materialized directly (N >= 16).
    let main_bound = alloc(func, RegClass::Gpr64);
    match rec.bound {
        Bound::Runtime(n) => {
            let pv = pv.expect("runtime bound -> precheck block");
            emit(
                func,
                pv,
                AArch64Opcode::SubRI,
                vec![vreg(main_bound), vreg(n), imm(WIDTH_ELEMS - 1)],
            );
            emit(
                func,
                pv,
                AArch64Opcode::CmpRI,
                vec![vreg(n), imm(WIDTH_ELEMS)],
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
            let mb = materialize_before(func, pre, n - (WIDTH_ELEMS - 1));
            emit_before(
                func,
                pre,
                AArch64Opcode::MovR,
                vec![vreg(main_bound), vreg(mb)],
            );
        }
    }

    // --- Entry guard: `iv <u main_bound` admits only full in-bounds blocks.
    emit(
        func,
        vh,
        AArch64Opcode::CmpRR,
        vec![vreg(rec.iv), vreg(main_bound)],
    );
    emit(func, vh, AArch64Opcode::BCond, vec![imm(CC_LO), block(vb)]);
    emit(func, vh, AArch64Opcode::B, vec![block(rec.header)]);

    // --- Vector body (single-block, bottom-tested): 16 elements / 64 bytes.
    let v1 = alloc(func, RegClass::Fpr128);
    let v2 = alloc(func, RegClass::Fpr128);
    let v3 = alloc(func, RegClass::Fpr128);
    emit(
        func,
        vb,
        AArch64Opcode::NeonAddV,
        vec![vreg(v1), vreg(v0), vreg(c4), imm(ARR_S4)],
    );
    emit(
        func,
        vb,
        AArch64Opcode::NeonAddV,
        vec![vreg(v2), vreg(v0), vreg(c8), imm(ARR_S4)],
    );
    emit(
        func,
        vb,
        AArch64Opcode::NeonAddV,
        vec![vreg(v3), vreg(v0), vreg(c12), imm(ARR_S4)],
    );
    emit(
        func,
        vb,
        AArch64Opcode::NeonStpQPost,
        vec![vreg(v0), vreg(v1), vreg(p), imm(32)],
    );
    emit(
        func,
        vb,
        AArch64Opcode::NeonStpQPost,
        vec![vreg(v2), vreg(v3), vreg(p), imm(32)],
    );
    emit(
        func,
        vb,
        AArch64Opcode::NeonAddV,
        vec![vreg(v0), vreg(v0), vreg(c16), imm(ARR_S4)],
    );
    emit(
        func,
        vb,
        AArch64Opcode::AddRI,
        vec![vreg(rec.iv), vreg(rec.iv), imm(WIDTH_ELEMS)],
    );
    emit(
        func,
        vb,
        AArch64Opcode::CmpRR,
        vec![vreg(rec.iv), vreg(main_bound)],
    );
    emit(func, vb, AArch64Opcode::BCond, vec![imm(CC_LO), block(vb)]);
    emit(func, vb, AArch64Opcode::B, vec![block(rec.header)]);

    // --- COMMIT: splice the fresh blocks in front of the scalar loop. Point
    // of no return; runs only after all emission succeeded.
    let entry = pv.unwrap_or(vh);
    if !rewrite_block_target(func.inst_mut(rec.preheader_term), rec.header, entry) {
        return false;
    }
    remove_cfg_edge(func, rec.preheader, rec.header);
    func.add_edge(rec.preheader, entry);
    true
}

/// Materialize a (non-negative) constant into a fresh `Gpr64` via `Movz` +
/// `Movk` chunks, before `before`. Returns the register.
fn materialize_before(func: &mut MachFunction, before: InstId, value: i64) -> VReg {
    let d = alloc(func, RegClass::Gpr64);
    let bits = value as u64;
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

/// Follow `MovR`/`Copy` chains to the underlying value (canonical name; used
/// only for the loop-bound register, never for iv identity).
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

/// 16-bit `Movz` constant, or a `Movz(lo16)`+`Movk(hi..)` chain, through
/// copies.
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

/// Conservative "operand 0 is a written def" predicate.
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

/// Def map over BLOCK-RESIDENT instructions only (`func.insts` also holds
/// detached ghosts — e.g. a bounds-check-elim'd carrier — that must not
/// shadow live defs).
fn build_def_map(func: &MachFunction) -> HashMap<u32, InstId> {
    let mut map = HashMap::new();
    for &b in &func.block_order {
        for &id in &func.block(b).insts {
            let inst = func.inst(id);
            if let Some(MachOperand::VReg(v)) = inst.operands.first()
                && produces_def(inst.opcode)
            {
                map.insert(v.id, id);
            }
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

#[cfg(test)]
mod tests;
