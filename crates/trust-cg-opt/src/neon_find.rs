// trust-cg-opt - SOUND NEON early-exit linear-search vectorizer (aarch64)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! # NEON early-exit search vectorizer (`neon-find`)
//!
//! Vectorizes the **first-match linear search** (`find` / `memchr`) family:
//!
//! ```text
//! for i in 0..n (signed i < n):  if a[i] == key { return i }
//! return -1
//! ```
//!
//! `a` is a pointer that is **only loaded** in the loop, `key` and `n` are
//! loop-invariant `i32`, and the body's sole memory op is a non-volatile,
//! non-atomic `i32` load `a[i] = *(base + sxtw(i)*4)`. Both clang -O2 and -O3
//! REFUSE this class (the early-exit read set is data-dependent — LLVM's
//! loop-vectorizer bails; issue class open upstream since 2013), yet native
//! measurement shows a large NEON win because the *no-match* and *late-match*
//! executions read the whole array anyway.
//!
//! ## The transform — a BLOCK FILTER, not an index computer
//!
//! The pass is **purely additive**: a vector "block filter" loop is spliced in
//! front of the UNCHANGED scalar loop, and the scalar loop is re-entered for the
//! actual answer. Per 16-element block `[iv, iv+16)` the vector body:
//!
//! * loads the 4 `4 x i32` vectors (`LDP Qt1, Qt2, [p], #32` x 2),
//! * builds 4 all-ones/zero lane masks with `CMEQ.4S` against a `DUP`-splat of
//!   `key` (faithfully proven — `neon_lowering_proofs::proof_neon_cmeqv_lanewise_4s`),
//! * OR-trees the 4 masks into one `.16B` register `o`,
//! * tests **"does any of the 16 lanes match?"** by extracting the two 64-bit
//!   halves of `o` (`UMOV Xd, o.D[0/1]`), OR-ing them in a GPR and comparing to
//!   zero — `o != 0` iff some `a[iv+j] == key`.
//!
//! On a **no-match block** (`o == 0`) the filter skips it (`iv += 16`, next
//! block). On **any-hit** OR when the bounds guard rejects a partial trailing
//! block, control branches to the scalar loop **header with `iv` unchanged**
//! (the block's base for a hit; a multiple of 16 for the tail). The scalar loop
//! then does its own forward scan from `iv` and returns the exact index.
//!
//! ### Why delegating the index is EXACTLY first-match
//!
//! The vector loop NEVER computes a match index and never extracts a "first
//! lane". It only ever **skips blocks it has proven contain no match** and hands
//! control to the scalar loop at a base address `iv0` with the invariant:
//!
//! > every element in `[0, iv0)` has been proven `!= key`.
//!
//! The invariant holds because a block is skipped only when `CMEQ` (a faithful
//! per-lane equality) reports all 16 lanes unequal. The scalar loop, unchanged
//! and correct by construction, computes `min { i in [iv0, n) : a[i] == key }`
//! (or `-1`). Combined with the invariant, that equals `min { i in [0, n) :
//! a[i] == key }` — the exact scalar first-match, INCLUDING same-block and
//! cross-block duplicate keys, WITHOUT any vector lane-ordering argument. The
//! first-match-within-a-block crux is therefore discharged by the scalar loop's
//! own left-to-right scan, not by the vector code.
//!
//! Even a hypothetical bug in the any-hit reduction cannot MISDIRECT the result:
//! a false *positive* re-enters the scalar loop early (it re-scans a truly empty
//! block and continues — slower, still correct); only a false *negative* (a real
//! match whose block is skipped) could miscompile, and that direction is exactly
//! what the faithful `CMEQ` + bitwise-OR + "any bit set" reduction rules out.
//!
//! ## THE SOUNDNESS CRUX — over-read is a SUBSET of the scalar read set
//!
//! The vector body reads all of `a[iv..iv+15]` even when a match sits at
//! `a[iv+2]` and the scalar loop would have exited there. This reads elements
//! the *early-exiting* scalar execution never touches. It is still sound with
//! **no new axiom**:
//!
//! * The bounds guard admits a vector iteration only when
//!   `sxtw(iv) + (WIDTH-1) < sxtw(n)` (`WIDTH = 16`), i.e. the whole block
//!   `[iv, iv+15]` lies within `[0, n)`. So the vector loop's read set is a
//!   subset of `[0, n)`.
//! * `[0, n)` is exactly the read set of the *no-match* scalar execution (which
//!   loads `a[0..n-1]`). Readability of `[0, n)` is therefore already required
//!   by the WORST-CASE scalar execution of the very loop the caller wrote — the
//!   caller must pass an array readable over `[0, n)` or the scalar program
//!   itself faults.
//! * Loads are **side-effect-free** in trust-ir's memory model: the body's only
//!   memory op is a plain `LdrRI` (`READS_MEMORY`, no `HAS_SIDE_EFFECTS`).
//!   Volatile loads use distinct `VolatileLdr*` opcodes with
//!   `HAS_SIDE_EFFECTS`, and atomic loads use distinct `Ldar*` opcodes; both
//!   families are rejected by the loop-body whitelist. The pass double-checks
//!   no body instruction carries `HAS_SIDE_EFFECTS`.
//!
//! Hence reordering / widening the pure reads within `[0, n)` cannot change any
//! observable behavior, and the early-exit answer is reproduced exactly by the
//! delegated scalar scan. This is the BOUNDED-ONLY version; the page-alignment
//! speculative tail (reading past `n` within a page) is deliberately NOT
//! implemented — it would need the trusted OS page axiom.
//!
//! The trailing `< 16` elements are scanned by the untouched scalar loop, which
//! is re-entered with `iv` restored to the first unprocessed index.
//!
//! ## No horizontal-reduce op
//!
//! The any-hit test uses `UMOV Xd, o.D[lane]` + scalar `ORR`/`CMP` and NOT
//! `UMAXV`/`UMAXP`. `NeonUmaxv` is fail-closed *allowlisted* (a genuine
//! cross-lane reduce still lacking a faithful obligation); `NeonUmovGen` is on
//! the SAME allowlist and is what the shipping argmin path already uses, so this
//! introduces NO new opcode and no new proof debt. `CMEQ.4S` and the whole-
//! register `ORR.16B` are faithfully proven (`EmittableNeedsProof`).
//!
//! ## The byte (`memchr`, `.16B`) width
//!
//! The SAME block-filter design also fires on the byte search
//! `for i in 0..n: if a_u8[i] == key { return i }` whose loaded term is the
//! widening narrow load `Uxtb(LdrbRI(base + sxtw(iv)))` (or the `Sxtb` sibling)
//! — the exact leaf shape [`crate::neon_array`]'s widening machinery recognizes.
//! Per 64-byte block the vector body is the same 4 x `LDP Qt1, Qt2, [p], #32`
//! walk with `CMEQ.16B` masks against a `DUP Vd.16B, Wkey` splat (the credited
//! arrangement-parametric CMEQ obligation family; DUP/UMOV are the same
//! allowlisted opcodes at a different element code). The delegated-scalar
//! first-match argument carries over VERBATIM: the vector loop still only skips
//! blocks proven empty and re-enters the untouched scalar loop, and the bounds
//! guard still admits only whole blocks inside `[0, n)` (the worst-case scalar
//! read set).
//!
//! One byte-width subtlety: the scalar compares the EXTENDED 32-bit value
//! (`ext(a[i]) == key`) while `CMEQ.16B` compares raw bytes against
//! `trunc8(key)` (`DUP .16B` broadcasts the low 8 bits of `Wkey`). The byte
//! filter is a SUPERSET filter in exactly the safe direction:
//! * scalar match ⇒ `ext(a[i]) == key` ⇒ `trunc8(key) == a[i]` ⇒ the lane is
//!   all-ones ⇒ the block is NOT skipped — a false NEGATIVE (the only
//!   miscompiling direction) is impossible, for `Uxtb` and `Sxtb` alike;
//! * when `key` is outside the extension's byte range (e.g. `key > 255` under
//!   `Uxtb`), a lane may match `trunc8(key)` without any scalar match — a false
//!   POSITIVE, which merely re-enters the always-correct scalar loop (slower,
//!   never wrong; same argument as the any-hit reduction above).
//!
//! Disable with `TRUST_CG_DISABLE_PASSES=neon_find`. Widths: i32 (`.4S`,
//! 16-element blocks) and i8/u8 (`.16B`, 64-byte blocks).

use std::collections::{HashMap, HashSet};

use trust_cg_ir::{
    AArch64Opcode, BlockId, InstFlags, InstId, MachFunction, MachInst, MachOperand, RegClass, VReg,
};

use crate::dom::DomTree;
use crate::loops::LoopAnalysis;
use crate::pass_manager::{AnalysisCache, MachinePass};

/// Lanes per `4 x i32` NEON register.
const VF: i64 = 4;
/// NEON element-size operand code for `S` (32-bit) lanes.
const ELEM_S: i64 = 4;
/// NEON element-size operand code for `D` (64-bit) lanes.
const ELEM_D: i64 = 8;
/// NEON element-size operand code for `B` (8-bit) lanes.
const ELEM_B: i64 = 1;
/// NEON arrangement operand code for `.4S`.
const ARR_S4: i64 = 5;
/// NEON arrangement operand code for `.16B`.
const ARR_B16: i64 = 1;
/// Byte size of an `i32` array element.
const ELEM_BYTES: i64 = 4;
/// Byte size of an `i8`/`u8` array element (the `.16B` `memchr` path).
const ELEM_BYTES_B: i64 = 1;
/// Lanes per `16 x i8` NEON register.
const VF_B: i64 = 16;
/// Independent NEON vectors per block (`UNROLL` = 64 bytes / 16-byte Q register).
const UNROLL: usize = 4;
/// Elements processed per vector iteration on the i32 (`.4S`) path.
const WIDTH: i64 = UNROLL as i64 * VF;

// AArch64 condition codes (imm operands of BCond).
const CC_EQ: i64 = 0;
const CC_NE: i64 = 1;
/// Unsigned `LO` (`C == 0`): the `iv <u N` loop-continue of the forward chain.
const CC_LO: i64 = 3;
const CC_LT: i64 = 11;

// ---------------------------------------------------------------------------
// Pass
// ---------------------------------------------------------------------------

/// The `neon-find` machine pass.
#[derive(Default)]
pub struct NeonFindPass {
    fired: usize,
}

impl NeonFindPass {
    pub fn new() -> Self {
        Self { fired: 0 }
    }

    /// Loops vectorized in the last `run`.
    pub fn fired(&self) -> usize {
        self.fired
    }
}

impl MachinePass for NeonFindPass {
    fn name(&self) -> &str {
        "neon-find"
    }

    fn run(&mut self, func: &mut MachFunction) -> bool {
        let dom = DomTree::compute(func);
        let loops = LoopAnalysis::compute(func, &dom);
        self.run_core(func, &dom, &loops)
    }

    // Share the AnalysisCache's CFG-derived DomTree + LoopAnalysis instead of
    // recomputing per pass (see NeonArrayPass). Sound + byte-identical: both
    // analyses depend only on the CFG, which the cache invalidates on any CFG
    // change, so a shared instance equals a fresh recompute here.
    fn run_with_analyses(&mut self, func: &mut MachFunction, analyses: &mut AnalysisCache) -> bool {
        let loops = analyses.loop_analysis(func).clone();
        let changed = {
            let dom = analyses.domtree(func);
            self.run_core(func, dom, &loops)
        };
        // Invalidate the shared analyses on a FIRE (CFG mutated) so no downstream
        // pass reads a stale loop tree; zero cost in the no-fire hot path. See
        // NeonArrayPass::run_with_analyses.
        if changed {
            analyses.invalidate();
        }
        changed
    }
}

impl NeonFindPass {
    fn run_core(&mut self, func: &mut MachFunction, dom: &DomTree, loops: &LoopAnalysis) -> bool {
        self.fired = 0;

        // Recognize read-only first (applying only ADDS blocks and rewires the
        // preheader terminator; it never renumbers or edits the scalar loop), so
        // recognized data for other loops stays valid.
        //
        // Escape hatch (differential testing): disable ONLY the forward-chain
        // recognizer, leaving the proven strict 3-block path intact, so the
        // scalar output can be compared against the vectorized one.
        let allow_chain = std::env::var_os("TCG_NO_CHAIN_FIND").is_none();
        let mut plans = Vec::new();
        for lp in loops.all_loops() {
            if let Some(rec) =
                FindRecognized::recognize(func, dom, lp.header, lp.latch, &lp.body, allow_chain)
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
        if changed && std::env::var("TRUST_CG_DUMP_NEONFIND").is_ok() {
            eprintln!("[neon-find] fn={} vectorized={}", func.name, self.fired);
        }
        changed
    }
}

// ---------------------------------------------------------------------------
// Recognition
// ---------------------------------------------------------------------------

/// A validated first-match search loop ready to be filtered by a NEON block
/// scan. All fields refer to the UNCHANGED scalar loop; the transform only
/// splices a vector loop in front and re-enters `header`.
struct FindRecognized {
    /// Scalar loop header (`if iv < bound goto body else goto no-match exit`).
    /// This is also the re-entry target for both vector exits.
    header: BlockId,
    /// Block whose terminator branches to `header` (the loop preheader).
    preheader: BlockId,
    /// The preheader's branch instruction into `header`.
    preheader_term: InstId,
    /// Induction variable (`iv += 1` in the latch). `Gpr32` on the strict path,
    /// `Gpr64` (`usize` counter used directly for addressing) on the
    /// forward-chain path (`iv_is_i64`).
    iv: VReg,
    /// Loop trip bound `n` (loop-invariant register). `Some` on the strict path;
    /// `None` on the forward-chain path (a compile-time constant — `bound_const`).
    bound: Option<VReg>,
    /// Compile-time constant trip bound `N` of a forward `while iv <u N` chain
    /// (the folded immediate the bridge emits over a fixed-size local array).
    /// `Some` on the forward-chain path; `None` on the strict register-bound path.
    bound_const: Option<i64>,
    /// The search key (`Gpr32`, loop-invariant).
    key: VReg,
    /// The array base pointer (loop-invariant).
    base: VReg,
    /// True on the byte (`memchr`, `.16B`) width: the loaded term is
    /// `Uxtb/Sxtb(LdrbRI(base + sxtw(iv)))` and blocks are 64 bytes.
    is_byte: bool,
    /// True when `iv` is a `Gpr64` `usize` used directly in the address (the
    /// forward-chain shape). The guard/pointer then skip the `Sxtw` the `Gpr32`
    /// strict path performs and the loop-continue is UNSIGNED (`LO`).
    iv_is_i64: bool,
}

/// Opcodes permitted anywhere in the search loop body. Anything else — in
/// particular any store, call, volatile (`VolatileLdr*`/`VolatileStr*`),
/// atomic (`Ldar*`/`Ld*` LSE), or NEON op — BAILS, which fails closed on
/// side effects and on volatile/atomic memory.
/// `LdrbRI`/`Uxtb`/`Sxtb` are the byte (`memchr`) width's widening narrow load.
fn allowed_loop_op(op: AArch64Opcode) -> bool {
    use AArch64Opcode::*;
    matches!(
        op,
        AddRR
            | AddRI
            | SubRI
            | MovR
            | Copy
            | Movz
            | Movn
            | Sxtw
            | Madd
            | LdrRI
            | LdrbRI
            | Uxtb
            | Sxtb
            | CmpRR
            | CmpRI
            | BCond
            | B
    )
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

/// `(dst, src)` if `inst` is a register copy (`MovR`/`Copy`, or `AddRI +0`).
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

/// Constant value of a `Movz #imm` def (16-bit immediate).
fn const_value(func: &MachFunction, def: &HashMap<u32, InstId>, val: VReg) -> Option<i64> {
    let inst = func.inst(*def.get(&val.id)?);
    if inst.opcode == AArch64Opcode::Movz
        && inst.operands.len() == 2
        && let Some(v) = imm_of(&inst.operands[1])
        && (0..=0xFFFF).contains(&v)
    {
        return Some(v);
    }
    None
}

/// Whether `val` is `iv` or a chain of register copies rooted at `iv`.
fn resolves_to_iv(func: &MachFunction, def: &HashMap<u32, InstId>, val: VReg, iv: VReg) -> bool {
    let mut cur = val;
    for _ in 0..8 {
        if cur == iv {
            return true;
        }
        let Some(&id) = def.get(&cur.id) else {
            return false;
        };
        match copy_like(func.inst(id)) {
            Some((d, s)) if d == cur => cur = s,
            _ => return false,
        }
    }
    false
}

/// The nearest flag-setting `CmpRR`/`CmpRI` preceding `target` in program order.
fn nearest_cmp_before(
    func: &MachFunction,
    block_insts: &[InstId],
    target: InstId,
) -> Option<InstId> {
    let pos = block_insts.iter().position(|&id| id == target)?;
    for &id in block_insts[..pos].iter().rev() {
        if matches!(
            func.inst(id).opcode,
            AArch64Opcode::CmpRR | AArch64Opcode::CmpRI
        ) {
            return Some(id);
        }
    }
    None
}

/// Recognize the load `dst = *(base + sxtw(iv)*4)` at offset 0 and return its
/// loop-invariant `base`. `dst` must be `Gpr32`, the index a `Sxtw` of `iv`
/// (through copies), and the element factor `4`.
fn load_base(
    func: &MachFunction,
    dom: &DomTree,
    def: &HashMap<u32, InstId>,
    loop_insts: &HashSet<InstId>,
    iv: VReg,
    preheader: BlockId,
    dst: VReg,
) -> Option<VReg> {
    if dst.class != RegClass::Gpr32 {
        return None;
    }
    let load_id = *def.get(&dst.id)?;
    let load = func.inst(load_id);
    if load.opcode != AArch64Opcode::LdrRI
        || load.operands.len() != 3
        || imm_of(&load.operands[2]) != Some(0)
    {
        return None;
    }
    let addr = vreg_of(&load.operands[1])?;
    let madd = func.inst(*def.get(&addr.id)?);
    if madd.opcode != AArch64Opcode::Madd || madd.operands.len() != 4 {
        return None;
    }
    let f1 = vreg_of(&madd.operands[1])?;
    let f2 = vreg_of(&madd.operands[2])?;
    let base = vreg_of(&madd.operands[3])?;
    // One factor is `Sxtw(iv-through-copies)`, the other is the element size 4.
    let is_sext_iv = |factor: VReg| -> bool {
        let Some(&id) = def.get(&factor.id) else {
            return false;
        };
        if !loop_insts.contains(&id) {
            return false;
        }
        let inst = func.inst(id);
        inst.opcode == AArch64Opcode::Sxtw
            && inst.operands.len() == 2
            && vreg_of(&inst.operands[1]).is_some_and(|s| resolves_to_iv(func, def, s, iv))
    };
    let es_ok = |factor: VReg| const_value(func, def, factor) == Some(ELEM_BYTES);
    if !((is_sext_iv(f1) && es_ok(f2)) || (is_sext_iv(f2) && es_ok(f1))) {
        return None;
    }
    // `base` must be available in (dominate) the preheader.
    let base_def = *def.get(&base.id)?;
    let base_block = block_of_inst(func, base_def)?;
    if !dom.dominates(base_block, preheader) {
        return None;
    }
    Some(base)
}

/// Recognize the widening BYTE load `dst = Uxtb/Sxtb(LdrbRI(base + sxtw(iv), 0))`
/// and return its loop-invariant `base` — the byte (`memchr`) term shape,
/// mirroring [`crate::neon_array`]'s widening-leaf recognition. The address is
/// the unit-stride `a[i]`: either the folded `AddRR(base, sxtw(iv))` (the `*1`
/// gep collapses to a plain add, either operand order) or the equivalent
/// `Madd(sxtw(iv), 1, base)` (factor order free). Both the extend and the load
/// must be in-loop `Gpr32` defs at offset 0.
fn byte_load_base(
    func: &MachFunction,
    dom: &DomTree,
    def: &HashMap<u32, InstId>,
    loop_insts: &HashSet<InstId>,
    iv: VReg,
    preheader: BlockId,
    dst: VReg,
) -> Option<VReg> {
    if dst.class != RegClass::Gpr32 {
        return None;
    }
    let ext_id = *def.get(&dst.id)?;
    if !loop_insts.contains(&ext_id) {
        return None;
    }
    let ext = func.inst(ext_id);
    // Both extensions are safe: the CMEQ.16B filter is a superset filter under
    // either (see the module docs' byte-width section).
    if !matches!(ext.opcode, AArch64Opcode::Uxtb | AArch64Opcode::Sxtb) || ext.operands.len() != 2 {
        return None;
    }
    let loaded = vreg_of(&ext.operands[1])?;
    if loaded.class != RegClass::Gpr32 {
        return None;
    }
    let load_id = *def.get(&loaded.id)?;
    if !loop_insts.contains(&load_id) {
        return None;
    }
    let load = func.inst(load_id);
    if load.opcode != AArch64Opcode::LdrbRI
        || load.operands.len() != 3
        || imm_of(&load.operands[2]) != Some(0)
    {
        return None;
    }
    let addr = vreg_of(&load.operands[1])?;
    let addr_id = *def.get(&addr.id)?;
    if !loop_insts.contains(&addr_id) {
        return None;
    }
    let addr_inst = func.inst(addr_id);
    let is_sext_iv = |factor: VReg| -> bool {
        let Some(&id) = def.get(&factor.id) else {
            return false;
        };
        if !loop_insts.contains(&id) {
            return false;
        }
        let inst = func.inst(id);
        inst.opcode == AArch64Opcode::Sxtw
            && inst.operands.len() == 2
            && vreg_of(&inst.operands[1]).is_some_and(|s| resolves_to_iv(func, def, s, iv))
    };
    let base = match addr_inst.opcode {
        // The `*1` gep folds to a plain add: `AddRR(base, sxtw(iv))`.
        AArch64Opcode::AddRR if addr_inst.operands.len() == 3 => {
            let a = vreg_of(&addr_inst.operands[1])?;
            let b = vreg_of(&addr_inst.operands[2])?;
            if is_sext_iv(a) {
                b
            } else if is_sext_iv(b) {
                a
            } else {
                return None;
            }
        }
        // `Madd(idx, 1, base)` (factor order free).
        AArch64Opcode::Madd if addr_inst.operands.len() == 4 => {
            let f1 = vreg_of(&addr_inst.operands[1])?;
            let f2 = vreg_of(&addr_inst.operands[2])?;
            let base = vreg_of(&addr_inst.operands[3])?;
            let es_ok = |f: VReg| const_value(func, def, f) == Some(ELEM_BYTES_B);
            if (is_sext_iv(f1) && es_ok(f2)) || (is_sext_iv(f2) && es_ok(f1)) {
                base
            } else {
                return None;
            }
        }
        _ => return None,
    };
    // `base` must be available in (dominate) the preheader.
    let base_def = *def.get(&base.id)?;
    let base_block = block_of_inst(func, base_def)?;
    if !dom.dominates(base_block, preheader) {
        return None;
    }
    Some(base)
}

impl FindRecognized {
    /// Try the proven strict 3-block recognizer FIRST (byte-identical output); if
    /// it bails, and the forward chain is enabled, try the multi-block
    /// forward-chain recognizer. The two shapes are disjoint (strict =
    /// `Gpr32`/`CmpRR`-reg/`CC_LT`; chain = `Gpr64`/const-or-reg/`CC_LO`) and
    /// apply only ADDS blocks, so trying both is safe and never double-fires.
    fn recognize(
        func: &MachFunction,
        dom: &DomTree,
        header: BlockId,
        latch: BlockId,
        body: &HashSet<BlockId>,
        allow_chain: bool,
    ) -> Option<Self> {
        if let Some(rec) = Self::recognize_strict(func, dom, header, latch, body) {
            return Some(rec);
        }
        if !allow_chain {
            return None;
        }
        Self::recognize_forward_chain(func, dom, header, latch, body)
    }

    fn recognize_strict(
        func: &MachFunction,
        dom: &DomTree,
        header: BlockId,
        latch: BlockId,
        body: &HashSet<BlockId>,
    ) -> Option<Self> {
        // (R1) exactly a 3-block loop {header, body, latch}: `header` tests
        // `iv < n`, `body` loads + tests `a[iv] == key` (early exit), `latch`
        // increments `iv`.
        if header == latch || body.len() != 3 || !body.contains(&header) || !body.contains(&latch) {
            return None;
        }
        let body_blk = *body.iter().find(|&&b| b != header && b != latch)?;

        // (R2) Whitelist every opcode in the loop, and additionally reject any
        // memory WRITE or CALL flag (defense-in-depth over the whitelist —
        // `HAS_SIDE_EFFECTS` is NOT used because it also tags flag-setters like
        // `CmpRR`). Stores, atomics (`Ldar*`/LSE), and calls are all outside the
        // whitelist AND carry `WRITES_MEMORY`/`IS_CALL`; volatile loads use
        // distinct `VolatileLdr*` opcodes outside the whitelist.
        let mut loop_insts = HashSet::new();
        for &b in &[header, body_blk, latch] {
            for &id in &func.block(b).insts {
                let inst = func.inst(id);
                if !allowed_loop_op(inst.opcode)
                    || inst.flags.contains(InstFlags::WRITES_MEMORY)
                    || inst.flags.contains(InstFlags::IS_CALL)
                {
                    return None;
                }
                loop_insts.insert(id);
            }
        }
        let def = build_def_map(func);

        // (R3) header: `CmpRR(iv, bound); BCond LT -> body_blk; B -> no-match`.
        // The LT-true edge stays in the loop; the fall-through leaves it.
        let h_insts = func.block(header).insts.clone();
        let h_bcond_id = *h_insts
            .iter()
            .find(|&&id| func.inst(id).opcode == AArch64Opcode::BCond)?;
        let h_bcond = func.inst(h_bcond_id);
        if imm_of(&h_bcond.operands[0]) != Some(CC_LT) {
            return None;
        }
        if *branch_targets(h_bcond).first()? != body_blk {
            return None;
        }
        let h_cmp_id = nearest_cmp_before(func, &h_insts, h_bcond_id)?;
        let h_cmp = func.inst(h_cmp_id);
        if h_cmp.opcode != AArch64Opcode::CmpRR {
            return None;
        }
        let iv = vreg_of(&h_cmp.operands[0])?;
        let bound = vreg_of(&h_cmp.operands[1])?;
        if iv.class != RegClass::Gpr32 || bound.class != RegClass::Gpr32 {
            return None;
        }

        // (R4) latch: `iv <- iv + 1` writeback and `B -> header`.
        let l_insts = func.block(latch).insts.clone();
        let l_b = l_insts
            .iter()
            .map(|&id| func.inst(id))
            .find(|i| i.opcode == AArch64Opcode::B)?;
        if *branch_targets(l_b).first()? != header {
            return None;
        }
        let mut iv_src = None;
        for &id in &l_insts {
            if let Some((d, s)) = copy_like(func.inst(id))
                && d == iv
            {
                iv_src = Some(s);
            }
        }
        if !is_increment_by_one(func, &def, iv_src?, iv) {
            return None;
        }
        // (R4b) SOUNDNESS: `iv` must be the ONLY loop-carried value. This path
        // vectorizes into a block-SKIPPING filter whose latch advances ONLY
        // `iv` (see the apply); it maintains no other running state. So a loop
        // that also carries a reduction/accumulator (e.g. `sum += a[iv]`, whose
        // result is live-out) would be miscompiled — the vector filter skips
        // whole blocks without updating the accumulator, then the scalar loop
        // resumes with every skipped element missing. In this un-coalesced
        // conventional-SSA form (which R4 already requires, via the
        // `iv = MovR(iv+1)` latch copy), every loop-carried value's back-edge
        // copy lands in the latch as a `copy_like` writeback. Reject any latch
        // writeback to a register other than `iv` — mirrors the chain path's
        // identical guard ("no reduction accumulator in a pure first-match
        // scan"). Address arithmetic is recomputed per iteration (dead at
        // iteration end, no latch copy) and is correctly unaffected.
        for &id in &l_insts {
            if let Some((d, _)) = copy_like(func.inst(id))
                && d != iv
            {
                return None;
            }
        }

        // (R5) body: `CmpRR(a[iv], key); BCond EQ -> match exit (LEAVES loop);
        // B -> latch`. The load and key operands may appear in either order.
        let b_insts = func.block(body_blk).insts.clone();
        let b_bcond_id = *b_insts
            .iter()
            .find(|&&id| func.inst(id).opcode == AArch64Opcode::BCond)?;
        let b_bcond = func.inst(b_bcond_id);
        if imm_of(&b_bcond.operands[0]) != Some(CC_EQ) {
            return None;
        }
        let eq_target = *branch_targets(b_bcond).first()?;
        if body.contains(&eq_target) {
            return None; // the match exit must leave the loop
        }
        let b_b = b_insts
            .iter()
            .rev()
            .map(|&id| func.inst(id))
            .find(|i| i.opcode == AArch64Opcode::B)?;
        if *branch_targets(b_b).first()? != latch {
            return None;
        }
        let b_cmp_id = nearest_cmp_before(func, &b_insts, b_bcond_id)?;
        let b_cmp = func.inst(b_cmp_id);
        if b_cmp.opcode != AArch64Opcode::CmpRR {
            return None;
        }
        let c0 = vreg_of(&b_cmp.operands[0])?;
        let c1 = vreg_of(&b_cmp.operands[1])?;

        // preheader = header's non-latch predecessor (single-pred through the
        // guard chain); its terminator branches to `header`.
        let hpreds = &func.block(header).preds;
        if hpreds.len() != 2 || !hpreds.contains(&latch) {
            return None;
        }
        let preheader = *hpreds.iter().find(|&&b| b != latch)?;
        let preheader_term = *func
            .block(preheader)
            .insts
            .iter()
            .rev()
            .find(|&&id| branch_targets(func.inst(id)).contains(&header))?;

        // One compare operand is the load `a[iv]` (i32 direct load, or the byte
        // width's `Uxtb/Sxtb(LdrbRI)` widening load); the other is the invariant
        // key. Try both assignments and both widths (i32 first — the shapes are
        // mutually exclusive on the load opcode, so order is cosmetic).
        for &(load_res, key) in &[(c0, c1), (c1, c0)] {
            let (base, is_byte) = if let Some(base) =
                load_base(func, dom, &def, &loop_insts, iv, preheader, load_res)
            {
                (base, false)
            } else if let Some(base) =
                byte_load_base(func, dom, &def, &loop_insts, iv, preheader, load_res)
            {
                (base, true)
            } else {
                continue;
            };
            // `key` and `bound` must be loop-invariant (dominate the preheader).
            if !invariant(func, dom, &def, key, preheader)
                || !invariant(func, dom, &def, bound, preheader)
            {
                continue;
            }
            // The key must not be the induction variable.
            if resolves_to_iv(func, &def, key, iv) {
                continue;
            }
            return Some(FindRecognized {
                header,
                preheader,
                preheader_term,
                iv,
                bound: Some(bound),
                bound_const: None,
                key,
                base,
                is_byte,
                iv_is_i64: false,
            });
        }
        None
    }

    /// Recognize a forward bounds-guarded `while iv <u N` first-match SEARCH
    /// chain over a fixed-size local array — the shape the bridge emits when the
    /// per-iteration bounds checks are elided to pass-throughs and the equality
    /// test is an early-exit branch. Mirrors [`crate::neon_minmax`]'s
    /// `ChainRecognized`, specialized to a search (no reduction: the exact index
    /// is delegated to the untouched scalar loop). Fail-closed on any deviation.
    fn recognize_forward_chain(
        func: &MachFunction,
        dom: &DomTree,
        header: BlockId,
        latch: BlockId,
        body: &HashSet<BlockId>,
    ) -> Option<Self> {
        // A strict 2/3-block loop is handled by `recognize_strict`; the chain has
        // header + latch + at least one middle (pass-through / match) block.
        if header == latch || body.len() < 3 || !body.contains(&header) || !body.contains(&latch) {
            return None;
        }

        // Whitelist every opcode across EVERY body block, and reject any memory
        // WRITE / CALL flag (same defense-in-depth as `recognize_strict`). Stores,
        // atomics, calls, and distinct `VolatileLdr*` loads are outside the
        // whitelist; stores/calls are additionally flag-tagged here.
        let mut loop_insts = HashSet::new();
        for &b in body {
            for &id in &func.block(b).insts {
                let inst = func.inst(id);
                if !allowed_loop_op(inst.opcode)
                    || inst.flags.contains(InstFlags::WRITES_MEMORY)
                    || inst.flags.contains(InstFlags::IS_CALL)
                {
                    return None;
                }
                loop_insts.insert(id);
            }
        }

        // REQUIRED: the block_order-restricted def map. The flat `build_def_map`
        // still sees the bounds-check-elim-detached `TrapBoundsCheckExact` carrier
        // left in `func.insts` (its operand0 is a READ of the iv-copy), which would
        // shadow the real in-block def and break `resolves_to_iv` / the address
        // walks. See [`build_live_def_map`].
        let def = build_live_def_map(func);

        // preheader = header's non-latch predecessor; its terminator enters header.
        let hpreds = &func.block(header).preds;
        if hpreds.len() != 2 || !hpreds.contains(&latch) {
            return None;
        }
        let preheader = *hpreds.iter().find(|&&b| b != latch)?;
        let preheader_term = *func
            .block(preheader)
            .insts
            .iter()
            .rev()
            .find(|&&id| branch_targets(func.inst(id)).contains(&header))?;

        // The latch's ONLY successor is the header, ending in that back-edge `B`
        // (test-first `while` — the exit test lives in the header guard). Its sole
        // loop-carried writeback is the `iv = iv + 1` induction; a search loop
        // carries NO reduction accumulator (the index is delegated to the scalar
        // loop), so any extra carried var BAILS.
        let lsuccs = &func.block(latch).succs;
        if lsuccs.len() != 1 || lsuccs[0] != header {
            return None;
        }
        let latch_term = *func.block(latch).insts.last()?;
        if func.inst(latch_term).opcode != AArch64Opcode::B
            || !branch_targets(func.inst(latch_term)).contains(&header)
        {
            return None;
        }
        let mut writebacks: Vec<(VReg, VReg)> = Vec::new();
        for &id in &func.block(latch).insts {
            if let Some((d, s)) = copy_like(func.inst(id)) {
                writebacks.push((d, s));
            }
        }
        let iv = writebacks
            .iter()
            .find(|(d, s)| is_increment_by_one(func, &def, *s, *d))
            .map(|(d, _)| *d)?;
        if writebacks.iter().filter(|(d, _)| *d == iv).count() != 1 {
            return None;
        }
        // The induction is the `Gpr64` `usize` counter of a `for i in 0..N` loop
        // (the mixed i64-index / i32-element shape the bridge emits); a `Gpr32`
        // induction is the strict path's domain (fail-closed here).
        if iv.class != RegClass::Gpr64 {
            return None;
        }
        if writebacks.iter().any(|(d, _)| *d != iv) {
            return None; // no reduction accumulator in a pure first-match scan
        }

        // Walk header -> ... -> latch, classifying each block as the loop-continue
        // / bounds guard, the (single) equality match block, or a pass-through,
        // proving SINGLE-N agreement, full coverage, and EXACTLY ONE match block.
        let (bound, mtch) = walk_find_chain(
            func,
            dom,
            &def,
            &loop_insts,
            body,
            header,
            latch,
            iv,
            preheader,
        )?;
        // The trip bound arrives EITHER as a compile-time immediate (`CmpRI`, the
        // `ChainBound::Const` shape) OR as a register the bridge CSE-materialized
        // the fixed array length into and guards with `CmpRR(iv, r)` — the shape
        // real lowering emits for `while i<N` over a fixed-size local array (`Movz
        // r,#N` in the entry block, reused by the loop guard AND the per-access
        // bounds checks; e06_find). Recover the constant in the register case
        // under a THREE-way fail-closed discipline that makes the runtime value
        // of `r` at the guard provably equal `n` (machine IR is NOT SSA, so a
        // bare def-map lookup is not enough):
        //   1. `r` is defined by a single-instruction `Movz #n` (`const_value`;
        //      a `Movz+Movk` pair leaves the def map pointing at the `Movk` and
        //      correctly fails this),
        //   2. that def DOMINATES the preheader (`invariant` — executed before
        //      every loop entry),
        //   3. it is the ONLY live def of `r.id` in the whole function
        //      (`unique_live_def_count == 1`), so no other def can be the one
        //      reaching the guard.
        // Then the vector guard `iv <u n-(W-1)` is bit-for-bit implied by the
        // scalar guard `iv <u r`, and single-N agreement (checked in
        // `walk_find_chain`) still ties `n` to every bounds-check limit == the
        // array length == the no-match scalar read set. A runtime-dynamic bound
        // (no `const_value`, or any second def) stays fail-closed.
        let n = match bound {
            ChainBound::Const(n) => n,
            ChainBound::Reg(r) => match const_value(func, &def, r) {
                Some(n)
                    if invariant(func, dom, &def, r, preheader)
                        && unique_live_def_count(func, r) == 1 =>
                {
                    n
                }
                _ => return None,
            },
        };
        if !(1..=i32::MAX as i64).contains(&n) {
            return None;
        }
        let (base, key, is_byte) = mtch;

        Some(FindRecognized {
            header,
            preheader,
            preheader_term,
            iv,
            bound: None,
            bound_const: Some(n),
            key,
            base,
            is_byte,
            iv_is_i64: true,
        })
    }
}

/// The loop-continue / bounds-guard limit of a forward `while iv <u N` chain:
/// a constant `CmpRI(iv, Imm(N))` (the folded form the bridge emits over a
/// fixed-size local array) or a register `CmpRR(iv, N_reg)`.
#[derive(Clone, Copy, PartialEq, Eq)]
enum ChainBound {
    Const(i64),
    Reg(VReg),
}

/// Follow value-preserving copy chains to the underlying value (bounded). Used
/// only on single-def bound registers, never on the multi-def induction.
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

/// Recognize the terminating guard diamond `cmp x, N; b.lo t_lo; b t_b` (last
/// three instructions) with the unsigned-`LO` taken edge `t_lo` IN the loop and
/// the fall-through `t_b` OUT of it. `N` is a constant immediate (`CmpRI`) or a
/// register (`CmpRR`). Mirrors [`crate::neon_minmax`]'s `recognize_chain_guard`.
/// Fail-closed on any other shape.
fn recognize_chain_guard(
    func: &MachFunction,
    blk: BlockId,
    body: &HashSet<BlockId>,
) -> Option<(VReg, ChainBound, BlockId)> {
    let insts = &func.block(blk).insts;
    let n = insts.len();
    if n < 3 {
        return None;
    }
    let cmp = func.inst(insts[n - 3]);
    let bcond = func.inst(insts[n - 2]);
    let br = func.inst(insts[n - 1]);
    if bcond.opcode != AArch64Opcode::BCond
        || br.opcode != AArch64Opcode::B
        || imm_of(&bcond.operands[0])? != CC_LO
    {
        return None;
    }
    let (x, bound) = match cmp.opcode {
        AArch64Opcode::CmpRR => (
            vreg_of(&cmp.operands[0])?,
            ChainBound::Reg(vreg_of(&cmp.operands[1])?),
        ),
        AArch64Opcode::CmpRI => (
            vreg_of(&cmp.operands[0])?,
            ChainBound::Const(imm_of(&cmp.operands[1])?),
        ),
        _ => return None,
    };
    let t_lo = *branch_targets(bcond).first()?;
    let t_b = *branch_targets(br).first()?;
    if !body.contains(&t_lo) || body.contains(&t_b) {
        return None;
    }
    Some((x, bound, t_lo))
}

/// Two chain bounds agree iff same constant / same register (after copy strip) /
/// register-resolves-to-the-constant.
fn chain_bound_agrees(
    func: &MachFunction,
    def: &HashMap<u32, InstId>,
    a: ChainBound,
    b: ChainBound,
) -> bool {
    match (a, b) {
        (ChainBound::Const(x), ChainBound::Const(y)) => x == y,
        (ChainBound::Reg(x), ChainBound::Reg(y)) => {
            strip_copies(func, def, x) == strip_copies(func, def, y)
                || matches!(
                    (const_value(func, def, x), const_value(func, def, y)),
                    (Some(p), Some(q)) if p == q
                )
        }
        (ChainBound::Const(x), ChainBound::Reg(r)) | (ChainBound::Reg(r), ChainBound::Const(x)) => {
            const_value(func, def, r) == Some(x)
        }
    }
}

/// Chain variant of [`load_base`]: recognize `dst = *(base + idx*4)` (i32 `.4S`,
/// offset 0) where `idx` is a copy of `iv` used DIRECTLY (the `Gpr64` induction —
/// the bridge's mixed i64-index shape) OR `Sxtw(iv)`. Returns the loop-invariant
/// `base`. Fail-closed otherwise.
fn chain_load_base(
    func: &MachFunction,
    dom: &DomTree,
    def: &HashMap<u32, InstId>,
    loop_insts: &HashSet<InstId>,
    iv: VReg,
    preheader: BlockId,
    dst: VReg,
) -> Option<VReg> {
    if dst.class != RegClass::Gpr32 {
        return None;
    }
    let load_id = *def.get(&dst.id)?;
    if !loop_insts.contains(&load_id) {
        return None;
    }
    let load = func.inst(load_id);
    if load.opcode != AArch64Opcode::LdrRI
        || load.operands.len() != 3
        || imm_of(&load.operands[2]) != Some(0)
    {
        return None;
    }
    let addr = vreg_of(&load.operands[1])?;
    let madd_id = *def.get(&addr.id)?;
    if !loop_insts.contains(&madd_id) {
        return None;
    }
    let madd = func.inst(madd_id);
    if madd.opcode != AArch64Opcode::Madd || madd.operands.len() != 4 {
        return None;
    }
    let f1 = vreg_of(&madd.operands[1])?;
    let f2 = vreg_of(&madd.operands[2])?;
    let base = vreg_of(&madd.operands[3])?;
    let is_sext_iv = |factor: VReg| chain_is_sext_iv(func, def, loop_insts, factor, iv);
    let idx_ok = |factor: VReg| resolves_to_iv(func, def, factor, iv) || is_sext_iv(factor);
    let es_ok = |factor: VReg| const_value(func, def, factor) == Some(ELEM_BYTES);
    if !((idx_ok(f1) && es_ok(f2)) || (idx_ok(f2) && es_ok(f1))) {
        return None;
    }
    let base_def = *def.get(&base.id)?;
    let base_block = block_of_inst(func, base_def)?;
    if !dom.dominates(base_block, preheader) {
        return None;
    }
    Some(base)
}

/// `true` iff `factor` is `Sxtw(iv-through-copies)` and both the extend and its
/// source are in-loop (the pure-i32 addressing arm of the chain load).
fn chain_is_sext_iv(
    func: &MachFunction,
    def: &HashMap<u32, InstId>,
    loop_insts: &HashSet<InstId>,
    factor: VReg,
    iv: VReg,
) -> bool {
    let Some(&id) = def.get(&factor.id) else {
        return false;
    };
    if !loop_insts.contains(&id) {
        return false;
    }
    let inst = func.inst(id);
    inst.opcode == AArch64Opcode::Sxtw
        && inst.operands.len() == 2
        && vreg_of(&inst.operands[1]).is_some_and(|s| resolves_to_iv(func, def, s, iv))
}

/// Chain variant of [`byte_load_base`]: the byte (`memchr`, `.16B`) widening
/// load `dst = Uxtb/Sxtb(LdrbRI(base + idx))` where `idx` is a direct `Gpr64`
/// copy of `iv` OR `Sxtw(iv)`, address either `AddRR(base, idx)` (the `*1` gep
/// folded, either order) or `Madd(idx, 1, base)`.
fn chain_byte_load_base(
    func: &MachFunction,
    dom: &DomTree,
    def: &HashMap<u32, InstId>,
    loop_insts: &HashSet<InstId>,
    iv: VReg,
    preheader: BlockId,
    dst: VReg,
) -> Option<VReg> {
    if dst.class != RegClass::Gpr32 {
        return None;
    }
    let ext_id = *def.get(&dst.id)?;
    if !loop_insts.contains(&ext_id) {
        return None;
    }
    let ext = func.inst(ext_id);
    if !matches!(ext.opcode, AArch64Opcode::Uxtb | AArch64Opcode::Sxtb) || ext.operands.len() != 2 {
        return None;
    }
    let loaded = vreg_of(&ext.operands[1])?;
    if loaded.class != RegClass::Gpr32 {
        return None;
    }
    let load_id = *def.get(&loaded.id)?;
    if !loop_insts.contains(&load_id) {
        return None;
    }
    let load = func.inst(load_id);
    if load.opcode != AArch64Opcode::LdrbRI
        || load.operands.len() != 3
        || imm_of(&load.operands[2]) != Some(0)
    {
        return None;
    }
    let addr = vreg_of(&load.operands[1])?;
    let addr_id = *def.get(&addr.id)?;
    if !loop_insts.contains(&addr_id) {
        return None;
    }
    let addr_inst = func.inst(addr_id);
    let is_sext_iv = |factor: VReg| chain_is_sext_iv(func, def, loop_insts, factor, iv);
    let idx_ok = |factor: VReg| resolves_to_iv(func, def, factor, iv) || is_sext_iv(factor);
    let base = match addr_inst.opcode {
        AArch64Opcode::AddRR if addr_inst.operands.len() == 3 => {
            let a = vreg_of(&addr_inst.operands[1])?;
            let b = vreg_of(&addr_inst.operands[2])?;
            if idx_ok(a) {
                b
            } else if idx_ok(b) {
                a
            } else {
                return None;
            }
        }
        AArch64Opcode::Madd if addr_inst.operands.len() == 4 => {
            let f1 = vreg_of(&addr_inst.operands[1])?;
            let f2 = vreg_of(&addr_inst.operands[2])?;
            let base = vreg_of(&addr_inst.operands[3])?;
            let es_ok = |f: VReg| const_value(func, def, f) == Some(ELEM_BYTES_B);
            if (idx_ok(f1) && es_ok(f2)) || (idx_ok(f2) && es_ok(f1)) {
                base
            } else {
                return None;
            }
        }
        _ => return None,
    };
    let base_def = *def.get(&base.id)?;
    let base_block = block_of_inst(func, base_def)?;
    if !dom.dominates(base_block, preheader) {
        return None;
    }
    Some(base)
}

/// Recognize the equality early-exit MATCH block: a 2-successor block whose
/// compare is `CmpRR(a[iv], key)` and whose branch encodes "exit iff
/// `a[iv] == key`". Two orientations are accepted, both meaning the loop leaves
/// on equality:
///   * `CC_EQ`: the taken (`b.eq`) edge LEAVES the loop body; the fall-through
///     continues.
///   * `CC_NE`: the taken (`b.ne`) edge CONTINUES in body; the fall-through
///     (equality) leaves.
///     `a[iv]` is resolved via [`chain_load_base`] / [`chain_byte_load_base`] and
///     `key` must be loop-invariant and NOT the induction. Returns
///     `(base, key, is_byte, continue_target)`. Fail-closed otherwise. This is what
///     distinguishes the match block from a bounds guard (`iv <u N`, `CC_LO`): the
///     compare is load-vs-key with an EQUALITY exit, never `iv`-vs-`N`.
#[allow(clippy::too_many_arguments)]
fn recognize_search_match(
    func: &MachFunction,
    dom: &DomTree,
    def: &HashMap<u32, InstId>,
    loop_insts: &HashSet<InstId>,
    blk: BlockId,
    body: &HashSet<BlockId>,
    iv: VReg,
    preheader: BlockId,
) -> Option<(VReg, VReg, bool, BlockId)> {
    let insts = func.block(blk).insts.clone();
    let bcond_id = *insts
        .iter()
        .find(|&&id| func.inst(id).opcode == AArch64Opcode::BCond)?;
    let bcond = func.inst(bcond_id);
    let cc = imm_of(&bcond.operands[0])?;
    let br = insts
        .iter()
        .rev()
        .map(|&id| func.inst(id))
        .find(|i| i.opcode == AArch64Opcode::B)?;
    let taken = *branch_targets(bcond).first()?;
    let fall = *branch_targets(br).first()?;
    // The continue edge must stay in body; the exit (equality) edge must leave.
    let cont = match cc {
        CC_EQ => {
            if body.contains(&taken) || !body.contains(&fall) {
                return None;
            }
            fall
        }
        CC_NE => {
            if !body.contains(&taken) || body.contains(&fall) {
                return None;
            }
            taken
        }
        _ => return None,
    };
    let cmp_id = nearest_cmp_before(func, &insts, bcond_id)?;
    let cmp = func.inst(cmp_id);
    if cmp.opcode != AArch64Opcode::CmpRR {
        return None;
    }
    let c0 = vreg_of(&cmp.operands[0])?;
    let c1 = vreg_of(&cmp.operands[1])?;
    // One operand is the `a[iv]` load, the other the invariant key (either order;
    // i32 direct load, else the byte width's widening load — mutually exclusive
    // on the opcode).
    for &(load_res, key) in &[(c0, c1), (c1, c0)] {
        let (base, is_byte) = if let Some(base) =
            chain_load_base(func, dom, def, loop_insts, iv, preheader, load_res)
        {
            (base, false)
        } else if let Some(base) =
            chain_byte_load_base(func, dom, def, loop_insts, iv, preheader, load_res)
        {
            (base, true)
        } else {
            continue;
        };
        if !invariant(func, dom, def, key, preheader) {
            continue;
        }
        if resolves_to_iv(func, def, key, iv) {
            continue; // the key must not be the induction variable
        }
        return Some((base, key, is_byte, cont));
    }
    None
}

/// Walk the chain header -> ... -> latch, classifying every block and proving
/// SINGLE-N agreement, full coverage, and EXACTLY ONE equality match block.
/// Returns `(bound, (base, key, is_byte))`. Fail-closed on any block off the
/// header->latch structure, a limit disagreement, a missing/duplicate match, or
/// an unclassifiable shape (e.g. an outer loop whose body contains a 2-in
/// sub-block).
#[allow(clippy::too_many_arguments)]
fn walk_find_chain(
    func: &MachFunction,
    dom: &DomTree,
    def: &HashMap<u32, InstId>,
    loop_insts: &HashSet<InstId>,
    body: &HashSet<BlockId>,
    header: BlockId,
    latch: BlockId,
    iv: VReg,
    preheader: BlockId,
) -> Option<(ChainBound, (VReg, VReg, bool))> {
    let mut visited: HashSet<BlockId> = HashSet::new();
    let mut bound: Option<ChainBound> = None;
    let mut mtch: Option<(VReg, VReg, bool)> = None;
    let mut cur = header;
    for _ in 0..(body.len() + 1) {
        if !body.contains(&cur) || visited.contains(&cur) {
            return None;
        }
        if cur == latch {
            visited.insert(latch);
            break;
        }
        let succs = &func.block(cur).succs;
        let in_body = succs.iter().filter(|s| body.contains(s)).count();
        let out_body = succs.len() - in_body;
        if succs.len() == 2 && in_body == 1 && out_body == 1 {
            // Either the loop-continue / bounds-guard diamond (`iv <u N`, `CC_LO`,
            // taken edge IN body) OR the equality early-exit match block
            // (`a[iv] == key`, the equality edge LEAVES the loop). Disambiguate by
            // compare shape; the two are mutually exclusive on the condition code.
            if let Some((x, b, t_lo)) = recognize_chain_guard(func, cur, body) {
                if !resolves_to_iv(func, def, x, iv) {
                    return None;
                }
                match bound {
                    Some(bb) if !chain_bound_agrees(func, def, bb, b) => return None,
                    None => bound = Some(b),
                    _ => {}
                }
                visited.insert(cur);
                cur = t_lo;
            } else if let Some((base, key, is_byte, cont)) =
                recognize_search_match(func, dom, def, loop_insts, cur, body, iv, preheader)
            {
                if mtch.is_some() {
                    return None; // EXACTLY ONE match block
                }
                mtch = Some((base, key, is_byte));
                visited.insert(cur);
                cur = cont;
            } else {
                return None;
            }
        } else if succs.len() == 1 && in_body == 1 {
            // Pass-through (its bounds guard was elided to an unconditional edge).
            visited.insert(cur);
            cur = succs[0];
        } else {
            return None;
        }
    }
    if visited.len() != body.len() {
        return None;
    }
    Some((bound?, mtch?))
}

/// Build a def map (`vreg id -> defining InstId`) considering ONLY instructions
/// that are LIVE (reachable through `block_order`). The flat [`build_def_map`]
/// iterates the entire instruction storage, which can still contain DEAD
/// instructions that bounds-check-elim unhooked from their blocks but left in
/// `func.insts` (e.g. the `TrapBoundsCheckExact` carrier whose operand0 is a
/// READ of the iv-copy); a dead duplicate would shadow the live in-block def and
/// break the copy/address walks. Restricting to the current CFG fixes this.
/// Mirrors [`crate::neon_minmax`]'s `build_live_def_map`.
fn build_live_def_map(func: &MachFunction) -> HashMap<u32, InstId> {
    let mut map = HashMap::new();
    for &bid in &func.block_order {
        for &id in &func.block(bid).insts {
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

/// Number of LIVE (in a `block_order` block) instructions defining `v.id`.
/// Machine IR is not SSA: the chain path's register-bound constant recovery is
/// sound only when the `Movz` is the SOLE def, so the value reaching the loop
/// guard is unambiguous. Counts defs the same way [`build_live_def_map`] finds
/// them (operand 0 of a `produces_def` opcode).
fn unique_live_def_count(func: &MachFunction, v: VReg) -> usize {
    let mut n = 0;
    for &bid in &func.block_order {
        for &id in &func.block(bid).insts {
            let inst = func.inst(id);
            if let Some(MachOperand::VReg(d)) = inst.operands.first()
                && d.id == v.id
                && produces_def(inst.opcode)
            {
                n += 1;
            }
        }
    }
    n
}

/// Materialize a non-negative i32-range constant into a fresh preheader vreg of
/// `class` via the isel `Movz`(+`Movk`) convention. Used for the compile-time
/// vector guard limit `N - (width-1)`, which the chain path cannot read from a
/// register (the loop bound is a folded immediate inside the loop). Mirrors
/// [`crate::neon_minmax`]'s `materialize_const`.
fn materialize_const(func: &mut MachFunction, pre: InstId, k: i64, class: RegClass) -> VReg {
    let b = alloc(func, class);
    let lo = k & 0xFFFF;
    let hi = (k >> 16) & 0xFFFF;
    emit_before(func, pre, AArch64Opcode::Movz, vec![vreg(b), imm(lo)]);
    if hi != 0 {
        emit_before(
            func,
            pre,
            AArch64Opcode::Movk,
            vec![vreg(b), imm(hi), imm(16)],
        );
    }
    b
}

/// Whether `val`'s definition dominates the preheader (loop-invariant).
fn invariant(
    func: &MachFunction,
    dom: &DomTree,
    def: &HashMap<u32, InstId>,
    val: VReg,
    preheader: BlockId,
) -> bool {
    let Some(&id) = def.get(&val.id) else {
        return false;
    };
    let Some(block) = block_of_inst(func, id) else {
        return false;
    };
    dom.dominates(block, preheader)
}

fn is_increment_by_one(
    func: &MachFunction,
    def: &HashMap<u32, InstId>,
    iv_src: VReg,
    iv: VReg,
) -> bool {
    let Some(&id) = def.get(&iv_src.id) else {
        return false;
    };
    let inst = func.inst(id);
    match inst.opcode {
        AArch64Opcode::AddRI => {
            vreg_of(&inst.operands[1]) == Some(iv) && imm_of(&inst.operands[2]) == Some(1)
        }
        AArch64Opcode::AddRR => {
            let a = vreg_of(&inst.operands[1]);
            let b = vreg_of(&inst.operands[2]);
            (a == Some(iv) && b.is_some_and(|b| const_value(func, def, b) == Some(1)))
                || (b == Some(iv) && a.is_some_and(|a| const_value(func, def, a) == Some(1)))
        }
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// Transformation
// ---------------------------------------------------------------------------

/// Splice the NEON block-filter loop in front of the scalar search loop.
///
/// New CFG (all fresh blocks are inserted before `header`; `W` = the width's
/// block size, 16 i32 elements or 64 bytes):
/// ```text
///   preheader --------------------> vh
///   vh: sxtw(iv) < sxtw(n)-(W-1) ? vb : header   (guard: full block in [0,n))
///   vb: load W ; CMEQ x4 ; OR ; anyhit != 0 ? header : vl
///   vl: iv += W ; -> vh
/// ```
/// Both vector exits target the UNCHANGED `header`, which re-scans from the
/// current `iv` (a matching block's base, or the first unprocessed tail index).
fn apply(func: &mut MachFunction, rec: &FindRecognized) -> bool {
    // Per-width parameters: the i32 path is `.4S` over 16-element blocks; the
    // byte (`memchr`) path is `.16B` over 64-byte blocks. The block is 64 bytes
    // (4 Q registers) either way, so the load walk is identical.
    let (width, elem_bytes, arr_code, elem_code) = if rec.is_byte {
        (UNROLL as i64 * VF_B, ELEM_BYTES_B, ARR_B16, ELEM_B)
    } else {
        (WIDTH, ELEM_BYTES, ARR_S4, ELEM_S)
    };

    let vh = func.create_block();
    let vb = func.create_block();
    let vl = func.create_block();
    insert_new_blocks_before(func, rec.header, &[vh, vb, vl]);
    func.add_edge(vh, vb);
    func.add_edge(vh, rec.header); // guard fail -> scalar tail (iv unchanged)
    func.add_edge(vb, rec.header); // any hit    -> scalar re-scan (iv = block base)
    func.add_edge(vb, vl); // no hit -> next block
    func.add_edge(vl, vh);

    let pre = rec.preheader_term;

    // --- Preheader: key splat, element-size const, guard bound, running pointer
    // `p = base + iv0*elem`.
    // On the byte width, `DUP Vd.16B, Wkey` broadcasts trunc8(key) — the safe
    // superset filter (see the module docs' byte-width section).
    let key_splat = alloc(func, RegClass::Fpr128);
    emit_before(
        func,
        pre,
        AArch64Opcode::NeonDupGen,
        vec![vreg(key_splat), vreg(rec.key), imm(elem_code)],
    );
    let c_es = alloc(func, RegClass::Gpr64);
    emit_before(
        func,
        pre,
        AArch64Opcode::Movz,
        vec![vreg(c_es), imm(elem_bytes)],
    );

    // Guard bound in `Gpr64`. Register bound (strict path): `main = sxtw(n) -
    // (width-1)` computed at runtime (exact in i64 — `sxtw(n)` is in i32 range).
    // Constant bound (forward-chain path): `main = N - (width-1)` when
    // `N >= width`, else `0` — a compile-time constant; when `N < width` no full
    // block fits and the UNSIGNED guard `iv <u 0` NEVER passes (the scalar loop
    // does everything).
    let main_bound = if let Some(n) = rec.bound_const {
        let k = if n >= width { n - (width - 1) } else { 0 };
        materialize_const(func, pre, k, RegClass::Gpr64)
    } else {
        let bound_reg = rec.bound.expect("strict path carries a register bound");
        let nb64 = alloc(func, RegClass::Gpr64);
        emit_before(
            func,
            pre,
            AArch64Opcode::Sxtw,
            vec![vreg(nb64), vreg(bound_reg)],
        );
        let mb = alloc(func, RegClass::Gpr64);
        emit_before(
            func,
            pre,
            AArch64Opcode::SubRI,
            vec![vreg(mb), vreg(nb64), imm(width - 1)],
        );
        mb
    };

    // Running pointer `p = base + iv0*elem` (`Madd d, n, m, a = a + n*m`). The
    // `Gpr64` induction is used DIRECTLY (the bridge's mixed i64-index / i32-
    // element addressing); the `Gpr32` strict induction is sign-extended first.
    let p = if rec.iv_is_i64 {
        let p = alloc(func, RegClass::Gpr64);
        emit_before(
            func,
            pre,
            AArch64Opcode::Madd,
            vec![vreg(p), vreg(rec.iv), vreg(c_es), vreg(rec.base)],
        );
        p
    } else {
        let si0 = alloc(func, RegClass::Gpr64);
        emit_before(
            func,
            pre,
            AArch64Opcode::Sxtw,
            vec![vreg(si0), vreg(rec.iv)],
        );
        let p = alloc(func, RegClass::Gpr64);
        emit_before(
            func,
            pre,
            AArch64Opcode::Madd,
            vec![vreg(p), vreg(si0), vreg(c_es), vreg(rec.base)],
        );
        p
    };

    // --- Vector header: admit a vector iteration only when the whole block
    // `[iv, iv+width-1]` is `< n` (in-bounds within [0,n)). The `Gpr64` chain
    // compares `iv <u main_bound` UNSIGNED — algebraically `iv + (width-1) <u n`
    // — matching the scalar `iv <u N` loop-continue bit-for-bit. The `Gpr32`
    // strict path sign-extends iv and does a signed `sxtw(iv) < main_bound`.
    if rec.iv_is_i64 {
        emit(
            func,
            vh,
            AArch64Opcode::CmpRR,
            vec![vreg(rec.iv), vreg(main_bound)],
        );
        emit(func, vh, AArch64Opcode::BCond, vec![imm(CC_LO), block(vb)]);
    } else {
        let gi = alloc(func, RegClass::Gpr64);
        emit(func, vh, AArch64Opcode::Sxtw, vec![vreg(gi), vreg(rec.iv)]);
        emit(
            func,
            vh,
            AArch64Opcode::CmpRR,
            vec![vreg(gi), vreg(main_bound)],
        );
        emit(func, vh, AArch64Opcode::BCond, vec![imm(CC_LT), block(vb)]);
    }
    emit(func, vh, AArch64Opcode::B, vec![block(rec.header)]);

    // --- Vector body: walk the running pointer with `UNROLL/2` post-index
    // `LDP Qt1, Qt2, [p], #32` pair loads (64 bytes = the block, in order), then
    // one `CMEQ.4S`/`.16B` mask per vector against the key splat.
    let mut masks: Vec<VReg> = Vec::with_capacity(UNROLL);
    for _pair in 0..UNROLL / 2 {
        let q0 = alloc(func, RegClass::Fpr128);
        let q1 = alloc(func, RegClass::Fpr128);
        emit(
            func,
            vb,
            AArch64Opcode::NeonLdpQPost,
            vec![vreg(q0), vreg(q1), vreg(p), imm(32)],
        );
        for q in [q0, q1] {
            let m = alloc(func, RegClass::Fpr128);
            emit(
                func,
                vb,
                AArch64Opcode::NeonCmeqV,
                vec![vreg(m), vreg(q), vreg(key_splat), imm(arr_code)],
            );
            masks.push(m);
        }
    }
    // OR-tree the 4 masks: `o` has an all-ones lane wherever ANY vector
    // matched, so `o != 0` iff some `a[iv+j] == key`.
    let mut o = masks[0];
    for &m in &masks[1..] {
        let n = alloc(func, RegClass::Fpr128);
        emit(
            func,
            vb,
            AArch64Opcode::NeonOrrV,
            vec![vreg(n), vreg(o), vreg(m)],
        );
        o = n;
    }
    // any-hit test: OR the two 64-bit halves of `o` in a GPR, compare to zero.
    // No horizontal-reduce op — `UMOV Xd, o.D[lane]` is the shipping allowlisted
    // lane extract. `o != 0` <=> the two halves OR to a nonzero value.
    let lo = alloc(func, RegClass::Gpr64);
    emit(
        func,
        vb,
        AArch64Opcode::NeonUmovGen,
        vec![vreg(lo), vreg(o), imm(0), imm(ELEM_D)],
    );
    let hi = alloc(func, RegClass::Gpr64);
    emit(
        func,
        vb,
        AArch64Opcode::NeonUmovGen,
        vec![vreg(hi), vreg(o), imm(1), imm(ELEM_D)],
    );
    let any = alloc(func, RegClass::Gpr64);
    emit(
        func,
        vb,
        AArch64Opcode::OrrRR,
        vec![vreg(any), vreg(lo), vreg(hi)],
    );
    emit(func, vb, AArch64Opcode::CmpRI, vec![vreg(any), imm(0)]);
    // hit -> scalar loop header (iv still holds the block base); else next block.
    emit(
        func,
        vb,
        AArch64Opcode::BCond,
        vec![imm(CC_NE), block(rec.header)],
    );
    emit(func, vb, AArch64Opcode::B, vec![block(vl)]);

    // --- Vector latch: advance iv by the block width (the running pointer
    // advanced 64 bytes = width*elem via the post-index loads).
    emit(
        func,
        vl,
        AArch64Opcode::AddRI,
        vec![vreg(rec.iv), vreg(rec.iv), imm(width)],
    );
    emit(func, vl, AArch64Opcode::B, vec![block(vh)]);

    // --- COMMIT: enter the vector loop from the preheader.
    if !rewrite_block_target(func.inst_mut(pre), rec.header, vh) {
        return false;
    }
    remove_cfg_edge(func, rec.preheader, rec.header);
    func.add_edge(rec.preheader, vh);
    true
}

// ---------------------------------------------------------------------------
// Emission / CFG helpers (self-contained, mirroring the sibling NEON passes).
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

fn build_def_map(func: &MachFunction) -> HashMap<u32, InstId> {
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

fn produces_def(op: AArch64Opcode) -> bool {
    use AArch64Opcode::*;
    !matches!(op, CmpRR | CmpRI | BCond | B)
}

fn block_of_inst(func: &MachFunction, target: InstId) -> Option<BlockId> {
    for (idx, block) in func.blocks.iter().enumerate() {
        if block.insts.contains(&target) {
            return Some(BlockId(idx as u32));
        }
    }
    None
}

fn branch_targets(inst: &MachInst) -> Vec<BlockId> {
    inst.operands
        .iter()
        .filter_map(|op| match op {
            MachOperand::Block(b) => Some(*b),
            _ => None,
        })
        .collect()
}

fn rewrite_block_target(inst: &mut MachInst, old: BlockId, new: BlockId) -> bool {
    let mut changed = false;
    for op in &mut inst.operands {
        if matches!(op, MachOperand::Block(b) if *b == old) {
            *op = MachOperand::Block(new);
            changed = true;
        }
    }
    changed
}

fn remove_cfg_edge(func: &mut MachFunction, from: BlockId, to: BlockId) {
    func.block_mut(from).succs.retain(|&s| s != to);
    func.block_mut(to).preds.retain(|&p| p != from);
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

#[cfg(test)]
mod tests;
