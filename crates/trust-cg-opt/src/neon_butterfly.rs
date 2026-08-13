// trust-cg-opt - SOUND NEON AoS complex-butterfly (FFT) vectorizer (aarch64)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! # NEON AoS stride-2 complex-butterfly vectorizer (`neon-butterfly`)
//!
//! Vectorizes the radix-2 FFT butterfly inner loop over an ARRAY-OF-STRUCTS
//! `struct complex { float rp, ip; }` stream (the Stanford `Oscar.c` `Fft`
//! kernel — clang -O3 4-wide NEON-vectorizes it; without this pass trust-cg
//! runs it fully scalar, the largest single vectorizer gap):
//!
//! ```text
//! do {                                             // i64 iv, do-while
//!   w[i+k].rp = z[i].rp + z[i+m].rp;               // (A) sum stream
//!   w[i+k].ip = z[i].ip + z[i+m].ip;
//!   w[i+j].rp = e.rp*(z[i].rp - z[i+m].rp)         // (B) twiddle stream
//!             - e.ip*(z[i].ip - z[i+m].ip);        //     (fmul + fused fmadd)
//!   w[i+j].ip = e.rp*(z[i].ip - z[i+m].ip)
//!             + e.ip*(z[i].rp - z[i+m].rp);
//!   i = i + 1;
//! } while (i_old < j);
//! ```
//!
//! where `e` is a fixed (loop-invariant address) twiddle cell reloaded inside
//! the loop (clang -O1 cannot hoist it: the `w` stores might alias it), and
//! each complex is TWO adjacent f32 fields (byte offsets +0 / +4, element
//! stride 8). Two lanes (= one whole complex PAIR, `.4S`) are processed per
//! vector iteration on the INTERLEAVED data — no deinterleave is needed:
//!
//! ```text
//! vz   = LD1.4S  z[i]        = [zr0, zi0, zr1, zi1]
//! vzm  = LD1.4S  z[i+m]
//! sum  = FADD.4S vz, vzm                      -> ST1.4S w[i+k]
//! d    = FSUB.4S vz, vzm     = [dr0, di0, dr1, di1]
//! dsw  = REV64.4S d          = [di0, dr0, di1, dr1]   (32-bit pair swap)
//! dsg  = EOR.16B dsw, MASK   = [-di0, dr0, -di1, dr1] (MASK = [0x80000000,0]x2)
//! t    = FMUL.4S vei, dsg    = [ei*-di0, ei*dr0, ...]
//! res  = FMLA.4S t, ver, d   = [ei*-di0 + er*dr0, ei*dr0 + er*di0, ...]
//!                                             -> ST1.4S w[i+j]
//! ```
//!
//! with `ver`/`vei` the broadcast twiddle fields, hoisted to the vector
//! preheader (licensed by the runtime disjointness check below).
//!
//! ## Why the result is BIT-IDENTICAL to the scalar loop
//!
//! Purely elementwise: lane `2t+f`'s result is the EXACT scalar op tree of
//! iteration `i0+t`, field `f` — no cross-lane arithmetic:
//!
//! * A64 NEON `FADD/FSUB/FMUL.4S` compute per lane the SAME IEEE-754 op as the
//!   scalar `S`-form under the same FPCR (the [`crate::neon_fmap`] argument,
//!   verbatim). NO CONTRACTION is introduced: the source's `fmul` stays
//!   `FMUL.4S` and only the source's ALREADY-FUSED `llvm.fmuladd` (`FmaddRR`)
//!   becomes the equally-fused `FMLA.4S` (`FPMulAdd` with identical addend /
//!   multiplicand roles — one rounding, exactly as the scalar rounds).
//! * `REV64.4S` and `EOR.16B` are exact bit movers; XOR with the lane pattern
//!   `[0x8000_0000, 0, …]` flips ONLY the sign bit of the swapped `di` lanes —
//!   precisely the scalar `FNEG` (a pure sign-bit inversion, NaN included),
//!   and the even (`dr`) lanes XOR with 0 (identity).
//! * Operand ORDER is preserved role-for-role (recognition is order-sensitive
//!   and fails closed on any commuted variant), so NaN-propagation picks the
//!   same operand payloads scalar execution picks.
//!
//! ## Why the transform is SOUND (memory) — runtime alias versioning
//!
//! The scalar body RELOADS `z`/`e` cells after `w` stores, so its dataflow
//! only simplifies to the pure butterfly above when the stores do not touch
//! the loaded cells. The vector loop is therefore entered ONLY behind a
//! runtime preamble (the [`crate::neon_fmap`] regime-C scheme, extended to
//! this shape's SEVEN range pairs) proving all of:
//!
//! * `0 <= i0` and `0 <= j < 2^31` (so the trip byte count `T8 = (j-i0+1)*8 <
//!   2^34` is exact) and `i0 < j` (at least one full 2-lane block);
//! * the two STORE ranges `A = [wA, wA+T8)` / `B = [wB, wB+T8)` are each
//!   disjoint from BOTH read ranges `Z1`/`Z2` (each `[z*, z*+T8)`) and from
//!   the 8-byte twiddle cell `E`, and from EACH OTHER (the vector iteration
//!   reorders A/B stores of adjacent lanes).
//!
//! Each pair is tested WRAP-SAFELY: ranges `[x, x+Lx)`, `[y, y+Ly)` (byte sets
//! taken mod 2^64, exactly the address arithmetic the scalar loop performs)
//! are disjoint iff `(y - x) >=u Lx && (x - y) >=u Ly`. Any failing pair
//! branches to the UNTOUCHED scalar loop — sound independent of any `noalias`
//! claim. Under the license, every reload equals the first load, all four
//! store cells across the trip space are pairwise distinct or ordered
//! identically, and the vector loop computes the same final memory.
//!
//! Every vector memory access is a SUBSET of the scalar loop's access set:
//! lane pair `{i, i+1}` is admitted only while `i < j` (both lanes are
//! iterations the scalar do-while performs), and the preheader twiddle loads
//! read exactly the two `E` cells the scalar's first iteration reads.
//!
//! ## Exit-state equivalence
//!
//! The scalar do-while carries exactly TWO registers out: the induction `iv`
//! (dead outside — VERIFIED, only redefined) and `ivs = iv+1` (the exit
//! live-out). The vector loop steps `iv` by 2 and exits with `iv ∈ {j, j+1}`:
//! at `iv == j` it falls into the scalar do-while, which runs the last
//! iteration and computes `ivs` itself; at `iv == j+1` (all lanes consumed)
//! the do-while must be SKIPPED (it would store `w[j+1+k]` — the rotated
//! remainder-0 class), so a `iv > j` guard routes to the loop's true exit
//! setting `ivs = iv = j+1` — the exact value the scalar exit produces.
//! Recognition verifies NO other loop-defined value (flags included: the exit
//! path re-defines NZCV before any read) is observable outside.
//!
//! If ANY premise fails — a different op tree or operand order, an extra
//! load/store/opcode, an f64 field, a non-`+1` step, an out-of-loop use of a
//! loop temp, an unresolvable address chain — the loop is left ENTIRELY to
//! the scalar path: fail-closed beats miscompile.
//!
//! Runs right after [`crate::neon_fmap`] (disjoint shapes: fmap bails on this
//! loop's multi-store body). Disable with
//! `TRUST_CG_DISABLE_PASSES=neon_butterfly`.

use std::collections::{HashMap, HashSet};

use trust_cg_ir::{
    AArch64Opcode, BlockId, InstId, MachFunction, MachInst, MachOperand, RegClass, VReg,
};

use crate::dom::DomTree;
use crate::effects;
use crate::loops::LoopAnalysis;
use crate::pass_manager::{AnalysisCache, MachinePass};

/// INTEGER-op arrangement code for `.4S` (NeonLd1Post/NeonSt1Post/NeonRev64V).
const ARR_S4: i64 = 5;
/// FP-op arrangement code for `.4S` (NeonFaddV/NeonFsubV/NeonFmulV/NeonFmlaV).
const FARR_S4: i64 = 1;
/// NEON element-size operand code for `S` (32-bit) lanes (DUP element).
const ELEM_S: i64 = 4;
/// NEON element-size operand code for `D` (64-bit) lanes (DUP general).
const ELEM_D: i64 = 8;
/// AArch64 condition codes.
const CC_LT: i64 = 11;
const CC_GT: i64 = 12;
const CC_GE: i64 = 10;
const CC_LO: i64 = 3;
/// Element stride in bytes: one `struct complex { f32 rp, ip; }`.
const ELEM_BYTES: i64 = 8;
/// Largest admitted twiddle-cell byte offset: `AddRI` 12-bit immediate minus
/// the `+4` ip field (the range-start computation must stay encodable).
const MAX_E_OFF: i64 = 4088;

/// The `neon-butterfly` machine pass.
#[derive(Default)]
pub struct NeonButterflyPass {
    /// Number of loops vectorized in the last run (diagnostics/tests).
    fired: usize,
}

impl NeonButterflyPass {
    pub fn new() -> Self {
        Self { fired: 0 }
    }

    /// Loops vectorized in the last `run`.
    pub fn fired(&self) -> usize {
        self.fired
    }
}

impl MachinePass for NeonButterflyPass {
    fn name(&self) -> &str {
        "neon-butterfly"
    }

    fn run(&mut self, func: &mut MachFunction) -> bool {
        let dom = DomTree::compute(func);
        let loops = LoopAnalysis::compute(func, &dom);
        self.run_core(func, &dom, &loops)
    }

    // Share the AnalysisCache's CFG-derived analyses (see NeonFMapPass): both
    // depend only on the CFG, which the cache invalidates on any CFG change.
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

impl NeonButterflyPass {
    fn run_core(&mut self, func: &mut MachFunction, dom: &DomTree, loops: &LoopAnalysis) -> bool {
        self.fired = 0;
        let mut plans = Vec::new();
        for lp in loops.all_loops() {
            if let Some(rec) =
                RecognizedButterfly::recognize(func, dom, lp.header, lp.latch, &lp.body)
            {
                plans.push(rec);
            }
        }
        let mut changed = false;
        for rec in plans {
            if apply_butterfly(func, &rec) {
                self.fired += 1;
                changed = true;
            }
        }
        if changed && std::env::var("TRUST_CG_DUMP_NEONBUTTERFLY").is_ok() {
            eprintln!(
                "[neon-butterfly] fn={} vectorized={}",
                func.name, self.fired
            );
        }
        changed
    }
}

// ---------------------------------------------------------------------------
// Recognition
// ---------------------------------------------------------------------------

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

/// 16-bit `Movz` constant value of `val`, if any.
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

/// A resolved address recipe: `base + Σ invs[..]*8 (+ iv*8 if has_iv) + off`
/// with `base`/`invs` loop-invariant `Gpr64` registers.
#[derive(Clone)]
struct AddrChain {
    base: VReg,
    /// Loop-invariant scaled index registers (each contributes `idx*8`),
    /// SORTED by vreg id (addition commutes; canonical for stream keys).
    invs: Vec<VReg>,
    has_iv: bool,
    /// Accumulated constant byte offset (`AddRI` immediates).
    off: i64,
    /// Chain member instructions INSIDE the loop (for the completeness scan).
    insts: Vec<InstId>,
}

impl AddrChain {
    /// Canonical stream key: same `(base, scaled invariant set, iv presence)`
    /// — cells of one stream differ only in `off`.
    fn key(&self) -> (u32, Vec<u32>, bool) {
        (
            self.base.id,
            self.invs.iter().map(|v| v.id).collect(),
            self.has_iv,
        )
    }
}

/// The invariant part of a stream's address (for versioning + re-emission).
#[derive(Clone)]
struct StreamRecipe {
    base: VReg,
    invs: Vec<VReg>,
}

/// A fully validated butterfly loop.
struct RecognizedButterfly {
    preheader: BlockId,
    preheader_term: InstId,
    header: BlockId,
    exit: BlockId,
    iv: VReg,
    /// `iv + 1` — the loop's only exit live-out.
    ivs: VReg,
    bound: VReg,
    /// The shared `Movz(8)` element-size multiplier register.
    es: VReg,
    /// `z[i]` read stream (order = fadd/fsub LHS role).
    s1: StreamRecipe,
    /// `z[i+m]` read stream (RHS role).
    s2: StreamRecipe,
    /// `w[i+k]` sum-store stream.
    sa: StreamRecipe,
    /// `w[i+j]` twiddle-store stream.
    sb: StreamRecipe,
    /// Twiddle cell: `e.rp` at `[e_root + e_off]`, `e.ip` at `+4`.
    e_root: VReg,
    e_off: i64,
}

/// Opcodes permitted anywhere in the loop body (fail-closed on anything else).
fn allowed_op(op: AArch64Opcode) -> bool {
    use AArch64Opcode::*;
    matches!(
        op,
        Madd | AddRI
            | LdrRI
            | StrRI
            | FaddRR
            | FsubRR
            | FmulRR
            | FnegRR
            | FmaddRR
            | CmpRR
            | BCond
            | B
            | MovR
            | Copy
    )
}

/// True iff `val` is LOOP-INVARIANT: it has NO def inside the loop (this MIR
/// is not SSA — a register may have several defs on the paths AROUND the loop,
/// e.g. an enclosing loop's writeback; what matters is that its value cannot
/// change while the inner loop runs). Availability at the loop entry — where
/// the gate/preamble blocks read it — is guaranteed by the ORIGINAL loop's own
/// in-loop uses of the same register on the first iteration.
fn is_invariant(loop_defs: &HashSet<u32>, val: VReg) -> bool {
    !loop_defs.contains(&val.id)
}

impl RecognizedButterfly {
    fn recognize(
        func: &MachFunction,
        dom: &DomTree,
        header: BlockId,
        latch: BlockId,
        body: &HashSet<BlockId>,
    ) -> Option<Self> {
        // (R1) exactly a 2-block innermost loop {header, latch}, whitelisted.
        if header == latch || body.len() != 2 || !body.contains(&header) || !body.contains(&latch) {
            return None;
        }
        let mut loop_insts = HashSet::new();
        for &b in [header, latch].iter() {
            for &id in &func.block(b).insts {
                if !allowed_op(func.inst(id).opcode) {
                    return None;
                }
                loop_insts.insert(id);
            }
        }
        let def = build_def_map(func);
        // All registers DEFINED inside the loop (non-SSA: the def map alone
        // cannot decide invariance — see [`is_invariant`]).
        let mut loop_defs: HashSet<u32> = HashSet::new();
        for &id in &loop_insts {
            let inst = func.inst(id);
            if inst.opcode.produces_value()
                && let Some(MachOperand::VReg(d)) = inst.operands.first()
            {
                loop_defs.insert(d.id);
            }
        }

        // (R2) latch = EXACTLY the induction writeback + `B -> header`.
        let latch_insts = func.block(latch).insts.clone();
        if latch_insts.len() != 2 {
            return None;
        }
        let wb = func.inst(latch_insts[0]);
        let (iv, ivs) = match wb.opcode {
            AArch64Opcode::MovR | AArch64Opcode::Copy if wb.operands.len() == 2 => {
                (vreg_of(&wb.operands[0])?, vreg_of(&wb.operands[1])?)
            }
            _ => return None,
        };
        let lb = func.inst(latch_insts[1]);
        if lb.opcode != AArch64Opcode::B || branch_targets(lb) != vec![header] {
            return None;
        }
        if iv.class != RegClass::Gpr64 || ivs.class != RegClass::Gpr64 || iv.id == ivs.id {
            return None;
        }
        // ivs = AddRI(iv, 1) defined in the loop.
        let ivs_def = *def.get(&ivs.id)?;
        if !loop_insts.contains(&ivs_def) {
            return None;
        }
        let ivs_inst = func.inst(ivs_def);
        if ivs_inst.opcode != AArch64Opcode::AddRI
            || vreg_of(&ivs_inst.operands[1]) != Some(iv)
            || imm_of(&ivs_inst.operands[2]) != Some(1)
        {
            return None;
        }

        // (R3) header ends with the do-while bottom test on the OLD iv:
        // `CmpRR(iv, bound); BCond(LT, latch); B(exit)` (adjacent => sound
        // flag dataflow), `exit` outside the body.
        let hinsts = func.block(header).insts.clone();
        if hinsts.len() < 3 {
            return None;
        }
        let [cmp_id, bcond_id, b_id] = [
            hinsts[hinsts.len() - 3],
            hinsts[hinsts.len() - 2],
            hinsts[hinsts.len() - 1],
        ];
        let cmp = func.inst(cmp_id);
        if cmp.opcode != AArch64Opcode::CmpRR || vreg_of(&cmp.operands[0]) != Some(iv) {
            return None;
        }
        let bound = vreg_of(&cmp.operands[1])?;
        if bound.class != RegClass::Gpr64 {
            return None;
        }
        let bcond = func.inst(bcond_id);
        if bcond.opcode != AArch64Opcode::BCond
            || imm_of(&bcond.operands[0]) != Some(CC_LT)
            || branch_targets(bcond) != vec![latch]
        {
            return None;
        }
        let bterm = func.inst(b_id);
        if bterm.opcode != AArch64Opcode::B {
            return None;
        }
        let exit = *branch_targets(bterm).first()?;
        if body.contains(&exit) {
            return None;
        }

        // (R4) header preds are exactly {latch, preheader}; the preheader's
        // terminator branches to the header (rewired on commit).
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

        // (R5) bound loop-invariant; iv defined on the preheader path.
        if !is_invariant(&loop_defs, bound) {
            return None;
        }
        if !iv_def_dominates_preheader(func, dom, iv, preheader) {
            return None;
        }

        // (R6) resolve every load / store address into chains; collect cells.
        let mut chain_insts: HashSet<InstId> = HashSet::new();
        let resolve = |func: &MachFunction, addr: VReg, extra_off: i64| -> Option<AddrChain> {
            let mut chain = AddrChain {
                base: addr,
                invs: Vec::new(),
                has_iv: false,
                off: extra_off,
                insts: Vec::new(),
            };
            let mut cur = addr;
            for _ in 0..8 {
                let &did = def.get(&cur.id)?;
                if !loop_insts.contains(&did) {
                    // Terminal: a loop-invariant root.
                    if cur.class != RegClass::Gpr64 || !is_invariant(&loop_defs, cur) {
                        return None;
                    }
                    chain.base = cur;
                    chain.invs.sort_by_key(|v| v.id);
                    return Some(chain);
                }
                let inst = func.inst(did);
                match inst.opcode {
                    AArch64Opcode::AddRI if inst.operands.len() == 3 => {
                        chain.off += imm_of(&inst.operands[2])?;
                        chain.insts.push(did);
                        cur = vreg_of(&inst.operands[1])?;
                    }
                    AArch64Opcode::Madd if inst.operands.len() == 4 => {
                        let idx = vreg_of(&inst.operands[1])?;
                        let mul = vreg_of(&inst.operands[2])?;
                        if const_value(func, &def, mul) != Some(ELEM_BYTES) {
                            return None;
                        }
                        if idx == iv {
                            if chain.has_iv {
                                return None; // iv term admitted exactly once
                            }
                            chain.has_iv = true;
                        } else {
                            if !is_invariant(&loop_defs, idx)
                                || idx.class != RegClass::Gpr64
                                || chain.invs.len() >= 2
                            {
                                return None;
                            }
                            chain.invs.push(idx);
                        }
                        chain.insts.push(did);
                        cur = vreg_of(&inst.operands[3])?;
                    }
                    _ => return None,
                }
            }
            None // chain too deep
        };

        // Loads: map result vreg id -> (chain, cell offset). Stores collected.
        let mut load_cells: HashMap<u32, AddrChain> = HashMap::new();
        let mut es_reg: Option<VReg> = None;
        let mut stores: Vec<(InstId, AddrChain, VReg)> = Vec::new();
        for &id in &func.block(header).insts {
            let inst = func.inst(id);
            match inst.opcode {
                AArch64Opcode::LdrRI => {
                    let dst = vreg_of(&inst.operands[0])?;
                    if dst.class != RegClass::Fpr32 {
                        return None;
                    }
                    let addr = vreg_of(&inst.operands[1])?;
                    let off = imm_of(&inst.operands[2])?;
                    let chain = resolve(func, addr, off)?;
                    for &cid in &chain.insts {
                        chain_insts.insert(cid);
                    }
                    if load_cells.insert(dst.id, chain).is_some() {
                        return None; // reused load destination: ambiguous cell
                    }
                }
                AArch64Opcode::StrRI => {
                    let val = vreg_of(&inst.operands[0])?;
                    if val.class != RegClass::Fpr32 {
                        return None;
                    }
                    let addr = vreg_of(&inst.operands[1])?;
                    let off = imm_of(&inst.operands[2])?;
                    let chain = resolve(func, addr, off)?;
                    for &cid in &chain.insts {
                        chain_insts.insert(cid);
                    }
                    stores.push((id, chain, val));
                }
                _ => {}
            }
        }
        // All chains must share ONE element-size register (the Movz(8)).
        {
            let mut check_es = |c: &AddrChain| -> Option<()> {
                for &cid in &c.insts {
                    let inst = func.inst(cid);
                    if inst.opcode == AArch64Opcode::Madd {
                        let mul = vreg_of(&inst.operands[2])?;
                        match es_reg {
                            None => es_reg = Some(mul),
                            Some(e) if e.id == mul.id => {}
                            _ => return None,
                        }
                    }
                }
                Some(())
            };
            for c in load_cells.values() {
                check_es(c)?;
            }
            for (_, c, _) in &stores {
                check_es(c)?;
            }
        }
        let es = es_reg?;
        if !is_invariant(&loop_defs, es) {
            return None;
        }
        // `const_value(es) == 8` (checked per chain Madd) reads the def MAP —
        // sound only if the `Movz(8)` is the register's ONLY def anywhere.
        {
            let mut es_defs = 0usize;
            for inst in &func.insts {
                if inst.opcode.produces_value()
                    && matches!(inst.operands.first(), Some(MachOperand::VReg(d)) if d.id == es.id)
                {
                    es_defs += 1;
                }
            }
            if es_defs != 1 {
                return None;
            }
        }

        // (R7) EXACTLY four stores forming two iv-rooted streams at {+0, +4}.
        if stores.len() != 4 {
            return None;
        }
        type StreamKey = (u32, Vec<u32>, bool);
        type StoreGroup = (StreamKey, VReg, VReg);

        let mut store_groups: HashMap<StreamKey, Vec<(i64, VReg)>> = HashMap::new();
        let mut store_recipes: HashMap<StreamKey, StreamRecipe> = HashMap::new();
        for (_, chain, val) in &stores {
            if !chain.has_iv || !(chain.off == 0 || chain.off == 4) {
                return None;
            }
            store_groups
                .entry(chain.key())
                .or_default()
                .push((chain.off, *val));
            store_recipes.entry(chain.key()).or_insert(StreamRecipe {
                base: chain.base,
                invs: chain.invs.clone(),
            });
        }
        if store_groups.len() != 2 {
            return None;
        }
        // Each group: exactly one +0 and one +4 store.
        let mut groups: Vec<StoreGroup> = Vec::new();
        for (key, mut cells) in store_groups {
            if cells.len() != 2 {
                return None;
            }
            cells.sort_by_key(|(off, _)| *off);
            if cells[0].0 != 0 || cells[1].0 != 4 {
                return None;
            }
            groups.push((key, cells[0].1, cells[1].1));
        }

        // (R8) match the butterfly dag, cell-exactly and order-exactly.
        // Identify group (A): its +0 value is an Fadd of two iv-rooted cells.
        let fp_def = |v: VReg| -> Option<(&MachInst, InstId)> {
            let did = *def.get(&v.id)?;
            if !loop_insts.contains(&did) {
                return None;
            }
            Some((func.inst(did), did))
        };
        let cell_of = |v: VReg| -> Option<(&AddrChain, i64)> {
            let c = load_cells.get(&v.id)?;
            Some((c, c.off))
        };

        let mut a_grp: Option<usize> = None;
        for (gi, (_, v0, _)) in groups.iter().enumerate() {
            if let Some((inst, _)) = fp_def(*v0)
                && inst.opcode == AArch64Opcode::FaddRR
            {
                if a_grp.is_some() {
                    return None; // ambiguous
                }
                a_grp = Some(gi);
            }
        }
        let a_grp = a_grp?;
        let b_grp = 1 - a_grp;
        let (a_key, a0, a4) = groups[a_grp].clone();
        let (b_key, b0, b4) = groups[b_grp].clone();
        if a_key == b_key {
            return None;
        }

        let mut matched: HashSet<InstId> = HashSet::new();
        // a0 = Fadd(load(S1,0), load(S2,0)) — S1/S2 DEFINED here by position.
        let (a0i, a0id) = fp_def(a0)?;
        if a0i.opcode != AArch64Opcode::FaddRR {
            return None;
        }
        let (x, y) = (vreg_of(&a0i.operands[1])?, vreg_of(&a0i.operands[2])?);
        let (s1c, s1off) = cell_of(x)?;
        let (s2c, s2off) = cell_of(y)?;
        if s1off != 0 || s2off != 0 || !s1c.has_iv || !s2c.has_iv {
            return None;
        }
        let s1_key = s1c.key();
        let s2_key = s2c.key();
        if s1_key == s2_key {
            return None; // degenerate same-stream butterfly: fail closed
        }
        let s1 = StreamRecipe {
            base: s1c.base,
            invs: s1c.invs.clone(),
        };
        let s2 = StreamRecipe {
            base: s2c.base,
            invs: s2c.invs.clone(),
        };
        matched.insert(a0id);

        // Cell matcher: `v` is a load of stream `key` at offset `off`.
        let is_cell = |v: VReg, key: &(u32, Vec<u32>, bool), off: i64| -> bool {
            match cell_of(v) {
                Some((c, o)) => c.key() == *key && o == off,
                None => false,
            }
        };
        // a4 = Fadd(load(S1,4), load(S2,4)).
        let (a4i, a4id) = fp_def(a4)?;
        if a4i.opcode != AArch64Opcode::FaddRR
            || !is_cell(vreg_of(&a4i.operands[1])?, &s1_key, 4)
            || !is_cell(vreg_of(&a4i.operands[2])?, &s2_key, 4)
        {
            return None;
        }
        matched.insert(a4id);

        // Twiddle cell E: derived from b0's Fmadd multiplicand n.
        let (b0i, b0id) = fp_def(b0)?;
        if b0i.opcode != AArch64Opcode::FmaddRR || b0i.operands.len() != 4 {
            return None;
        }
        let er_v = vreg_of(&b0i.operands[1])?;
        let (ec, e_off) = cell_of(er_v)?;
        if ec.has_iv || !ec.invs.is_empty() || !(0..=MAX_E_OFF).contains(&e_off) {
            return None;
        }
        let e_root = ec.base;
        let e_key = ec.key();
        // A sub-tree matcher for `Fsub(load(S1,f), load(S2,f))`.
        let match_diff = |v: VReg, f: i64, matched: &mut HashSet<InstId>| -> Option<()> {
            let (i, id) = fp_def(v)?;
            if i.opcode != AArch64Opcode::FsubRR
                || !is_cell(vreg_of(&i.operands[1])?, &s1_key, f)
                || !is_cell(vreg_of(&i.operands[2])?, &s2_key, f)
            {
                return None;
            }
            matched.insert(id);
            Some(())
        };
        // b0 = Fmadd(er, dr, Fmul(ei, Fneg(di)))
        match_diff(vreg_of(&b0i.operands[2])?, 0, &mut matched)?;
        {
            let (mi, mid) = fp_def(vreg_of(&b0i.operands[3])?)?;
            if mi.opcode != AArch64Opcode::FmulRR {
                return None;
            }
            if !is_cell(vreg_of(&mi.operands[1])?, &e_key, e_off + 4) {
                return None;
            }
            let (ni, nid) = fp_def(vreg_of(&mi.operands[2])?)?;
            if ni.opcode != AArch64Opcode::FnegRR {
                return None;
            }
            match_diff(vreg_of(&ni.operands[1])?, 4, &mut matched)?;
            matched.insert(mid);
            matched.insert(nid);
        }
        matched.insert(b0id);
        // b4 = Fmadd(er, di, Fmul(ei, dr))
        let (b4i, b4id) = fp_def(b4)?;
        if b4i.opcode != AArch64Opcode::FmaddRR
            || b4i.operands.len() != 4
            || !is_cell(vreg_of(&b4i.operands[1])?, &e_key, e_off)
        {
            return None;
        }
        match_diff(vreg_of(&b4i.operands[2])?, 4, &mut matched)?;
        {
            let (mi, mid) = fp_def(vreg_of(&b4i.operands[3])?)?;
            if mi.opcode != AArch64Opcode::FmulRR
                || !is_cell(vreg_of(&mi.operands[1])?, &e_key, e_off + 4)
            {
                return None;
            }
            match_diff(vreg_of(&mi.operands[2])?, 0, &mut matched)?;
            matched.insert(mid);
        }
        matched.insert(b4id);

        // (R9) COMPLETENESS: every loop instruction is accounted for — a
        // recognized load (of a cell of S1/S2/E at the matched offsets), a
        // matched FP node, one of the four stores, an address-chain member,
        // the induction increment, or the loop control. Anything else BAILS.
        let z_cell_ok = |c: &AddrChain| -> bool {
            let k = c.key();
            ((k == s1_key || k == s2_key) && (c.off == 0 || c.off == 4))
                || (k == e_key && (c.off == e_off || c.off == e_off + 4))
        };
        for &id in &loop_insts {
            if matched.contains(&id) || chain_insts.contains(&id) {
                continue;
            }
            let inst = func.inst(id);
            match inst.opcode {
                AArch64Opcode::LdrRI => {
                    let dst = vreg_of(&inst.operands[0]);
                    let ok = dst
                        .and_then(|d| load_cells.get(&d.id))
                        .map(z_cell_ok)
                        .unwrap_or(false);
                    if !ok {
                        return None;
                    }
                }
                AArch64Opcode::StrRI => {
                    if !stores.iter().any(|(sid, _, _)| *sid == id) {
                        return None;
                    }
                }
                AArch64Opcode::AddRI if id == ivs_def => {}
                AArch64Opcode::CmpRR if id == cmp_id => {}
                AArch64Opcode::BCond if id == bcond_id => {}
                AArch64Opcode::B if id == b_id || id == latch_insts[1] => {}
                AArch64Opcode::MovR | AArch64Opcode::Copy if id == latch_insts[0] => {}
                _ => return None,
            }
        }
        // Every load's VALUE must feed only the matched dag: guaranteed by the
        // completeness of `matched` + the live-out scan below (a load feeding
        // an unmatched consumer leaves that consumer unmatched => bailed).

        // (R10) NO in-loop redefinition of any register treated as invariant
        // (belt-and-braces: [`is_invariant`] already enforced this per leaf).
        let mut invariant_regs: Vec<u32> = vec![bound.id, es.id, e_root.id];
        for r in [&s1, &s2] {
            invariant_regs.push(r.base.id);
            invariant_regs.extend(r.invs.iter().map(|v| v.id));
        }
        for key in [&a_key, &b_key] {
            let rec = &store_recipes[key];
            invariant_regs.push(rec.base.id);
            invariant_regs.extend(rec.invs.iter().map(|v| v.id));
        }
        if invariant_regs.iter().any(|r| loop_defs.contains(r)) {
            return None;
        }

        // (R11) LIVE-OUT scan: no loop-defined value except `ivs` is USED by
        // any instruction outside the loop (`iv` may be REdefined outside —
        // that is a def, not a use). Uses are taken from the shared operand
        // ROLES (tied def-use positions count as uses).
        for (idx, inst) in func.insts.iter().enumerate() {
            let id = InstId(idx as u32);
            if loop_insts.contains(&id) {
                continue;
            }
            // Skip unlinked (removed) instructions.
            if block_of_inst(func, id).is_none() {
                continue;
            }
            let mut bad = false;
            effects::aarch64_for_each_use_position(inst.opcode, inst.operands.len(), |pos| {
                if let Some(MachOperand::VReg(v)) = inst.operands.get(pos)
                    && v.id != ivs.id
                    && loop_defs.contains(&v.id)
                {
                    bad = true;
                }
            });
            if bad {
                return None;
            }
        }

        // (R12) FLAGS: the exit path must redefine NZCV before any read (the
        // vector exit leaves different flags than the scalar exit compare).
        if !flags_reset_before_read(func, exit) {
            return None;
        }

        Some(RecognizedButterfly {
            preheader,
            preheader_term,
            header,
            exit,
            iv,
            ivs,
            bound,
            es,
            s1,
            s2,
            sa: store_recipes[&a_key].clone(),
            sb: store_recipes[&b_key].clone(),
            e_root,
            e_off,
        })
    }
}

/// True iff every path from `from` re-defines the NZCV flags before any
/// instruction reads them (bounded DFS over successors; conservative: an
/// opcode not proven flag-free counts as a reader).
fn flags_reset_before_read(func: &MachFunction, from: BlockId) -> bool {
    let mut visited: HashSet<BlockId> = HashSet::new();
    let mut work = vec![from];
    while let Some(b) = work.pop() {
        if !visited.insert(b) {
            continue;
        }
        let mut resolved = false;
        for &id in &func.block(b).insts {
            let op = func.inst(id).opcode;
            if effects::reads_flags(op) {
                return false;
            }
            if effects::writes_flags(op) {
                resolved = true;
                break;
            }
            if !flag_free(op) {
                return false; // unknown flag behavior: fail closed
            }
        }
        if !resolved {
            let succs = func.block(b).succs.clone();
            if succs.is_empty() {
                continue; // path ends without reading flags
            }
            work.extend(succs);
        }
    }
    true
}

/// Opcodes PROVEN not to read or write NZCV (a conservative allowlist for the
/// exit-path flag walk; anything else is treated as a potential reader).
fn flag_free(op: AArch64Opcode) -> bool {
    use AArch64Opcode::*;
    matches!(
        op,
        AddRR
            | AddRI
            | SubRR
            | SubRI
            | Madd
            | Msub
            | Movz
            | Movk
            | Movn
            | MovR
            | Copy
            | Sxtw
            | Uxtw
            | LslRI
            | LsrRI
            | AsrRI
            | LdrRI
            | StrRI
            | LdrbRI
            | StrbRI
            | LdrhRI
            | StrhRI
            | FaddRR
            | FsubRR
            | FmulRR
            | FdivRR
            | FmaddRR
            | FnegRR
            | B
            | Ret
            | Nop
            | Cbz
            | Cbnz
    )
}

fn iv_def_dominates_preheader(
    func: &MachFunction,
    dom: &DomTree,
    iv: VReg,
    preheader: BlockId,
) -> bool {
    for &block_id in &func.block_order {
        if !dom.dominates(block_id, preheader) {
            continue;
        }
        for &inst_id in &func.block(block_id).insts {
            let inst = func.inst(inst_id);
            if inst.opcode.produces_value()
                && matches!(inst.operands.first(), Some(MachOperand::VReg(v)) if *v == iv)
            {
                return true;
            }
        }
    }
    false
}

// ---------------------------------------------------------------------------
// Lowering
// ---------------------------------------------------------------------------

fn apply_butterfly(func: &mut MachFunction, rec: &RecognizedButterfly) -> bool {
    use AArch64Opcode::*;

    // Range-pair list (store range x other range), lengths chosen below.
    // Streams: A, B (stores, len T8), S1, S2 (reads, len T8), E (reads, 8 B).
    // Pairs: (A,S1) (A,S2) (A,E) (B,S1) (B,S2) (B,E) (A,B) — 7 x 2 blocks.
    const N_PAIRS: usize = 7;

    let g1 = func.create_block();
    let g2 = func.create_block();
    let g3 = func.create_block();
    let av0 = func.create_block();
    let cblocks: Vec<BlockId> = (0..2 * N_PAIRS).map(|_| func.create_block()).collect();
    let vpre = func.create_block();
    let vh = func.create_block();
    let vb = func.create_block();
    let vl = func.create_block();
    let vxe = func.create_block();
    let skip = func.create_block();

    let mut fresh = vec![g1, g2, g3, av0];
    fresh.extend(cblocks.iter().copied());
    fresh.extend([vpre, vh, vb, vl, vxe, skip]);
    insert_new_blocks_before(func, rec.header, &fresh);

    // --- g1/g2: magnitude gates. Any high bit (bit >= 31) in `bound` or `iv`
    // (negative or >= 2^31) routes to the scalar loop — afterwards both are in
    // [0, 2^31) so `T8 = (bound - iv + 1) * 8 < 2^34` computes exactly.
    let hi_j = alloc(func, RegClass::Gpr64);
    emit(func, g1, LsrRI, vec![vreg(hi_j), vreg(rec.bound), imm(31)]);
    emit(func, g1, Cbnz, vec![vreg(hi_j), block(rec.header)]);
    emit(func, g1, B, vec![block(g2)]);
    func.add_edge(g1, rec.header);
    func.add_edge(g1, g2);

    let hi_i = alloc(func, RegClass::Gpr64);
    emit(func, g2, LsrRI, vec![vreg(hi_i), vreg(rec.iv), imm(31)]);
    emit(func, g2, Cbnz, vec![vreg(hi_i), block(rec.header)]);
    emit(func, g2, B, vec![block(g3)]);
    func.add_edge(g2, rec.header);
    func.add_edge(g2, g3);

    // --- g3: trip guard. Vector path needs at least one FULL 2-lane block:
    // `iv < bound` (lanes iv and iv+1 are both iterations the scalar do-while
    // performs). `iv >= bound` (including the impossible-but-unproven
    // single-trip `iv == bound` and empty shapes) => untouched scalar loop.
    emit(func, g3, CmpRR, vec![vreg(rec.iv), vreg(rec.bound)]);
    emit(func, g3, BCond, vec![imm(CC_GE), block(rec.header)]);
    emit(func, g3, B, vec![block(av0)]);
    func.add_edge(g3, rec.header);
    func.add_edge(g3, av0);

    // --- av0: range starts + lengths.
    // T8 = (bound - iv + 1) * 8 — exact (see g1/g2), the byte length of every
    // array range: lane i in [iv, bound] touches [start + (i-iv)*8, +8).
    let t = alloc(func, RegClass::Gpr64);
    emit(
        func,
        av0,
        SubRR,
        vec![vreg(t), vreg(rec.bound), vreg(rec.iv)],
    );
    let t1 = alloc(func, RegClass::Gpr64);
    emit(func, av0, AddRI, vec![vreg(t1), vreg(t), imm(1)]);
    let t8 = alloc(func, RegClass::Gpr64);
    emit(func, av0, LslRI, vec![vreg(t8), vreg(t1), imm(3)]);
    let e8 = alloc(func, RegClass::Gpr64);
    emit(func, av0, Movz, vec![vreg(e8), imm(ELEM_BYTES)]);

    // Range start of an iv-rooted stream at the CURRENT iv (= i0 here):
    // base + Σ inv*8 + iv*8 (mod 2^64 — the same arithmetic the scalar loop's
    // Madd chains perform, so the range is exactly its access set).
    let start_of = |func: &mut MachFunction, blk: BlockId, r: &StreamRecipe| -> VReg {
        let mut cur = r.base;
        for inv in &r.invs {
            let n = alloc(func, RegClass::Gpr64);
            emit(
                func,
                blk,
                Madd,
                vec![vreg(n), vreg(*inv), vreg(rec.es), vreg(cur)],
            );
            cur = n;
        }
        let n = alloc(func, RegClass::Gpr64);
        emit(
            func,
            blk,
            Madd,
            vec![vreg(n), vreg(rec.iv), vreg(rec.es), vreg(cur)],
        );
        n
    };
    let s_a = start_of(func, av0, &rec.sa);
    let s_b = start_of(func, av0, &rec.sb);
    let s_1 = start_of(func, av0, &rec.s1);
    let s_2 = start_of(func, av0, &rec.s2);
    let s_e = if rec.e_off == 0 {
        rec.e_root
    } else {
        let n = alloc(func, RegClass::Gpr64);
        emit(
            func,
            av0,
            AddRI,
            vec![vreg(n), vreg(rec.e_root), imm(rec.e_off)],
        );
        n
    };
    emit(func, av0, B, vec![block(cblocks[0])]);
    func.add_edge(av0, cblocks[0]);

    // --- Disjointness chain. Ranges [x, x+Lx) and [y, y+Ly) (byte sets mod
    // 2^64) are disjoint iff (y-x) >=u Lx AND (x-y) >=u Ly — WRAP-SAFE (the
    // classic modular-interval test; no end-pointer overflow to reason about).
    // A failing sub-test (`<u`, CC_LO) may overlap => the untouched scalar
    // loop; both passing => next pair, the last => the vector preheader.
    let pairs: [(VReg, VReg, VReg, VReg); N_PAIRS] = [
        (s_a, t8, s_1, t8),
        (s_a, t8, s_2, t8),
        (s_a, t8, s_e, e8),
        (s_b, t8, s_1, t8),
        (s_b, t8, s_2, t8),
        (s_b, t8, s_e, e8),
        (s_a, t8, s_b, t8),
    ];
    for (p, (x, lx, y, ly)) in pairs.iter().enumerate() {
        let c1 = cblocks[2 * p];
        let c2 = cblocks[2 * p + 1];
        let next = if p + 1 < N_PAIRS {
            cblocks[2 * p + 2]
        } else {
            vpre
        };
        let d1 = alloc(func, RegClass::Gpr64);
        emit(func, c1, SubRR, vec![vreg(d1), vreg(*y), vreg(*x)]);
        emit(func, c1, CmpRR, vec![vreg(d1), vreg(*lx)]);
        emit(func, c1, BCond, vec![imm(CC_LO), block(rec.header)]);
        emit(func, c1, B, vec![block(c2)]);
        func.add_edge(c1, rec.header);
        func.add_edge(c1, c2);

        let d2 = alloc(func, RegClass::Gpr64);
        emit(func, c2, SubRR, vec![vreg(d2), vreg(*x), vreg(*y)]);
        emit(func, c2, CmpRR, vec![vreg(d2), vreg(*ly)]);
        emit(func, c2, BCond, vec![imm(CC_LO), block(rec.header)]);
        emit(func, c2, B, vec![block(next)]);
        func.add_edge(c2, rec.header);
        func.add_edge(c2, next);
    }

    // --- vpre: hoisted twiddle broadcasts (licensed: E is disjoint from both
    // store ranges, and the scalar loop's first iteration — which runs on
    // every path reaching here, `iv < bound` — performs these exact reads).
    let er = alloc(func, RegClass::Fpr32);
    emit(
        func,
        vpre,
        LdrRI,
        vec![vreg(er), vreg(rec.e_root), imm(rec.e_off)],
    );
    let ei = alloc(func, RegClass::Fpr32);
    emit(
        func,
        vpre,
        LdrRI,
        vec![vreg(ei), vreg(rec.e_root), imm(rec.e_off + 4)],
    );
    let ver = alloc(func, RegClass::Fpr128);
    emit(
        func,
        vpre,
        NeonDupElem,
        vec![vreg(ver), vreg(er), imm(0), imm(ELEM_S)],
    );
    let vei = alloc(func, RegClass::Fpr128);
    emit(
        func,
        vpre,
        NeonDupElem,
        vec![vreg(vei), vreg(ei), imm(0), imm(ELEM_S)],
    );
    // MASK = [0x8000_0000, 0, 0x8000_0000, 0] (.4S view): DUP.2D of the GPR
    // 0x0000_0000_8000_0000 — each 64-bit lane's LOW word is the f32 sign bit.
    let mk16 = alloc(func, RegClass::Gpr64);
    emit(func, vpre, Movz, vec![vreg(mk16), imm(0x8000)]);
    let mk = alloc(func, RegClass::Gpr64);
    emit(func, vpre, LslRI, vec![vreg(mk), vreg(mk16), imm(16)]);
    let vmask = alloc(func, RegClass::Fpr128);
    emit(
        func,
        vpre,
        NeonDupGen,
        vec![vreg(vmask), vreg(mk), imm(ELEM_D)],
    );
    // WALKING POINTERS: each stream's address is materialized ONCE at the
    // entry `iv` (= i0) and then advanced by the POST-INDEX `LD1`/`ST1`
    // (+16 bytes = one complex pair per iteration, exactly `iv += 2` in step —
    // the pointer registers are loop-carried and stay in lock-step with the
    // guard's `iv`). Each stream gets its OWN register: the post-index is a
    // tied use-def, so no chain value is ever reused after being bumped.
    let addr_of = |func: &mut MachFunction, r: &StreamRecipe| -> VReg {
        let mut cur = r.base;
        for inv in &r.invs {
            let n = alloc(func, RegClass::Gpr64);
            emit(
                func,
                vpre,
                Madd,
                vec![vreg(n), vreg(*inv), vreg(rec.es), vreg(cur)],
            );
            cur = n;
        }
        let n = alloc(func, RegClass::Gpr64);
        emit(
            func,
            vpre,
            Madd,
            vec![vreg(n), vreg(rec.iv), vreg(rec.es), vreg(cur)],
        );
        n
    };
    let p1 = addr_of(func, &rec.s1);
    let p2 = addr_of(func, &rec.s2);
    let pa = addr_of(func, &rec.sa);
    let pb = addr_of(func, &rec.sb);
    emit(func, vpre, B, vec![block(vh)]);
    func.add_edge(vpre, vh);

    // --- vh: `iv < bound` (signed; both stay in [0, 2^31+1) on this path)
    // admits lanes {iv, iv+1} — both iterations the scalar do-while performs.
    emit(func, vh, CmpRR, vec![vreg(rec.iv), vreg(rec.bound)]);
    emit(func, vh, BCond, vec![imm(CC_LT), block(vb)]);
    emit(func, vh, B, vec![block(vxe)]);
    func.add_edge(vh, vb);
    func.add_edge(vh, vxe);

    // --- vb: one complex PAIR per iteration on the walking pointers.
    let q1 = alloc(func, RegClass::Fpr128);
    emit(func, vb, NeonLd1Post, vec![vreg(q1), vreg(p1), imm(ARR_S4)]);
    let q2 = alloc(func, RegClass::Fpr128);
    emit(func, vb, NeonLd1Post, vec![vreg(q2), vreg(p2), imm(ARR_S4)]);
    // sum -> A store.
    let vsum = alloc(func, RegClass::Fpr128);
    emit(
        func,
        vb,
        NeonFaddV,
        vec![vreg(vsum), vreg(q1), vreg(q2), imm(FARR_S4)],
    );
    emit(
        func,
        vb,
        NeonSt1Post,
        vec![vreg(vsum), vreg(pa), imm(ARR_S4)],
    );
    // diff, pair-swap, sign-flip (the scalar FNEG on the di lanes), twiddle.
    let vd = alloc(func, RegClass::Fpr128);
    emit(
        func,
        vb,
        NeonFsubV,
        vec![vreg(vd), vreg(q1), vreg(q2), imm(FARR_S4)],
    );
    let vsw = alloc(func, RegClass::Fpr128);
    emit(func, vb, NeonRev64V, vec![vreg(vsw), vreg(vd), imm(ARR_S4)]);
    let vsg = alloc(func, RegClass::Fpr128);
    emit(func, vb, NeonEorV, vec![vreg(vsg), vreg(vsw), vreg(vmask)]);
    let vm = alloc(func, RegClass::Fpr128);
    emit(
        func,
        vb,
        NeonFmulV,
        vec![vreg(vm), vreg(vei), vreg(vsg), imm(FARR_S4)],
    );
    // FMLA is a tied read-modify-write: copy the addend into a fresh Vd.
    let vres = alloc(func, RegClass::Fpr128);
    emit(func, vb, NeonOrrV, vec![vreg(vres), vreg(vm), vreg(vm)]);
    emit(
        func,
        vb,
        NeonFmlaV,
        vec![vreg(vres), vreg(ver), vreg(vd), imm(FARR_S4)],
    );
    emit(
        func,
        vb,
        NeonSt1Post,
        vec![vreg(vres), vreg(pb), imm(ARR_S4)],
    );
    emit(func, vb, B, vec![block(vl)]);
    func.add_edge(vb, vl);

    // --- vl: advance the induction by one complex PAIR.
    emit(func, vl, AddRI, vec![vreg(rec.iv), vreg(rec.iv), imm(2)]);
    emit(func, vl, B, vec![block(vh)]);
    func.add_edge(vl, vh);

    // --- vxe: `iv ∈ {bound, bound+1}` here. `iv == bound` => ONE leftover
    // iteration: fall into the scalar do-while (which also computes the `ivs`
    // live-out). `iv > bound` => all lanes consumed: the do-while must be
    // SKIPPED (it would store one past the end — the remainder-0 class);
    // `skip` materializes the exit live-out `ivs = iv` (= bound+1 — exactly
    // the value the scalar exit computes) and branches to the true exit.
    emit(func, vxe, CmpRR, vec![vreg(rec.iv), vreg(rec.bound)]);
    emit(func, vxe, BCond, vec![imm(CC_GT), block(skip)]);
    emit(func, vxe, B, vec![block(rec.header)]);
    func.add_edge(vxe, skip);
    func.add_edge(vxe, rec.header);

    emit(func, skip, MovR, vec![vreg(rec.ivs), vreg(rec.iv)]);
    emit(func, skip, B, vec![block(rec.exit)]);
    func.add_edge(skip, rec.exit);

    // --- COMMIT: route the preheader into the gate chain.
    if !rewrite_block_target(func.inst_mut(rec.preheader_term), rec.header, g1) {
        return false;
    }
    remove_cfg_edge(func, rec.preheader, rec.header);
    func.add_edge(rec.preheader, g1);

    true
}

// ---------------------------------------------------------------------------
// Small local IR helpers (kept independent of the sibling NEON passes)
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

fn alloc(func: &mut MachFunction, class: RegClass) -> VReg {
    // Allocate a vreg id strictly greater than every id currently in use so we
    // never alias an existing value.
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
            && inst.opcode.produces_value()
        {
            map.insert(v.id, InstId(idx as u32));
        }
    }
    map
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

#[cfg(test)]
mod tests;
