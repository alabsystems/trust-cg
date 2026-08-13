// trust-cg-opt - AArch64 Pointer-IV Strength Reduction
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! AArch64 pointer induction-variable strength reduction.
//!
//! A LATE machine pass (after the NEON vectorizers AND after `ext-addr`, whose
//! recognizers must see the unreduced index chains — this pass must never run
//! before them) that rewrites a register-offset array walk inside a
//! conventional (non-SSA, `MovR`-carried) counted loop into a WALKING POINTER:
//!
//! ```text
//! preheader:  movz v94, #0 ; mov v95, v94          ; k = 0
//! header:     mul  v100, v95, v7                    ; k * 8      (v7 = movz #8)
//!             madd v101, v14, v98, v100             ; np*72 + k*8 (invariants)
//!             ldr  d105, [v103, v101]               ; table + np*72 + k*8
//!             add  v163, v95, #1
//!             ...
//! latch:      mov  v95, v163 ; b header
//!   =>
//! preheader:  (clone: mul f1, v95, v7 ; madd f2, v14, v98, f1)
//!             add  t0, v103, f2 ; mov P, t0         ; P = &table[np][k0]
//! header:     ldr  d105, [P, #0]                    ; walking pointer
//! latch:      add  Pn, P, #8 ; mov P, Pn            ; advance by the
//!             mov  v95, v163 ; b header             ; per-iteration stride
//! ```
//!
//! killing BOTH the per-iteration address recompute (the `mul`+`madd` chain
//! becomes dead and is deleted) and the loop-carried pressure on the addressing
//! ALUs (almabench `planetpv`'s k-loops; the same 2D `table + np*stride + k*es`
//! shape `ext_addr` cannot fold because of the loop-invariant `np*stride`
//! addend).
//!
//! # Soundness (telescoping invariant)
//!
//! For each rewritten access the pass proves `INV: P == base + (idx << s)` at
//! every point where `P`, the IV carrier `V`, and the index `idx` are stable:
//!
//! - **Init.** `P0` is computed at the END of the preheader by CLONING the
//!   index chain (fresh destination vregs; `V` and every loop-invariant leaf
//!   referenced directly). The clone reads exactly the values iteration 1's
//!   chain reads: `V`'s only defs are its preheader init (which dominates the
//!   clone) and the latch `MovR` (not on any preheader→header path), and every
//!   leaf is whole-function single-def with its def dominating the preheader.
//!   All cloned opcodes are `Pure` (no traps), so executing them on a
//!   preheader path that bypasses the loop is harmless.
//! - **Step.** The index is proven AFFINE in `V` with a compile-time constant
//!   derivative `a` (strict whitelist below), so one IV step `V += step`
//!   changes the effective address by exactly `C = (a·step) << s` (wrapping
//!   arithmetic distributes). The pass inserts `AddRI`/`SubRI` + an explicit
//!   `MovR` carrier (NOT a writeback form) IMMEDIATELY BEFORE the IV's latch
//!   `MovR V, N` — the only in-loop def of `V` — so every execution of the V
//!   update is paired with exactly one P update and `INV` is preserved even if
//!   the latch executes several times between header visits.
//! - **Use.** The loop shape (below) guarantees the chain, the memory op, and
//!   the IV update relate the SAME iteration's values, so at the access
//!   `base + (idx << s) == P` and `LdrRI/StrRI [P, #0]` computes the identical
//!   effective address.
//!
//! # Fail-closed constraints
//!
//! - Loop shape: an innermost natural loop with a preheader whose body is
//!   EXACTLY `{header}` (rotated self-loop) or `{header, latch}` with the
//!   latch's sole predecessor the header and its only in-body successor the
//!   header (the importer's rotated do-while + copy-latch shape). Exactly one
//!   back-edge. Everything else bails.
//! - IV: a `Gpr64` vreg `V` with EXACTLY two whole-function defs — one whose
//!   block dominates the preheader, and the latch `MovR V, N` — where `N` is
//!   whole-function single-def `AddRI/SubRI N, V, #step` in the header (or in
//!   the latch before the `MovR` for a self-loop).
//! - Access: `LdrRO`/`StrRO` in the HEADER, either the 3-operand plain form
//!   (`[Xn, Xm]`, shift 0) or the 4-operand packed-extend form with the LSL
//!   option only (`S=0`, or `S=1` with the shift implied by the transfer
//!   class). The `SXTW`/`UXTW` options are NEVER touched: a sign/zero-extend
//!   of a loop-variant 32-bit index does not commute with the 64-bit step
//!   (the historic matrix-multiply miscompile), so those accesses are left to
//!   `ext_addr`'s proven forms. For a self-loop the access must precede the
//!   IV's carrier `MovR`.
//! - Index chain: whole-function single-def `Gpr64` instructions in the header
//!   (each def preceding its user), over the strict whitelist `MovR`, `AddRI`,
//!   `SubRI`, `LslRI`, `AddRR`, `SubRR`, `MulRR`, `Madd` — where a multiply
//!   contributes a nonzero derivative only when one factor is a single-def
//!   `Movz` compile-time constant (an invariant×invariant product contributes
//!   zero). Leaves are `V` itself or loop-invariant single-def vregs whose def
//!   dominates the preheader. NOTHING loop-variant is ever traced through a
//!   `Sxtw`/`Uxtw` (not on the whitelist at all).
//! - The byte step `C` must be nonzero and fit the `AddRI`/`SubRI` imm12
//!   encoding (|C| ≤ 4095); the base must be a whole-function single-def
//!   `Gpr64` vreg (never SP) defined outside the loop.
//! - Per-access carriers: every rewritten access gets its OWN walking pointer
//!   (clones of a shared index chain are reused within one loop). The original
//!   chain is deleted only when its results have NO remaining uses.
//! - Profitability gate: an access is rewritten only when its index chain has
//!   ≥ 2 in-loop instructions that all provably DIE with the rewrite — the
//!   recompute-elimination case. An already-optimal register-offset access
//!   (raw-IV index) is never touched: the walking pointer would add carried
//!   pressure for zero per-iteration savings (see
//!   `filter_profitable_plans`).
//!
//! The rewrite emits only already-credited opcodes (`AddRR`, `AddRRShift`,
//! `AddRI`, `SubRI`, `MovR`, `LdrRI`, `StrRI`) — no new emittable surface.
//!
//! # Kill switches
//!
//! Compile-time: set `TCG_NO_PTR_IV_SR` (any value) — [`run`] becomes a no-op.
//! Per-pass bisect: `TRUST_CG_DISABLE_PASSES=ptrivsr`.
//!
//! [`run`]: MachinePass::run

use std::collections::{HashMap, HashSet};

use trust_cg_ir::{
    AArch64Opcode, BlockId, InstId, MachFunction, MachInst, MachOperand, PassId, ProvenanceMap,
    RegClass, VReg,
};

use crate::dom::DomTree;
use crate::loops::{LoopAnalysis, NaturalLoop};
use crate::pass_manager::{AnalysisCache, MachinePass};

/// Packed extend operand values (`(option << 1) | S`) for the LSL option,
/// matching the `LdrRO`/`StrRO` encoder contract in trust-cg-codegen.
const PACKED_LSL_UNSHIFTED: i64 = 0b0110;
const PACKED_LSL_SHIFTED: i64 = 0b0111;

/// Maximum index-chain depth traced by the affine resolver (defense in depth;
/// real chains are 2-4 instructions).
const MAX_CHAIN_DEPTH: u32 = 8;

/// AArch64 pointer induction-variable strength reduction pass.
pub struct PtrIvStrengthReduce;

/// Compile-time kill switch: set `TCG_NO_PTR_IV_SR` (any value) to disable the
/// pass entirely.
fn pass_enabled() -> bool {
    crate::env_lock::var_os("TCG_NO_PTR_IV_SR").is_none()
}

impl MachinePass for PtrIvStrengthReduce {
    fn name(&self) -> &str {
        "ptr-iv-sr"
    }

    fn run(&mut self, func: &mut MachFunction) -> bool {
        run_ptr_iv_sr(func, None)
    }

    fn run_with_provenance(
        &mut self,
        func: &mut MachFunction,
        provenance: &mut ProvenanceMap,
    ) -> bool {
        run_ptr_iv_sr(func, Some(provenance))
    }

    fn run_with_analyses_and_provenance(
        &mut self,
        func: &mut MachFunction,
        _analyses: &mut AnalysisCache,
        provenance: &mut ProvenanceMap,
    ) -> bool {
        self.run_with_provenance(func, provenance)
    }
}

/// A def site: the defining instruction and its location.
#[derive(Clone, Copy)]
struct DefSite {
    inst_id: InstId,
    block_id: BlockId,
    position: usize,
}

/// The recognized loop shape all soundness arguments hang off.
struct LoopShape {
    header: BlockId,
    latch: BlockId,
    preheader: BlockId,
    body: HashSet<BlockId>,
}

/// A recognized conventional induction variable of one loop.
#[derive(Clone, Copy)]
struct IvInfo {
    /// Position of the `MovR V, N` carrier update in the latch.
    movr_pos: usize,
    /// Signed per-iteration step (`AddRI` => +imm, `SubRI` => -imm).
    step: i64,
}

/// Result of the affine resolver: `value == a·V + (loop-invariant part)`.
struct Affine {
    /// Compile-time constant derivative d(value)/d(V).
    a: i64,
    /// The IV the value depends on (`None` while invariant).
    iv: Option<VReg>,
    /// In-loop chain instructions, in dependency order (operands first),
    /// deduplicated. Cloned into the preheader; deleted when dead.
    chain: Vec<InstId>,
}

/// One planned access rewrite.
struct AccessPlan {
    mem_id: InstId,
    new_opcode: AArch64Opcode,
    base: VReg,
    index: VReg,
    /// Left-shift applied to the index by the addressing mode (0 for the
    /// unshifted forms).
    shift: u32,
    iv: VReg,
    /// Byte advance per IV step: `(a·step) << shift`.
    step_bytes: i64,
    chain: Vec<InstId>,
}

fn run_ptr_iv_sr(func: &mut MachFunction, mut provenance: Option<&mut ProvenanceMap>) -> bool {
    if !pass_enabled() {
        return false;
    }
    // Cheap pre-scan: no register-offset access anywhere means nothing to do —
    // skip the dominator/loop analyses entirely (compile-time discipline).
    let has_ro_access = func.block_order.iter().any(|&b| {
        func.block(b).insts.iter().any(|&id| {
            matches!(
                func.inst(id).opcode,
                AArch64Opcode::LdrRO | AArch64Opcode::StrRO
            )
        })
    });
    if !has_ro_access {
        return false;
    }
    let dom = DomTree::compute(func);
    let loops = LoopAnalysis::compute(func, &dom);
    if loops.is_empty() {
        return false;
    }
    // Whole-function def sites. Valid across per-loop applications: rewrites
    // define only FRESH vregs, and dead-chain deletion removes only defs whose
    // vregs have no remaining uses anywhere.
    let def_sites = collect_def_sites(func);

    let mut changed = false;
    // BTreeMap-ordered loop iteration (LoopAnalysis) keeps vreg numbering and
    // emitted bytes deterministic.
    let headers: Vec<BlockId> = loops.all_loops().map(|lp| lp.header).collect();
    for header in headers {
        let lp = loops
            .get_loop(header)
            .expect("header collected from this analysis");
        let Some(shape) = recognize_loop_shape(func, lp) else {
            continue;
        };
        let ivs = find_conventional_ivs(func, &shape, &def_sites, &dom);
        if ivs.is_empty() {
            continue;
        }
        let plans =
            filter_profitable_plans(func, plan_accesses(func, &shape, &ivs, &def_sites, &dom));
        if plans.is_empty() {
            continue;
        }
        apply_plans(func, &shape, &ivs, plans, provenance.as_deref_mut());
        changed = true;
    }
    changed
}

/// Recognize the two supported rotated-loop shapes and their single back-edge.
///
/// Returns `None` (bail) unless:
/// - the loop has a preheader,
/// - the body is `{header}` (self-loop) or `{header, latch}`,
/// - the header's only in-body predecessor is the latch (ONE back-edge),
/// - for the 2-block shape: the latch's sole predecessor is the header (every
///   latch execution directly follows a header execution of the same
///   iteration) and the latch has no in-body successor other than the header
///   (the loop cannot revisit the latch without passing the header).
fn recognize_loop_shape(func: &MachFunction, lp: &NaturalLoop) -> Option<LoopShape> {
    let preheader = lp.preheader?;
    let header = lp.header;
    let latch = lp.latch;
    let body = &lp.body;
    let in_body_header_preds: Vec<BlockId> = func
        .block(header)
        .preds
        .iter()
        .filter(|p| body.contains(p))
        .copied()
        .collect();
    if in_body_header_preds != [latch] {
        return None;
    }
    if header == latch {
        if body.len() != 1 {
            return None;
        }
    } else {
        if body.len() != 2 || !body.contains(&latch) {
            return None;
        }
        if func.block(latch).preds != [header] {
            return None;
        }
        if func
            .block(latch)
            .succs
            .iter()
            .any(|s| body.contains(s) && *s != header)
        {
            return None;
        }
    }
    Some(LoopShape {
        header,
        latch,
        preheader,
        body: body.clone(),
    })
}

/// Find the loop's conventional (copy-carried) induction variables.
///
/// `V` qualifies when it has EXACTLY two whole-function defs — an init whose
/// block dominates the preheader, and a latch `MovR V, N` — with `N` a
/// whole-function single-def `AddRI/SubRI N, V, #step` in the header (or in
/// the latch BEFORE the `MovR` for a self-loop). Then `V` is constant within
/// an iteration and advances by exactly `step` at each latch execution.
fn find_conventional_ivs(
    func: &MachFunction,
    shape: &LoopShape,
    def_sites: &HashMap<VReg, Vec<DefSite>>,
    dom: &DomTree,
) -> HashMap<VReg, IvInfo> {
    let mut ivs: HashMap<VReg, IvInfo> = HashMap::new();
    let latch_insts = &func.block(shape.latch).insts;
    for (movr_pos, &inst_id) in latch_insts.iter().enumerate() {
        let inst = func.inst(inst_id);
        if inst.opcode != AArch64Opcode::MovR || inst.operands.len() != 2 {
            continue;
        }
        let (Some(v), Some(n)) = (inst.operands[0].as_vreg(), inst.operands[1].as_vreg()) else {
            continue;
        };
        if v.class != RegClass::Gpr64 || n.class != RegClass::Gpr64 {
            continue;
        }
        // V: exactly two defs — this MovR plus an init dominating the
        // preheader (hence outside the body).
        let Some(v_defs) = def_sites.get(&v) else {
            continue;
        };
        if v_defs.len() != 2 {
            continue;
        }
        let Some(init) = v_defs.iter().find(|d| d.inst_id != inst_id) else {
            continue;
        };
        if shape.body.contains(&init.block_id) || !dom.dominates(init.block_id, shape.preheader) {
            continue;
        }
        // N: single def, `AddRI/SubRI N, V, #step`, in the header — or, for a
        // self-loop, before the carrier MovR.
        let Some(n_def) = single_def(def_sites, n) else {
            continue;
        };
        if n_def.block_id != shape.header {
            continue;
        }
        if shape.header == shape.latch && n_def.position >= movr_pos {
            continue;
        }
        let n_inst = func.inst(n_def.inst_id);
        let step = match n_inst.opcode {
            AArch64Opcode::AddRI => n_inst.operands.get(2).and_then(|op| op.as_imm()),
            AArch64Opcode::SubRI => n_inst
                .operands
                .get(2)
                .and_then(|op| op.as_imm())
                .map(|imm| -imm),
            _ => None,
        };
        let Some(step) = step else {
            continue;
        };
        if step == 0 || n_inst.operands.len() != 3 || n_inst.operands[1].as_vreg() != Some(v) {
            continue;
        }
        ivs.insert(v, IvInfo { movr_pos, step });
    }
    ivs
}

/// Plan every rewritable `LdrRO`/`StrRO` in the header.
fn plan_accesses(
    func: &MachFunction,
    shape: &LoopShape,
    ivs: &HashMap<VReg, IvInfo>,
    def_sites: &HashMap<VReg, Vec<DefSite>>,
    dom: &DomTree,
) -> Vec<AccessPlan> {
    let mut plans = Vec::new();
    let header_insts = &func.block(shape.header).insts;
    for (position, &inst_id) in header_insts.iter().enumerate() {
        let inst = func.inst(inst_id);
        let new_opcode = match inst.opcode {
            AArch64Opcode::LdrRO => AArch64Opcode::LdrRI,
            AArch64Opcode::StrRO => AArch64Opcode::StrRI,
            _ => continue,
        };
        let Some(transfer) = inst.operands.first().and_then(|op| op.as_vreg()) else {
            continue;
        };
        // Base/index roles and the addressing-mode shift. The 3-operand form
        // is `base + index` (LSL #0) and commutes, so both assignments are
        // tried; the packed 4-operand form is LSL-only (SXTW/UXTW of a
        // loop-variant index NEVER commutes with the 64-bit step — bail).
        let candidates: Vec<(VReg, VReg, u32)> = match inst.operands.len() {
            3 => {
                let (Some(op1), Some(op2)) =
                    (inst.operands[1].as_vreg(), inst.operands[2].as_vreg())
                else {
                    continue;
                };
                vec![(op1, op2, 0), (op2, op1, 0)]
            }
            4 => {
                let (Some(op1), Some(op2), Some(packed)) = (
                    inst.operands[1].as_vreg(),
                    inst.operands[2].as_vreg(),
                    inst.operands[3].as_imm(),
                ) else {
                    continue;
                };
                let shift = match packed {
                    PACKED_LSL_UNSHIFTED => 0,
                    PACKED_LSL_SHIFTED => match transfer.class {
                        RegClass::Gpr32 | RegClass::Fpr32 => 2,
                        RegClass::Gpr64 | RegClass::Fpr64 => 3,
                        _ => continue,
                    },
                    _ => continue,
                };
                vec![(op1, op2, shift)]
            }
            _ => continue,
        };
        for (base, index, shift) in candidates {
            let Some(plan) = try_plan_access(
                func, shape, ivs, def_sites, dom, inst_id, position, new_opcode, base, index, shift,
            ) else {
                continue;
            };
            plans.push(plan);
            break;
        }
    }
    plans
}

/// Try to plan one access with the given base/index role assignment.
#[allow(clippy::too_many_arguments)]
fn try_plan_access(
    func: &MachFunction,
    shape: &LoopShape,
    ivs: &HashMap<VReg, IvInfo>,
    def_sites: &HashMap<VReg, Vec<DefSite>>,
    dom: &DomTree,
    mem_id: InstId,
    mem_position: usize,
    new_opcode: AArch64Opcode,
    base: VReg,
    index: VReg,
    shift: u32,
) -> Option<AccessPlan> {
    // Base: whole-function single-def Gpr64 defined outside the loop, with the
    // def dominating the preheader (available at the P0 computation AND
    // provably loop-invariant).
    if base.class != RegClass::Gpr64 {
        return None;
    }
    let base_def = single_def(def_sites, base)?;
    if shape.body.contains(&base_def.block_id) || !dom.dominates(base_def.block_id, shape.preheader)
    {
        return None;
    }
    // Index: affine in exactly one recognized IV with a nonzero compile-time
    // constant derivative.
    let affine = resolve_affine(
        func,
        shape,
        ivs,
        def_sites,
        dom,
        index,
        mem_position,
        MAX_CHAIN_DEPTH,
    )?;
    let iv = affine.iv?;
    if affine.a == 0 {
        return None;
    }
    let iv_info = ivs[&iv];
    // Self-loop: the access must precede the carrier MovR, so it reads THIS
    // iteration's `P`/`idx` (in the 2-block shape the whole header precedes
    // the latch within the iteration).
    if shape.header == shape.latch && mem_position >= iv_info.movr_pos {
        return None;
    }
    // Byte advance per iteration; must be a nonzero AddRI/SubRI imm12
    // (the i64::MIN guard keeps `.abs()` total).
    let step_bytes = affine.a.wrapping_mul(iv_info.step).wrapping_shl(shift);
    if step_bytes == 0 || step_bytes == i64::MIN || step_bytes.abs() > 4095 {
        return None;
    }
    Some(AccessPlan {
        mem_id,
        new_opcode,
        base,
        index,
        shift,
        iv,
        step_bytes,
        chain: affine.chain,
    })
}

/// Resolve `v` as an affine expression `a·V + invariant` over the strict
/// whitelist, collecting the in-loop chain in dependency order.
///
/// `limit_pos` is the header position of the instruction consuming `v`: every
/// in-loop def must sit strictly before its user, so each value read is the
/// SAME iteration's.
#[allow(clippy::too_many_arguments)]
fn resolve_affine(
    func: &MachFunction,
    shape: &LoopShape,
    ivs: &HashMap<VReg, IvInfo>,
    def_sites: &HashMap<VReg, Vec<DefSite>>,
    dom: &DomTree,
    v: VReg,
    limit_pos: usize,
    depth: u32,
) -> Option<Affine> {
    if v.class != RegClass::Gpr64 {
        return None;
    }
    // Leaf: a recognized IV.
    if ivs.contains_key(&v) {
        return Some(Affine {
            a: 1,
            iv: Some(v),
            chain: Vec::new(),
        });
    }
    let def = single_def(def_sites, v)?;
    // Leaf: loop-invariant, available at the preheader clone point.
    if !shape.body.contains(&def.block_id) {
        if !dom.dominates(def.block_id, shape.preheader) {
            return None;
        }
        return Some(Affine {
            a: 0,
            iv: None,
            chain: Vec::new(),
        });
    }
    // In-loop chain member: single-def in the HEADER, strictly before its
    // user, whitelisted opcode.
    if depth == 0 || def.block_id != shape.header || def.position >= limit_pos {
        return None;
    }
    let inst = func.inst(def.inst_id);
    let resolve_op = |pos: usize| -> Option<Affine> {
        let opv = inst.operands.get(pos)?.as_vreg()?;
        resolve_affine(
            func,
            shape,
            ivs,
            def_sites,
            dom,
            opv,
            def.position,
            depth - 1,
        )
    };
    let combined = match inst.opcode {
        AArch64Opcode::MovR if inst.operands.len() == 2 => resolve_op(1)?,
        AArch64Opcode::AddRI | AArch64Opcode::SubRI if inst.operands.len() == 3 => {
            inst.operands[2].as_imm()?;
            resolve_op(1)?
        }
        AArch64Opcode::LslRI if inst.operands.len() == 3 => {
            let k = inst.operands[2].as_imm()?;
            if !(0..64).contains(&k) {
                return None;
            }
            let r = resolve_op(1)?;
            Affine {
                a: r.a.wrapping_shl(k as u32),
                ..r
            }
        }
        AArch64Opcode::AddRR | AArch64Opcode::SubRR if inst.operands.len() == 3 => {
            let rx = resolve_op(1)?;
            let ry = resolve_op(2)?;
            let iv = merge_iv(rx.iv, ry.iv)?;
            let a = if inst.opcode == AArch64Opcode::AddRR {
                rx.a.wrapping_add(ry.a)
            } else {
                rx.a.wrapping_sub(ry.a)
            };
            Affine {
                a,
                iv,
                chain: concat_chains(rx.chain, ry.chain),
            }
        }
        AArch64Opcode::MulRR if inst.operands.len() == 3 => {
            let rx = resolve_op(1)?;
            let ry = resolve_op(2)?;
            let a = mul_derivative(
                func,
                def_sites,
                &rx,
                inst.operands[1].as_vreg()?,
                &ry,
                inst.operands[2].as_vreg()?,
            )?;
            Affine {
                a,
                iv: merge_iv(rx.iv, ry.iv)?,
                chain: concat_chains(rx.chain, ry.chain),
            }
        }
        AArch64Opcode::Madd if inst.operands.len() == 4 => {
            let r1 = resolve_op(1)?;
            let r2 = resolve_op(2)?;
            let ra = resolve_op(3)?;
            let a_mul = mul_derivative(
                func,
                def_sites,
                &r1,
                inst.operands[1].as_vreg()?,
                &r2,
                inst.operands[2].as_vreg()?,
            )?;
            Affine {
                a: a_mul.wrapping_add(ra.a),
                iv: merge_iv(merge_iv(r1.iv, r2.iv)?, ra.iv)?,
                chain: concat_chains(concat_chains(r1.chain, r2.chain), ra.chain),
            }
        }
        _ => return None,
    };
    let mut chain = combined.chain;
    if !chain.contains(&def.inst_id) {
        chain.push(def.inst_id);
    }
    Some(Affine {
        a: combined.a,
        iv: combined.iv,
        chain,
    })
}

/// Derivative of a product `x·y`: zero when both factors are invariant;
/// `a_x·c` when exactly one factor is affine and the OTHER is a single-def
/// `Movz` compile-time constant. Anything else (two variant factors, or a
/// variant factor scaled by a non-constant invariant) has no compile-time
/// constant derivative — bail.
fn mul_derivative(
    func: &MachFunction,
    def_sites: &HashMap<VReg, Vec<DefSite>>,
    rx: &Affine,
    x: VReg,
    ry: &Affine,
    y: VReg,
) -> Option<i64> {
    match (rx.iv.is_some(), ry.iv.is_some()) {
        (false, false) => Some(0),
        (true, false) => Some(rx.a.wrapping_mul(movz_const(func, def_sites, y)?)),
        (false, true) => Some(ry.a.wrapping_mul(movz_const(func, def_sites, x)?)),
        (true, true) => None,
    }
}

/// The compile-time value of a whole-function single-def `Movz #imm` vreg.
fn movz_const(
    func: &MachFunction,
    def_sites: &HashMap<VReg, Vec<DefSite>>,
    v: VReg,
) -> Option<i64> {
    let def = single_def(def_sites, v)?;
    let inst = func.inst(def.inst_id);
    let (dst, value) = crate::reaching_const::movz_value(inst)?;
    if dst != v {
        return None;
    }
    i64::try_from(value).ok()
}

fn merge_iv(a: Option<VReg>, b: Option<VReg>) -> Option<Option<VReg>> {
    match (a, b) {
        (None, x) | (x, None) => Some(x),
        (Some(x), Some(y)) if x == y => Some(Some(x)),
        _ => None,
    }
}

fn concat_chains(mut a: Vec<InstId>, b: Vec<InstId>) -> Vec<InstId> {
    for id in b {
        if !a.contains(&id) {
            a.push(id);
        }
    }
    a
}

/// Profitability gate (measured, not assumed): keep only plans whose index
/// chain (a) has at least TWO in-loop instructions and (b) becomes provably
/// DEAD once the surviving plans' accesses are rewritten.
///
/// The walking pointer only pays when it DELETES a per-iteration address
/// recompute (almabench's `mul`+`madd` per access). An access whose index is
/// the raw IV (or one cheap op away) is ALREADY optimal in the
/// register-offset addressing mode — rewriting it saves nothing per iteration
/// while adding a loop-carried pointer (+`AddRI`+`MovR` in the latch), which
/// measurably REGRESSES pressure-bound loops (Stanford Perm's recursive swap
/// loop: four carriers live across a recursive call, +7..16%; the Puzzle-Fit
/// lesson from the original diagnosis). A chain kept alive by an external use
/// is the same pure loss, so those plans are dropped too. Iterates because
/// dropping a plan restores its access's index use, which can keep a chain
/// shared with another plan alive.
fn filter_profitable_plans(func: &MachFunction, mut plans: Vec<AccessPlan>) -> Vec<AccessPlan> {
    loop {
        let planned_mems: HashSet<InstId> = plans.iter().map(|p| p.mem_id).collect();
        let chain_set: HashSet<InstId> =
            plans.iter().flat_map(|p| p.chain.iter().copied()).collect();
        // All uses of each vreg: (using inst, operand position).
        let mut uses: HashMap<VReg, Vec<(InstId, usize)>> = HashMap::new();
        for &block_id in &func.block_order {
            for &inst_id in &func.block(block_id).insts {
                let inst = func.inst(inst_id);
                for pos in
                    crate::effects::aarch64_use_operand_positions(inst.opcode, inst.operands.len())
                {
                    if let Some(MachOperand::VReg(v)) = inst.operands.get(pos) {
                        uses.entry(*v).or_default().push((inst_id, pos));
                    }
                }
            }
        }
        // Fixpoint: a chain inst is deadable when every use of its def is
        // either an address operand (position >= 1) of a rewritten access —
        // those operands are REPLACED by the walking pointer — or another
        // deadable chain inst.
        let mut deadable: HashSet<InstId> = HashSet::new();
        loop {
            let mut changed = false;
            for &c in &chain_set {
                if deadable.contains(&c) {
                    continue;
                }
                let inst = func.inst(c);
                let all_dead =
                    crate::effects::aarch64_def_operand_positions(inst.opcode, inst.operands.len())
                        .into_iter()
                        .all(|dpos| {
                            let Some(d) = inst.operands.get(dpos).and_then(|op| op.as_vreg())
                            else {
                                return false;
                            };
                            uses.get(&d).map(Vec::as_slice).unwrap_or(&[]).iter().all(
                                |&(user, pos)| {
                                    deadable.contains(&user)
                                        || (planned_mems.contains(&user) && pos >= 1)
                                },
                            )
                        });
                if all_dead {
                    deadable.insert(c);
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        let before = plans.len();
        plans.retain(|p| p.chain.len() >= 2 && p.chain.iter().all(|id| deadable.contains(id)));
        if plans.len() == before {
            return plans;
        }
    }
}

/// Apply all planned rewrites for one loop, then delete the now-dead index
/// chains.
fn apply_plans(
    func: &mut MachFunction,
    shape: &LoopShape,
    ivs: &HashMap<VReg, IvInfo>,
    plans: Vec<AccessPlan>,
    mut provenance: Option<&mut ProvenanceMap>,
) {
    // Clone each distinct index chain ONCE per loop (accesses often share the
    // index; per-access carriers still get their own pointer).
    let mut clone_cache: HashMap<VReg, VReg> = HashMap::new();
    // Latch insertions accumulate at the IV's carrier MovR; group per IV so
    // positions are computed once against the ORIGINAL latch layout.
    let mut latch_inserts: Vec<(usize, Vec<InstId>)> = Vec::new();
    let pass = PassId::new("ptr-iv-sr");
    let mut all_chains: Vec<InstId> = Vec::new();

    for plan in &plans {
        let mem_loc = func.inst(plan.mem_id).source_loc;
        // ---- Preheader: clone the chain (cached per index vreg) + P0. ----
        let idx_clone = match clone_cache.get(&plan.index) {
            Some(&c) => c,
            None => {
                let c = clone_chain_into_preheader(func, shape, &plan.chain, plan.index, mem_loc);
                clone_cache.insert(plan.index, c);
                c
            }
        };
        let p0 = VReg::new(func.alloc_vreg(), RegClass::Gpr64);
        let p0_inst = if plan.shift == 0 {
            MachInst::new(
                AArch64Opcode::AddRR,
                vec![
                    MachOperand::VReg(p0),
                    MachOperand::VReg(plan.base),
                    MachOperand::VReg(idx_clone),
                ],
            )
        } else {
            MachInst::new(
                AArch64Opcode::AddRRShift,
                vec![
                    MachOperand::VReg(p0),
                    MachOperand::VReg(plan.base),
                    MachOperand::VReg(idx_clone),
                    MachOperand::Imm(plan.shift as i64),
                ],
            )
        };
        let carrier = VReg::new(func.alloc_vreg(), RegClass::Gpr64);
        let carrier_init = MachInst::new(
            AArch64Opcode::MovR,
            vec![MachOperand::VReg(carrier), MachOperand::VReg(p0)],
        );
        insert_before_terminator(func, shape.preheader, vec![p0_inst, carrier_init], mem_loc);

        // ---- Latch: advance the carrier right before the IV's MovR. ----
        let advanced = VReg::new(func.alloc_vreg(), RegClass::Gpr64);
        let (adv_opcode, adv_imm) = if plan.step_bytes >= 0 {
            (AArch64Opcode::AddRI, plan.step_bytes)
        } else {
            (AArch64Opcode::SubRI, -plan.step_bytes)
        };
        let mut adv = MachInst::new(
            adv_opcode,
            vec![
                MachOperand::VReg(advanced),
                MachOperand::VReg(carrier),
                MachOperand::Imm(adv_imm),
            ],
        );
        adv.source_loc = mem_loc;
        let mut carry = MachInst::new(
            AArch64Opcode::MovR,
            vec![MachOperand::VReg(carrier), MachOperand::VReg(advanced)],
        );
        carry.source_loc = mem_loc;
        let adv_id = func.push_inst(adv);
        let carry_id = func.push_inst(carry);
        latch_inserts.push((ivs[&plan.iv].movr_pos, vec![adv_id, carry_id]));

        // ---- Rewrite the access to the walking pointer. ----
        let mem = func.inst_mut(plan.mem_id);
        mem.opcode = plan.new_opcode;
        mem.operands = vec![
            mem.operands[0].clone(),
            MachOperand::VReg(carrier),
            MachOperand::Imm(0),
        ];
        mem.flags = plan.new_opcode.default_flags();

        if let Some(provenance) = provenance.as_deref_mut() {
            // The access is rewritten in place; the chain instructions REMAIN
            // in the stream (deleted below only once provably unused), so they
            // are live sources.
            let mut live = plan.chain.clone();
            live.sort_unstable();
            provenance.record_merge_with_live_sources(
                &[plan.mem_id],
                &live,
                plan.mem_id,
                pass.clone(),
            );
        }
        all_chains.extend(plan.chain.iter().copied());
    }

    // Splice the latch insertions. Sorting by ORIGINAL position (stable) keeps
    // per-IV groups in plan order; inserting from the back keeps earlier
    // positions valid.
    latch_inserts.sort_by_key(|(pos, _)| *pos);
    let latch_block = func.block_mut(shape.latch);
    for (pos, ids) in latch_inserts.into_iter().rev() {
        for id in ids.into_iter().rev() {
            latch_block.insts.insert(pos, id);
        }
    }

    // Delete chain instructions whose results are now unused (all whitelist
    // opcodes are Pure). Fixpoint: deleting a chain tail may free its feeder.
    let mut candidates: Vec<InstId> = Vec::new();
    for id in all_chains {
        if !candidates.contains(&id) {
            candidates.push(id);
        }
    }
    loop {
        let use_counts = count_vreg_uses(func);
        let dead: Vec<InstId> = candidates
            .iter()
            .copied()
            .filter(|&id| {
                let inst = func.inst(id);
                crate::effects::aarch64_def_operand_positions(inst.opcode, inst.operands.len())
                    .into_iter()
                    .all(|pos| {
                        inst.operands
                            .get(pos)
                            .and_then(|op| op.as_vreg())
                            .is_some_and(|d| use_counts.get(&d).copied().unwrap_or(0) == 0)
                    })
            })
            .collect();
        if dead.is_empty() {
            break;
        }
        let dead_set: HashSet<InstId> = dead.iter().copied().collect();
        func.block_mut(shape.header)
            .insts
            .retain(|id| !dead_set.contains(id));
        candidates.retain(|id| !dead_set.contains(id));
    }
}

/// Clone `chain` (dependency-ordered) into the preheader before its
/// terminator, mapping chain-defined vregs to fresh ones and leaving `V` and
/// invariant leaves referenced directly. Returns the clone of `index`.
fn clone_chain_into_preheader(
    func: &mut MachFunction,
    shape: &LoopShape,
    chain: &[InstId],
    index: VReg,
    fallback_loc: Option<trust_cg_ir::SourceLoc>,
) -> VReg {
    if chain.is_empty() {
        // The index IS the IV; its current value at the preheader end is
        // exactly what iteration 1 reads.
        return index;
    }
    let mut mapping: HashMap<VReg, VReg> = HashMap::new();
    let mut clones: Vec<MachInst> = Vec::new();
    for &inst_id in chain {
        let inst = func.inst(inst_id);
        let mut clone = MachInst::new(inst.opcode, inst.operands.clone());
        clone.source_loc = inst.source_loc.or(fallback_loc);
        let def_positions =
            crate::effects::aarch64_def_operand_positions(inst.opcode, inst.operands.len());
        // Map uses through existing clones FIRST, then mint the def's fresh
        // vreg (chain order guarantees operands precede users).
        for (pos, op) in clone.operands.iter_mut().enumerate() {
            if def_positions.contains(&pos) {
                continue;
            }
            if let MachOperand::VReg(v) = op
                && let Some(&mapped) = mapping.get(v)
            {
                *op = MachOperand::VReg(mapped);
            }
        }
        for pos in def_positions {
            if let MachOperand::VReg(d) = clone.operands[pos] {
                let fresh = VReg::new(func.alloc_vreg(), d.class);
                mapping.insert(d, fresh);
                clone.operands[pos] = MachOperand::VReg(fresh);
            }
        }
        clones.push(clone);
    }
    insert_before_terminator(func, shape.preheader, clones, fallback_loc);
    *mapping
        .get(&index)
        .expect("index vreg is defined by the last chain member")
}

/// Append `insts` to `block` immediately before its trailing terminator run
/// (a preheader may end with a `BCond`+`B` pair; the inserted code must
/// execute on the fall-through path to the loop, and — being pure and
/// flag-free — is harmless on any other path).
fn insert_before_terminator(
    func: &mut MachFunction,
    block: BlockId,
    insts: Vec<MachInst>,
    fallback_loc: Option<trust_cg_ir::SourceLoc>,
) {
    let mut ids = Vec::with_capacity(insts.len());
    for mut inst in insts {
        if inst.source_loc.is_none() {
            inst.source_loc = fallback_loc;
        }
        ids.push(func.push_inst(inst));
    }
    let mut at = func.block(block).insts.len();
    while at > 0 {
        let inst = func.inst(func.block(block).insts[at - 1]);
        if !inst.is_terminator() {
            break;
        }
        at -= 1;
    }
    let block = func.block_mut(block);
    for id in ids.into_iter().rev() {
        block.insts.insert(at, id);
    }
}

/// The unique whole-function def site of `v`, or `None` if it has zero or
/// multiple defs.
fn single_def(def_sites: &HashMap<VReg, Vec<DefSite>>, v: VReg) -> Option<DefSite> {
    match def_sites.get(&v)?.as_slice() {
        [d] => Some(*d),
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// Analysis helpers
// ---------------------------------------------------------------------------

fn collect_def_sites(func: &MachFunction) -> HashMap<VReg, Vec<DefSite>> {
    let mut sites: HashMap<VReg, Vec<DefSite>> = HashMap::new();
    for &block_id in &func.block_order {
        for (position, &inst_id) in func.block(block_id).insts.iter().enumerate() {
            let inst = func.inst(inst_id);
            for idx in
                crate::effects::aarch64_def_operand_positions(inst.opcode, inst.operands.len())
            {
                if let Some(vreg) = inst.operands.get(idx).and_then(|op| op.as_vreg()) {
                    sites.entry(vreg).or_default().push(DefSite {
                        inst_id,
                        block_id,
                        position,
                    });
                }
            }
        }
    }
    sites
}

fn count_vreg_uses(func: &MachFunction) -> HashMap<VReg, u32> {
    let mut counts: HashMap<VReg, u32> = HashMap::new();
    for &block_id in &func.block_order {
        for &inst_id in &func.block(block_id).insts {
            let inst = func.inst(inst_id);
            for idx in
                crate::effects::aarch64_use_operand_positions(inst.opcode, inst.operands.len())
            {
                if let Some(MachOperand::VReg(vreg)) = inst.operands.get(idx) {
                    *counts.entry(*vreg).or_insert(0) += 1;
                }
            }
        }
    }
    counts
}

#[cfg(test)]
mod tests;
