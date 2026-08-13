// trust-cg-opt - AArch64 Extended-Register Addressing Fold
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! AArch64 extended-register addressing fold.
//!
//! A LATE machine pass (after the NEON vectorizers, whose recognizers decode
//! the unfused `Sxtw`/`Madd`/`LdrRI` chain — this pass must never run before
//! them) that folds the 3-instruction scaled-index address derivation the
//! isel emits for `gep ty, ptr, idx` into AArch64's extended-register
//! load/store addressing mode:
//!
//! ```text
//! SXTW Xt, Wi                   ; sign-extend the i32 index
//! MADD Xa, Xt, Xs, Xbase        ; Xs := MOVZ #es (element size)
//! LDR  Wd, [Xa, #0]             ; (or STR / 64-bit / FPR32/FPR64 forms)
//!   =>
//! LDR  Wd, [Xbase, Wi, SXTW #log2(es)]
//! ```
//!
//! and the 64-bit-index variant without the extend:
//!
//! ```text
//! MADD Xa, Xi, Xs, Xbase
//! LDR  Xd, [Xa, #0]
//!   =>
//! LDR  Xd, [Xbase, Xi, LSL #log2(es)]
//! ```
//!
//! It also folds the NARROW register-offset loads (`LdrbRI`/`LdrhRI` =>
//! `LdrbRO`/`LdrhRO`). For a byte gather (`gep i8, ptr, idx`) the scale is 1, so
//! the isel needs no multiply and emits a plain `SXTW/UXTW + ADD` chain (rather
//! than a Movz-scaled `MADD`); this pass folds that too:
//!
//! ```text
//! SXTW Xt, Wi
//! ADD  Xa, Xbase, Xt
//! LDRB Wd, [Xa, #0]
//! UXTB Wd2, Wd            ; redundant — LDRB already zero-extends to 32 bits
//!   =>
//! LDRB Wd2, [Xbase, Wi, SXTW]      ; S=0 (log2(1) = 0)
//! ```
//!
//! The redundant `UXTB`/`UXTH` of a narrow-load result (which already
//! zero-extends into the W register) is folded into the load's destination; a
//! `SXTB`/`SXTH` is a genuine sign change and is left untouched.
//!
//! # Soundness
//!
//! The fold preserves the EXACT address arithmetic:
//! `base + sxtw(w) * es  ==  base + (sxtw(w) << log2(es))  (mod 2^64)`
//! for es in {1, 4, 8} — multiplication by a power of two equals a left
//! shift in wrapping 64-bit arithmetic, and the extended-register mode
//! applies the identical sign/zero-extension of the 32-bit index register
//! (including negative indices). The same identity covers the UXTW and
//! LSL (64-bit index) variants.
//!
//! # Fail-closed constraints
//!
//! - Only `LdrRI`/`StrRI`/`LdrbRI`/`LdrhRI` with **zero** immediate offset are
//!   folded. The full-width `LdrRO`/`StrRO` take their size from the transfer
//!   register class; the narrow `LdrbRO`/`LdrhRO` take their access WIDTH from
//!   the opcode (1/2 bytes), so a narrow load's `access_size` comes from the
//!   opcode, never the transfer class. Byte access uses S=0 (log2(1)=0).
//! - The `Madd`/`Add` address must have exactly one use (the memory base) and
//!   one def; the `Sxtw`/`Uxtw` index extension must have exactly one use (the
//!   `Madd`/`Add`) and one def. Otherwise the chain stays.
//! - The scale must be a whole-function single-def `Movz #es` (the shape
//!   LICM leaves after hoisting), with `es == access_size` (shifted form,
//!   S=1) or `es == 1` (unshifted form, S=0). The `Movz` itself is kept
//!   (it may have other uses; if dead it is one loop-invariant instruction
//!   in the entry block). The plain-`Add` (byte-gather) path has an implicit
//!   `es == 1`, so it always emits the unshifted (S=0) form.
//! - `Sxtw`/`Uxtw`/`Madd`/`Add`/memory op must sit in the SAME block, in order.
//! - Everything else (different scales, SP bases, physical registers,
//!   writeback forms) keeps the original sequence.
//!
//! The rewritten opcodes `LdrRO`/`StrRO` and the narrow `LdrbRO`/`LdrhRO` (with
//! the packed extend/shift 4th operand `(option << 1) | S`) are honestly
//! allowlisted in the coverage gate under the SHARED whole-backend
//! unfaithful-load debt (same reason string as `LdrRO`) — NOT proof-credited.
//! The narrow forms are the new opcodes this pass introduces.

use std::collections::HashMap;

use trust_cg_ir::{
    AArch64Opcode, BlockId, InstId, MachFunction, MachOperand, PassId, ProvenanceMap, RegClass,
    VReg,
};

use crate::dom::DomTree;
use crate::effects::{aarch64_def_operand_positions, aarch64_use_operand_positions};
use crate::loops::LoopAnalysis;
use crate::pass_manager::{AnalysisCache, MachinePass};

/// Packed extend/shift operand values (`(option << 1) | S`), matching the
/// `LdrRO`/`StrRO` encoder contract in trust-cg-codegen.
const OPTION_UXTW: i64 = 0b010;
const OPTION_LSL: i64 = 0b011;
const OPTION_SXTW: i64 = 0b110;

fn pack_extend(option: i64, shifted: bool) -> i64 {
    (option << 1) | (shifted as i64)
}

/// AArch64 extended-register addressing fold pass.
pub struct ExtRegAddrFold;

impl MachinePass for ExtRegAddrFold {
    fn name(&self) -> &str {
        "ext-addr"
    }

    fn run(&mut self, func: &mut MachFunction) -> bool {
        run_ext_addr_fold(func, None)
    }

    fn run_with_provenance(
        &mut self,
        func: &mut MachFunction,
        provenance: &mut ProvenanceMap,
    ) -> bool {
        run_ext_addr_fold(func, Some(provenance))
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

#[derive(Clone, Copy)]
struct InstSite {
    inst_id: InstId,
    block_id: BlockId,
    position: usize,
}

/// A planned fold of one memory access.
struct FoldPlan {
    mem_id: InstId,
    new_opcode: AArch64Opcode,
    base: MachOperand,
    index: MachOperand,
    packed_extend: i64,
    /// The address vreg (the `Madd`/`Add` result) this memory op consumes as
    /// its base. Plans that share an `addr_dst` fold the SAME address chain;
    /// the chain is deleted only when the group holds one plan per use of
    /// `addr_dst` (a read-modify-write / swap has a load AND a store both
    /// consuming it), so a partially-foldable address keeps its chain.
    addr_dst: VReg,
    /// Instructions deleted by the fold (the Madd, plus the Sxtw/Uxtw link
    /// when present).
    dead_chain: Vec<InstId>,
}

fn run_ext_addr_fold(func: &mut MachFunction, mut provenance: Option<&mut ProvenanceMap>) -> bool {
    let use_counts = count_vreg_uses(func);
    let def_counts = count_vreg_defs(func);
    let movz_scales = collect_single_def_movz_scales(func, &def_counts);
    let ext_sites = collect_single_def_ext_sites(func, &def_counts);
    let madd_sites = collect_single_def_madd_sites(func, &def_counts);

    let mut plans: Vec<FoldPlan> = Vec::new();

    let add_sites = collect_single_def_add_sites(func, &def_counts);

    // Dominator tree + loop analysis for the cross-block SEXT-SCALE fold,
    // computed LAZILY together (only when the first cross-block Madd candidate
    // appears) so a function with no such candidate pays nothing.
    let mut domtree: Option<DomTree> = None;
    let mut loops: Option<LoopAnalysis> = None;

    // Kill switch (fail-open to disabled): the cross-block read-modify-write
    // STORE fold — Fold (A). Set `TCG_NO_EXT_ADDR_XBLOCK_STORE` to keep the
    // store's `Madd`/`Str` chain unfolded (leaving only the same-block folds).
    // Fold (A) is OPT-IN (default-off): it is perf-neutral overall and slightly
    // costs memory-bound loops (nsieve-bits) by adding AGU work off the critical
    // path. Enable with TCG_EXT_ADDR_XBLOCK_STORE=1 (do-no-harm default).
    let xblock_store_enabled = crate::env_lock::var_os("TCG_EXT_ADDR_XBLOCK_STORE").is_some();

    // Kill switch (fail-open to enabled) for the SEXT-SCALE lever: the
    // cross-block-capable single-def Madd fold. A scaled-index `Madd` address
    // (`stack[s]` in Towers' Push/Pop/Move) is computed once and reused for a
    // load AND a store in a LATER block; the same-block position helpers cannot
    // see the cross-block uses, so the all-or-nothing grouping drops the whole
    // (partially foldable) chain and the surviving `Madd` later strength-reduces
    // to the standalone `sxtw + add …, lsl #s` clang folds into the addressing
    // mode. When `base` and the index are WHOLE-FUNCTION SINGLE-DEF their values
    // are invariant everywhere their def dominates — and since the mem op uses
    // the `Madd` result, the `Madd` uses base/index, and a single def dominates
    // ALL its uses, that includes every use site of the address — so
    // `[base, index, sxtw/uxtw/lsl #s]` computes the identical effective address
    // at each use with no dominator analysis. Set `TCG_NO_EXT_ADDR_SEXT_SCALE`
    // to keep the chain unfolded (reproduces the pre-lever behavior).
    let sext_scale_enabled = std::env::var_os("TCG_NO_EXT_ADDR_SEXT_SCALE").is_none();

    for block_id in func.block_order.clone() {
        let block_insts = func.block(block_id).insts.clone();
        for (position, &inst_id) in block_insts.iter().enumerate() {
            let inst = func.inst(inst_id);
            // `narrow_size` is `Some(bytes)` for the byte/half loads whose
            // access WIDTH is fixed by the opcode (the transfer register is a
            // W register but the memory access is 1/2 bytes); `None` for the
            // full-width forms whose width comes from the transfer class.
            let (new_opcode, narrow_size): (AArch64Opcode, Option<i64>) = match inst.opcode {
                AArch64Opcode::LdrRI => (AArch64Opcode::LdrRO, None),
                AArch64Opcode::StrRI => (AArch64Opcode::StrRO, None),
                AArch64Opcode::LdrbRI => (AArch64Opcode::LdrbRO, Some(1)),
                AArch64Opcode::LdrhRI => (AArch64Opcode::LdrhRO, Some(2)),
                _ => continue,
            };
            if inst.operands.len() != 3 {
                continue;
            }
            // The memory offset must be exactly 0 (register-offset mode has
            // no additional immediate).
            if inst.operands[2].as_imm() != Some(0) {
                continue;
            }
            let Some(transfer) = inst.operands[0].as_vreg() else {
                continue;
            };
            // Access size: from the OPCODE for the narrow forms, else from the
            // transfer register class (LdrRI/StrRI are full-width only).
            let access_size: i64 = match narrow_size {
                Some(sz) => sz,
                None => match transfer.class {
                    RegClass::Gpr32 | RegClass::Fpr32 => 4,
                    RegClass::Gpr64 | RegClass::Fpr64 => 8,
                    _ => continue,
                },
            };
            // The address register must be a private (single-def) Gpr64. Its
            // use count is NOT bounded here: an address feeding BOTH a load and
            // a store — a swap / read-modify-write, e.g. `perm[j]=perm[m];
            // perm[m]=t` — has two uses. Each foldable use produces its own
            // plan; the Madd/Add (and its Sxtw/Uxtw link) is deleted only when
            // EVERY use folded (checked at apply time: the plan group must hold
            // one plan per use). A use that is not an offset-0 memory op —
            // a non-memory op, an offset-bearing access, or a cross-block use —
            // produces no plan, so the group falls short and the whole chain
            // (and every candidate rewrite consuming it) is left untouched.
            let Some(addr) = inst.operands[1].as_vreg() else {
                continue;
            };
            if addr.class != RegClass::Gpr64 || def_counts.get(&addr).copied().unwrap_or(0) != 1 {
                continue;
            }
            // The address must be a private (one-def one-use) Madd — or, for a
            // scale-1 byte gather, a plain Add — in the SAME block at an earlier
            // position. Variant 1 (Sxtw/Uxtw index) and variant 2 (LSL) share
            // the helpers `try_ext_index_plan` / `lsl_index_plan`.
            let mut plan: Option<FoldPlan> = None;

            // ---- Madd (Movz-scaled) address ----
            if let Some(&madd_site) = madd_sites.get(&addr) {
                // Same-block fast path: the `Madd` sits earlier in THIS block, so
                // the precise position-range redefinition checks apply (and a
                // multi-def base is fine as long as it is not redefined across the
                // straight-line range).
                if madd_site.block_id == block_id && madd_site.position < position {
                    let madd = func.inst(madd_site.inst_id);
                    if madd.operands.len() == 4
                        && let (Some(mul_lhs), Some(mul_rhs), Some(base)) = (
                            madd.operands[1].as_vreg(),
                            madd.operands[2].as_vreg(),
                            madd.operands[3].as_vreg(),
                        )
                        && base.class == RegClass::Gpr64
                        && mul_lhs.class == RegClass::Gpr64
                        && mul_rhs.class == RegClass::Gpr64
                    {
                        // One multiplication operand must be a whole-function
                        // single-def Movz #es; the other is the index.
                        let index_es = match (movz_scales.get(&mul_lhs), movz_scales.get(&mul_rhs))
                        {
                            (_, Some(&es)) => Some((mul_lhs, es)),
                            (Some(&es), _) => Some((mul_rhs, es)),
                            (None, None) => None,
                        };
                        if let Some((index64, es)) = index_es {
                            // Scale legality: es == access size (S=1, shift by
                            // log2) or es == 1 (S=0, unshifted). For a byte access
                            // (size 1) log2 is 0, so the canonical S=0 form is used
                            // even when es == access_size == 1.
                            let scale_ok = es == access_size || es == 1;
                            let shifted = es == access_size && access_size != 1;
                            if scale_ok {
                                plan = try_ext_index_plan(
                                    func,
                                    &block_insts,
                                    block_id,
                                    position,
                                    inst_id,
                                    new_opcode,
                                    base,
                                    index64,
                                    shifted,
                                    madd_site,
                                    &def_counts,
                                    &use_counts,
                                    &ext_sites,
                                )
                                .or_else(|| {
                                    lsl_index_plan(
                                        func,
                                        &block_insts,
                                        position,
                                        inst_id,
                                        new_opcode,
                                        base,
                                        index64,
                                        shifted,
                                        madd_site,
                                    )
                                });
                            }
                        }
                    }
                }

                // Cross-block-capable fallback (the SEXT-SCALE lever): the `Madd`
                // may live in ANOTHER block (its address reused for a later
                // load/store). Gated on WHOLE-FUNCTION single-def base + index
                // (value invariance) plus a dominator-tree availability guard.
                // Only runs when the same-block path did not already claim this
                // mem op, and it picks the SAME variant (Sxtw/Uxtw vs LSL) the
                // same-block path would, so every plan sharing an address stays
                // consistent.
                if plan.is_none() && sext_scale_enabled {
                    if domtree.is_none() {
                        let dt = DomTree::compute(func);
                        loops = Some(LoopAnalysis::compute(func, &dt));
                        domtree = Some(dt);
                    }
                    plan = try_madd_general_plan(
                        func,
                        block_id,
                        inst_id,
                        new_opcode,
                        access_size,
                        madd_site,
                        domtree.as_ref().unwrap(),
                        loops.as_ref().unwrap(),
                        &movz_scales,
                        &def_counts,
                        &use_counts,
                        &ext_sites,
                    );
                }
            }

            // ---- Plain scale-1 Add address (byte gather only) ----
            // A `gep i8, ptr, idx` needs no multiply, so the isel emits
            // `sxtw/uxtw + add` (no Movz-scaled Madd). es == 1 implicitly, so
            // the byte RO load is unshifted (S=0). Either add operand may be
            // the base — addition commutes and the byte shift is 0 — so a
            // private Sxtw/Uxtw on EITHER side becomes the extended index.
            if plan.is_none()
                && narrow_size == Some(1)
                && let Some(&add_site) = add_sites.get(&addr)
                && add_site.block_id == block_id
                && add_site.position < position
            {
                let add = func.inst(add_site.inst_id);
                if add.operands.len() == 3
                    && let (Some(op1), Some(op2)) =
                        (add.operands[1].as_vreg(), add.operands[2].as_vreg())
                    && op1.class == RegClass::Gpr64
                    && op2.class == RegClass::Gpr64
                {
                    plan = try_ext_index_plan(
                        func,
                        &block_insts,
                        block_id,
                        position,
                        inst_id,
                        new_opcode,
                        op2,
                        op1,
                        false,
                        add_site,
                        &def_counts,
                        &use_counts,
                        &ext_sites,
                    )
                    .or_else(|| {
                        try_ext_index_plan(
                            func,
                            &block_insts,
                            block_id,
                            position,
                            inst_id,
                            new_opcode,
                            op1,
                            op2,
                            false,
                            add_site,
                            &def_counts,
                            &use_counts,
                            &ext_sites,
                        )
                    })
                    .or_else(|| {
                        lsl_index_plan(
                            func,
                            &block_insts,
                            position,
                            inst_id,
                            new_opcode,
                            op1,
                            op2,
                            false,
                            add_site,
                        )
                    });
                }
            }

            // ---- Cross-block read-modify-write STORE (Fold A) ----
            // A conditional store back to `base[index]` (the nsieve-bits bit
            // flip / a guarded RMW) sits in a SUCCESSOR block while the shared
            // `Madd` address + sibling load stay in the predecessor. The
            // same-block paths above cannot see it (the Madd is in another
            // block), so the store's use of the address never folds and the
            // whole chain is preserved. When the store's block has the Madd's
            // block as its SOLE predecessor (so the address derivation dominates
            // the store and `base`/`index` provably survive the one edge), plan
            // the `StrRO` fold sharing the load's dead chain. The all-or-nothing
            // grouping below still requires the sibling load to fold too before
            // the shared `Madd`/`ext` is deleted.
            if plan.is_none()
                && xblock_store_enabled
                && new_opcode == AArch64Opcode::StrRO
                && let Some(&madd_site) = madd_sites.get(&addr)
                && madd_site.block_id != block_id
            {
                plan = try_cross_block_store_plan(
                    func,
                    block_id,
                    position,
                    inst_id,
                    new_opcode,
                    addr,
                    access_size,
                    madd_site,
                    &movz_scales,
                    &def_counts,
                    &use_counts,
                    &ext_sites,
                );
            }

            if let Some(plan) = plan {
                plans.push(plan);
            }
        }
    }

    let mut changed = false;

    if !plans.is_empty() {
        // Group plans by the address they consume (`addr_dst`). The address's
        // Madd/Add (and its Sxtw/Uxtw link) may be deleted ONLY when EVERY use
        // of the address folds — i.e. the group holds one plan per use of
        // `addr_dst`. Compare the group size (plans found) to the whole-function
        // use count: equality means all uses are foldable offset-0 memory ops in
        // this block, so the chain is dead once they are rewritten. A shorter
        // group means some use was not folded (a non-memory op, an offset-bearing
        // access, or a cross-block use), and rewriting only SOME uses to the RO
        // form while leaving the Madd/Add live is a pure pessimization — so the
        // ENTIRE group is dropped and the original sequence is preserved.
        //
        // The single-def guard bounds `plan_count <= use_count`; the filter keeps
        // the deterministic block/position plan order (no map iteration).
        let mut plan_count: HashMap<VReg, usize> = HashMap::new();
        for plan in &plans {
            *plan_count.entry(plan.addr_dst).or_insert(0) += 1;
        }
        let applied: Vec<FoldPlan> = plans
            .into_iter()
            .filter(|plan| {
                let uses = use_counts.get(&plan.addr_dst).copied().unwrap_or(0) as usize;
                plan_count.get(&plan.addr_dst).copied().unwrap_or(0) == uses
            })
            .collect();

        let mut to_delete: std::collections::HashSet<InstId> = std::collections::HashSet::new();
        for plan in &applied {
            // Preserve the memory op's source_loc; fall back to the Madd/Add's.
            let fallback_loc = func
                .inst(plan.dead_chain[plan.dead_chain.len() - 1])
                .source_loc;
            let mem = func.inst_mut(plan.mem_id);
            mem.opcode = plan.new_opcode;
            mem.operands = vec![
                mem.operands[0].clone(),
                plan.base.clone(),
                plan.index.clone(),
                MachOperand::Imm(plan.packed_extend),
            ];
            mem.flags = plan.new_opcode.default_flags();
            if mem.source_loc.is_none() {
                mem.source_loc = fallback_loc;
            }
            to_delete.extend(plan.dead_chain.iter().copied());
        }

        if let Some(provenance) = provenance.as_deref_mut() {
            let pass = PassId::new("ext-addr");
            for plan in &applied {
                let mut sources = plan.dead_chain.clone();
                sources.sort_unstable();
                sources.push(plan.mem_id);
                provenance.record_merge(&sources, plan.mem_id, pass.clone());
            }
        }

        if !to_delete.is_empty() {
            for block_id in func.block_order.clone() {
                let block = func.block_mut(block_id);
                block.insts.retain(|id| !to_delete.contains(id));
            }
            changed = true;
        }
    }

    // Second phase: a byte/half load already zero-extends its result into the
    // 32-bit W register, so a following Uxtb/Uxth of that result is the
    // identity. Fold it away (a Sxtb/Sxth is NOT redundant — it changes the
    // sign extension — so it is deliberately left alone by THIS phase, and
    // width-folded into the signed load by the third phase below).
    if fold_redundant_narrow_zext(func, provenance.as_deref_mut()) {
        changed = true;
    }

    // Second-b phase (Fold C): the SAME identity zero-extend, but for the case
    // where the narrow-load result feeds OTHER consumers besides the extend (so
    // the load cannot be redirected). Every use of the extend's destination is
    // rewritten to the load result and the extend is deleted. Kill switch:
    // `TCG_NO_EXT_ADDR_ZEXT_IDENTITY`.
    if std::env::var_os("TCG_NO_EXT_ADDR_ZEXT_IDENTITY").is_none()
        && fold_identity_narrow_zext(func, provenance.as_deref_mut())
    {
        changed = true;
    }

    // Third phase (Fold B): a narrow RI load feeding a single-use SIGN-extend is
    // width-folded into the signed load opcode (`LdrbRI`+`Sxtb` => `LdrsbRI`,
    // `LdrhRI`+`Sxth` => `LdrshRI`). Kill switch: `TCG_NO_EXT_ADDR_NARROW_SEXT`.
    if std::env::var_os("TCG_NO_EXT_ADDR_NARROW_SEXT").is_none()
        && fold_narrow_load_sext(func, provenance)
    {
        changed = true;
    }

    changed
}

/// Variant 1: fold when `index64` is a private (one-def one-use) `Sxtw`/`Uxtw`
/// of a 32-bit index in the SAME block before `addr_site`; the extension is
/// folded into the RO addressing mode's `option`. Returns `None` if the shape
/// does not apply (the caller falls back to `lsl_index_plan`). Also verifies
/// `base` survives from `addr_site` to the memory access.
#[allow(clippy::too_many_arguments)]
fn try_ext_index_plan(
    func: &MachFunction,
    block_insts: &[InstId],
    block_id: BlockId,
    mem_position: usize,
    mem_id: InstId,
    new_opcode: AArch64Opcode,
    base: VReg,
    index64: VReg,
    shifted: bool,
    addr_site: InstSite,
    def_counts: &HashMap<VReg, u32>,
    use_counts: &HashMap<VReg, u32>,
    ext_sites: &HashMap<VReg, InstSite>,
) -> Option<FoldPlan> {
    // The base must not be redefined between the address derivation and the
    // memory access (loop-carried vregs are multi-def; the straight-line range
    // check is the precise guard).
    if defines_in_range(
        func,
        block_insts,
        addr_site.position + 1,
        mem_position,
        base,
    ) {
        return None;
    }
    if def_counts.get(&index64).copied().unwrap_or(0) != 1
        || use_counts.get(&index64).copied().unwrap_or(0) != 1
    {
        return None;
    }
    let &ext_site = ext_sites.get(&index64)?;
    if ext_site.block_id != block_id || ext_site.position >= addr_site.position {
        return None;
    }
    let ext = func.inst(ext_site.inst_id);
    if ext.operands.len() != 2 {
        return None;
    }
    let index32 = ext.operands[1].as_vreg()?;
    if index32.class != RegClass::Gpr32 {
        return None;
    }
    // The 32-bit index must not be redefined between the extension and the
    // memory access.
    if defines_in_range(
        func,
        block_insts,
        ext_site.position + 1,
        mem_position,
        index32,
    ) {
        return None;
    }
    let option = match ext.opcode {
        AArch64Opcode::Sxtw => OPTION_SXTW,
        AArch64Opcode::Uxtw => OPTION_UXTW,
        _ => return None,
    };
    let addr_dst = func.inst(addr_site.inst_id).operands[0].as_vreg()?;
    Some(FoldPlan {
        mem_id,
        new_opcode,
        base: MachOperand::VReg(base),
        index: MachOperand::VReg(index32),
        packed_extend: pack_extend(option, shifted),
        addr_dst,
        dead_chain: vec![ext_site.inst_id, addr_site.inst_id],
    })
}

/// Variant 2: 64-bit index used directly — LSL form. `idx*es == idx <<
/// log2(es)` in wrapping 64-bit arithmetic; for a plain scale-1 `add` the shift
/// is 0. Both `base` and `index64` must survive from `addr_site` to the access.
#[allow(clippy::too_many_arguments)]
fn lsl_index_plan(
    func: &MachFunction,
    block_insts: &[InstId],
    mem_position: usize,
    mem_id: InstId,
    new_opcode: AArch64Opcode,
    base: VReg,
    index64: VReg,
    shifted: bool,
    addr_site: InstSite,
) -> Option<FoldPlan> {
    if defines_in_range(
        func,
        block_insts,
        addr_site.position + 1,
        mem_position,
        base,
    ) {
        return None;
    }
    if defines_in_range(
        func,
        block_insts,
        addr_site.position + 1,
        mem_position,
        index64,
    ) {
        return None;
    }
    let addr_dst = func.inst(addr_site.inst_id).operands[0].as_vreg()?;
    Some(FoldPlan {
        mem_id,
        new_opcode,
        base: MachOperand::VReg(base),
        index: MachOperand::VReg(index64),
        packed_extend: pack_extend(OPTION_LSL, shifted),
        addr_dst,
        dead_chain: vec![addr_site.inst_id],
    })
}

/// The SEXT-SCALE lever: a cross-block-capable `Madd` address fold.
///
/// The same-block helpers above prove `base`/`index` survive to the mem op with a
/// straight-line position-range redefinition scan — which cannot see a use in
/// ANOTHER block. When such an out-of-block use exists (Towers computes
/// `stack[s]` once in the entry block and reuses it for a load AND a store after
/// the if/else), the address's group falls short of its use count and the WHOLE
/// chain is dropped — the surviving `Madd` then strength-reduces to the
/// standalone `sxtw + add …, lsl #s` clang folds into the addressing mode.
///
/// This fallback fires for those uses using WHOLE-FUNCTION single-def as the
/// availability proof: a value with exactly one def is never redefined, and that
/// single def dominates all its uses; since the mem op uses the `Madd` result,
/// the `Madd` uses `base`/`index`, and def-dominates-use is transitive, `base`
/// and `index` are live and UNCHANGED at every use of the address. So
/// `[base, index, sxtw/uxtw/lsl #s]` computes the identical effective address —
/// `base + sxtw(index)·2^s` — with no position scan. A dominator-tree check
/// (`madd_block` dominates the mem op's block) fail-closes defensively on the
/// importer-impossible non-dominating shape, and a store reused INSIDE A LOOP is
/// deferred to the opt-in Fold (A) (the memory-bound do-no-harm boundary).
///
/// It picks the SAME variant the same-block path would, so plans that share an
/// `addr_dst` never disagree on whether the `Sxtw`/`Uxtw` is deleted:
/// - If `index64` is a single-def single-use `Sxtw`/`Uxtw` of a single-def 32-bit
///   index, fold on the 32-bit index and delete the extension + `Madd` (matches
///   the same-block `try_ext_index_plan`). If the extension exists but those
///   preconditions fail, return `None` (fail-closed) — never fall back to the LSL
///   form over the extension's 64-bit result, which a sibling use's ext-variant
///   plan may be deleting.
/// - Otherwise `index64` is used directly (LSL form); it must be single-def so it
///   is available at the mem op. Only the `Madd` is deleted.
#[allow(clippy::too_many_arguments)]
fn try_madd_general_plan(
    func: &MachFunction,
    mem_block: BlockId,
    mem_id: InstId,
    new_opcode: AArch64Opcode,
    access_size: i64,
    madd_site: InstSite,
    dom: &DomTree,
    loops: &LoopAnalysis,
    movz_scales: &HashMap<VReg, i64>,
    def_counts: &HashMap<VReg, u32>,
    use_counts: &HashMap<VReg, u32>,
    ext_sites: &HashMap<VReg, InstSite>,
) -> Option<FoldPlan> {
    // The Madd's block must DOMINATE the mem op's block, so the address
    // derivation runs on every path reaching the mem op and its single-def
    // base/index are always the ones defined here. This fail-closes on the
    // (importer-impossible, but synthetically constructible) non-dominating
    // multi-predecessor shape where the value the mem op reads is not the one
    // this Madd derived — the defensive guard Fold (A) gets from its
    // sole-predecessor test.
    if !dom.dominates(madd_site.block_id, mem_block) {
        return None;
    }
    // Defer a STORE reused INSIDE A LOOP to the opt-in Fold (A): folding a store
    // into RO addressing in a (typically memory-bound) loop adds AGU work off the
    // critical path — the nsieve-bits bit flip / Bubblesort-Perm swap store-back,
    // measured as a small regression, which is exactly why Fold (A) is
    // default-off. A store at an ACYCLIC reuse point (Towers' `stack[s]` across
    // the Push/Pop/Move control flow) is folded by default: deleting the shared
    // Sxtw/Madd chain there is a pure win. Loads are always folded (their address
    // is on the critical path, so RO addressing only helps).
    if new_opcode == AArch64Opcode::StrRO && loops.is_in_loop(mem_block) {
        return None;
    }
    let madd = func.inst(madd_site.inst_id);
    if madd.operands.len() != 4 {
        return None;
    }
    let (Some(mul_lhs), Some(mul_rhs), Some(base)) = (
        madd.operands[1].as_vreg(),
        madd.operands[2].as_vreg(),
        madd.operands[3].as_vreg(),
    ) else {
        return None;
    };
    if base.class != RegClass::Gpr64
        || mul_lhs.class != RegClass::Gpr64
        || mul_rhs.class != RegClass::Gpr64
    {
        return None;
    }
    // `base` single-def: its one def dominates the `Madd` (which uses it), and the
    // `Madd` dominates the mem op (which uses the `Madd` result), so `base` is
    // available and holds the same value at the mem op as at the `Madd`.
    if def_counts.get(&base).copied().unwrap_or(0) != 1 {
        return None;
    }
    // One mul operand is the whole-function single-def `Movz #es` scale; the
    // other is the index. (Same shape as the same-block Madd path.)
    let (index64, es) = match (movz_scales.get(&mul_lhs), movz_scales.get(&mul_rhs)) {
        (_, Some(&es)) => (mul_lhs, es),
        (Some(&es), _) => (mul_rhs, es),
        (None, None) => return None,
    };
    // Scale legality: es == access size (S=1, shift by log2) or es == 1 (S=0).
    if es != access_size && es != 1 {
        return None;
    }
    let shifted = es == access_size && access_size != 1;
    let addr_dst = madd.operands[0].as_vreg()?;

    // Sxtw/Uxtw variant: `index64` is a single-def single-use extension of a
    // single-def 32-bit index. Delete the extension + `Madd`.
    if let Some(&ext_site) = ext_sites.get(&index64) {
        if def_counts.get(&index64).copied().unwrap_or(0) != 1
            || use_counts.get(&index64).copied().unwrap_or(0) != 1
        {
            // The extension exists but the load will NOT delete it — do not fall
            // through to the LSL form over its 64-bit result (a sibling
            // ext-variant plan on the same address may be deleting it).
            return None;
        }
        let ext = func.inst(ext_site.inst_id);
        if ext.operands.len() != 2 {
            return None;
        }
        let index32 = ext.operands[1].as_vreg()?;
        // The 32-bit index must be single-def too, so it is available and
        // unchanged at the (possibly cross-block) mem op.
        if index32.class != RegClass::Gpr32 || def_counts.get(&index32).copied().unwrap_or(0) != 1 {
            return None;
        }
        let option = match ext.opcode {
            AArch64Opcode::Sxtw => OPTION_SXTW,
            AArch64Opcode::Uxtw => OPTION_UXTW,
            _ => return None,
        };
        return Some(FoldPlan {
            mem_id,
            new_opcode,
            base: MachOperand::VReg(base),
            index: MachOperand::VReg(index32),
            packed_extend: pack_extend(option, shifted),
            addr_dst,
            dead_chain: vec![ext_site.inst_id, madd_site.inst_id],
        });
    }

    // LSL variant: the 64-bit index is used directly. It must be single-def so it
    // is available and unchanged at the mem op. Only the `Madd` is deleted.
    if def_counts.get(&index64).copied().unwrap_or(0) != 1 {
        return None;
    }
    Some(FoldPlan {
        mem_id,
        new_opcode,
        base: MachOperand::VReg(base),
        index: MachOperand::VReg(index64),
        packed_extend: pack_extend(OPTION_LSL, shifted),
        addr_dst,
        dead_chain: vec![madd_site.inst_id],
    })
}

/// Fold (A): the cross-block read-modify-write STORE. Plans the `StrRO` fold for
/// a store whose address is a single-def `Madd` in a DIFFERENT block `A` that is
/// the SOLE predecessor of the store's block `B`. Single-predecessor implies `A`
/// dominates `B`, so the address derivation always runs before the store and no
/// other edge can enter `B` to redefine `base`/`index` on an unconsidered path;
/// combined with the redefinition checks across the A-tail (Madd..end of A) and
/// B-head (start of B..store) this proves `base`/`index` hold the same values at
/// the store as at the `Madd`, so `StrRO [base, index, extend]` writes the
/// identical effective address.
///
/// The variant choice MIRRORS the sibling load's (`try_ext_index_plan` then
/// `lsl_index_plan`) so the two plans share the SAME `dead_chain`: when the
/// index's `Sxtw`/`Uxtw` is single-def single-use (the load's variant-1
/// precondition, so the load will delete it) the store MUST also fold on the
/// 32-bit index and fail-closed if it cannot survive to the store — it never
/// falls back to the LSL form over the 64-bit `Uxtw` result whose producer the
/// load is deleting. Otherwise (no extend, or a multi-use extend the load keeps)
/// both fold on the 64-bit index and the extend stays.
#[allow(clippy::too_many_arguments)]
fn try_cross_block_store_plan(
    func: &MachFunction,
    store_block: BlockId,
    store_position: usize,
    store_id: InstId,
    new_opcode: AArch64Opcode,
    addr: VReg,
    access_size: i64,
    madd_site: InstSite,
    movz_scales: &HashMap<VReg, i64>,
    def_counts: &HashMap<VReg, u32>,
    use_counts: &HashMap<VReg, u32>,
    ext_sites: &HashMap<VReg, InstSite>,
) -> Option<FoldPlan> {
    let a_block = madd_site.block_id;
    // B's ONLY predecessor must be A. Every path to the store then runs the
    // address derivation first, and no unconsidered edge can enter B. Multi-pred
    // successors and entry blocks fail closed.
    let preds = &func.block(store_block).preds;
    if preds.len() != 1 || preds[0] != a_block {
        return None;
    }
    let a_insts = &func.block(a_block).insts;
    let b_insts = &func.block(store_block).insts;

    let madd = func.inst(madd_site.inst_id);
    if madd.operands.len() != 4 {
        return None;
    }
    let (Some(mul_lhs), Some(mul_rhs), Some(base)) = (
        madd.operands[1].as_vreg(),
        madd.operands[2].as_vreg(),
        madd.operands[3].as_vreg(),
    ) else {
        return None;
    };
    if base.class != RegClass::Gpr64
        || mul_lhs.class != RegClass::Gpr64
        || mul_rhs.class != RegClass::Gpr64
    {
        return None;
    }
    // One multiplication operand is the whole-function single-def `Movz #es`
    // scale; the other is the index. Same shape as the same-block Madd path.
    let (index64, es) = match (movz_scales.get(&mul_lhs), movz_scales.get(&mul_rhs)) {
        (_, Some(&es)) => (mul_lhs, es),
        (Some(&es), _) => (mul_rhs, es),
        (None, None) => return None,
    };
    // Scale legality: es == access size (S=1, shift by log2) or es == 1 (S=0).
    if es != access_size && es != 1 {
        return None;
    }
    let shifted = es == access_size && access_size != 1;

    // `base` must survive from the Madd to the store: unmodified across the
    // A-tail (Madd+1 .. end of A) AND the B-head (0 .. store).
    if defines_in_range(func, a_insts, madd_site.position + 1, a_insts.len(), base)
        || defines_in_range(func, b_insts, 0, store_position, base)
    {
        return None;
    }

    // Is the index a single-def single-use `Sxtw`/`Uxtw` in A before the Madd?
    // That is exactly the sibling load's variant-1 precondition (the load will
    // delete the extend), so the store MUST fold on the 32-bit index too.
    let ext_deleted = def_counts.get(&index64).copied().unwrap_or(0) == 1
        && use_counts.get(&index64).copied().unwrap_or(0) == 1
        && ext_sites
            .get(&index64)
            .is_some_and(|s| s.block_id == a_block && s.position < madd_site.position);

    if ext_deleted {
        let &ext_site = ext_sites.get(&index64)?;
        let ext = func.inst(ext_site.inst_id);
        if ext.operands.len() != 2 {
            return None;
        }
        let index32 = ext.operands[1].as_vreg()?;
        if index32.class != RegClass::Gpr32 {
            return None;
        }
        let option = match ext.opcode {
            AArch64Opcode::Sxtw => OPTION_SXTW,
            AArch64Opcode::Uxtw => OPTION_UXTW,
            _ => return None,
        };
        // index32 must survive from the extension to the store (A-tail from
        // ext+1, then B-head to the store). If not, fail closed — do NOT fall
        // back to the 64-bit index whose `Uxtw` producer the load is deleting.
        if defines_in_range(func, a_insts, ext_site.position + 1, a_insts.len(), index32)
            || defines_in_range(func, b_insts, 0, store_position, index32)
        {
            return None;
        }
        return Some(FoldPlan {
            mem_id: store_id,
            new_opcode,
            base: MachOperand::VReg(base),
            index: MachOperand::VReg(index32),
            packed_extend: pack_extend(option, shifted),
            addr_dst: addr,
            dead_chain: vec![ext_site.inst_id, madd_site.inst_id],
        });
    }

    // LSL form: the 64-bit index is used directly (no extend deleted). It must
    // survive from the Madd to the store.
    if defines_in_range(
        func,
        a_insts,
        madd_site.position + 1,
        a_insts.len(),
        index64,
    ) || defines_in_range(func, b_insts, 0, store_position, index64)
    {
        return None;
    }
    Some(FoldPlan {
        mem_id: store_id,
        new_opcode,
        base: MachOperand::VReg(base),
        index: MachOperand::VReg(index64),
        packed_extend: pack_extend(OPTION_LSL, shifted),
        addr_dst: addr,
        dead_chain: vec![madd_site.inst_id],
    })
}

/// A byte load (`LdrbRI`/`LdrbRO`) zero-extends its result into all 32 bits of
/// the W transfer register, so a subsequent `Uxtb` of that result is the
/// identity; a halfword load (`LdrhRI`/`LdrhRO`) likewise makes a `Uxth`
/// redundant, and a byte load makes BOTH `Uxtb` and `Uxth` redundant (the high
/// 24/16 bits are already zero). When the load result feeds ONLY such a
/// redundant zero-extend (one def, one use), redirect the load to write the
/// zero-extend's destination and drop the zero-extend. A `Sxtb`/`Sxth` is NOT
/// touched — sign extension is a genuine value change.
fn fold_redundant_narrow_zext(
    func: &mut MachFunction,
    mut provenance: Option<&mut ProvenanceMap>,
) -> bool {
    let def_counts = count_vreg_defs(func);
    let use_counts = count_vreg_uses(func);

    // Map each single-def narrow-load result vreg to (defining load inst, the
    // set of extend widths it makes redundant).
    struct LoadDef {
        load_id: InstId,
        clears_bits_above: u32, // 8 for byte loads, 16 for halfword loads
    }
    let mut load_defs: HashMap<VReg, LoadDef> = HashMap::new();
    for block_id in &func.block_order {
        for &inst_id in &func.block(*block_id).insts {
            let inst = func.inst(inst_id);
            let clears = match inst.opcode {
                AArch64Opcode::LdrbRI | AArch64Opcode::LdrbRO => 8,
                AArch64Opcode::LdrhRI | AArch64Opcode::LdrhRO => 16,
                _ => continue,
            };
            let Some(dst) = inst.operands.first().and_then(|op| op.as_vreg()) else {
                continue;
            };
            if def_counts.get(&dst).copied().unwrap_or(0) == 1 {
                load_defs.insert(
                    dst,
                    LoadDef {
                        load_id: inst_id,
                        clears_bits_above: clears,
                    },
                );
            }
        }
    }

    // Collect redundant zero-extends: (uxt_inst, load_inst, dst).
    let mut redundant: Vec<(InstId, InstId, VReg)> = Vec::new();
    for block_id in &func.block_order {
        for &inst_id in &func.block(*block_id).insts {
            let inst = func.inst(inst_id);
            let width = match inst.opcode {
                AArch64Opcode::Uxtb => 8,
                AArch64Opcode::Uxth => 16,
                _ => continue,
            };
            if inst.operands.len() != 2 {
                continue;
            }
            let (Some(dst), Some(src)) = (inst.operands[0].as_vreg(), inst.operands[1].as_vreg())
            else {
                continue;
            };
            // The zero-extend's destination must have a single def (this
            // instruction) so redirecting the load to write it is safe.
            if def_counts.get(&dst).copied().unwrap_or(0) != 1 {
                continue;
            }
            let Some(load_def) = load_defs.get(&src) else {
                continue;
            };
            // Redundant iff the load already cleared every bit at/above the
            // zero-extend's width, and the load result feeds ONLY this extend.
            if load_def.clears_bits_above <= width
                && use_counts.get(&src).copied().unwrap_or(0) == 1
            {
                redundant.push((inst_id, load_def.load_id, dst));
            }
        }
    }

    if redundant.is_empty() {
        return false;
    }

    let mut to_delete: std::collections::HashSet<InstId> = std::collections::HashSet::new();
    let pass = PassId::new("ext-addr");
    for (uxt_id, load_id, dst) in &redundant {
        // Redirect the load to write the zero-extend's destination directly.
        let uxt_loc = func.inst(*uxt_id).source_loc;
        let load = func.inst_mut(*load_id);
        load.operands[0] = MachOperand::VReg(*dst);
        if load.source_loc.is_none() {
            load.source_loc = uxt_loc;
        }
        to_delete.insert(*uxt_id);
        if let Some(provenance) = provenance.as_deref_mut() {
            provenance.record_merge(&[*uxt_id, *load_id], *load_id, pass.clone());
        }
    }

    for block_id in func.block_order.clone() {
        let block = func.block_mut(block_id);
        block.insts.retain(|id| !to_delete.contains(id));
    }
    true
}

/// Fold (B): a narrow RI load feeding a single-use SIGN-extend is width-folded
/// into the signed load opcode. `LdrbRI` (byte, single def) feeding a single-use
/// `Sxtb`, or `LdrhRI` (halfword) feeding a single-use `Sxth`, is rewritten to
/// the signed load `LdrsbRI`/`LdrshRI` writing the extend's destination
/// directly, and the `Sxt` is deleted:
///
/// ```text
/// LDRB Wt, [Xn, #off]      ; zero-extends the byte into Wt
/// SXTB Xd/Wd, Wt           ; sign-extends the low byte
///   =>
/// LDRSB Xd/Wd, [Xn, #off]  ; loads + sign-extends in one op
/// ```
///
/// This is the exact SIGN dual of `fold_redundant_narrow_zext` (which DROPS a
/// redundant `Uxt` because the load already zero-extends). Here the load does
/// NOT sign-extend, so the fold changes the LOAD OPCODE to perform the sign
/// extension itself. The signed load's extension WIDTH follows the extend's
/// destination class — the `LdrsbRI`/`LdrshRI` encoder derives `opc` from the
/// transfer register (`Gpr64` => sign-extend to 64, `Gpr32` => to 32) — so the
/// result is bit-identical to the deleted `Sxt` for both widths.
///
/// Only the register+IMMEDIATE forms `LdrbRI`/`LdrhRI` are handled: the
/// register-offset `LdrbRO`/`LdrhRO` have no signed sibling opcode
/// (`LdrsbRO`/`LdrshRO` do not exist), so a byte/half GATHER feeding a `Sxt` is
/// left untouched (fail-closed). The `Sxt` width must match the load width
/// (`Sxtb`↔byte, `Sxth`↔halfword) — a mismatched extend is not a plain
/// width-fold and is skipped.
fn fold_narrow_load_sext(
    func: &mut MachFunction,
    mut provenance: Option<&mut ProvenanceMap>,
) -> bool {
    let def_counts = count_vreg_defs(func);
    let use_counts = count_vreg_uses(func);

    // Map each single-def narrow-RI-load result vreg to (load inst, signed
    // opcode, access width in bytes).
    struct LoadDef {
        load_id: InstId,
        signed_opcode: AArch64Opcode,
        width: i64,
    }
    let mut load_defs: HashMap<VReg, LoadDef> = HashMap::new();
    for block_id in &func.block_order {
        for &inst_id in &func.block(*block_id).insts {
            let inst = func.inst(inst_id);
            let (signed_opcode, width) = match inst.opcode {
                AArch64Opcode::LdrbRI => (AArch64Opcode::LdrsbRI, 1),
                AArch64Opcode::LdrhRI => (AArch64Opcode::LdrshRI, 2),
                _ => continue,
            };
            let Some(dst) = inst.operands.first().and_then(|op| op.as_vreg()) else {
                continue;
            };
            if def_counts.get(&dst).copied().unwrap_or(0) == 1 {
                load_defs.insert(
                    dst,
                    LoadDef {
                        load_id: inst_id,
                        signed_opcode,
                        width,
                    },
                );
            }
        }
    }

    // Collect foldable (sxt_inst, load_inst, sxt_dst, signed_opcode) tuples.
    let mut foldable: Vec<(InstId, InstId, VReg, AArch64Opcode)> = Vec::new();
    for block_id in &func.block_order {
        for &inst_id in &func.block(*block_id).insts {
            let inst = func.inst(inst_id);
            let sxt_width = match inst.opcode {
                AArch64Opcode::Sxtb => 1,
                AArch64Opcode::Sxth => 2,
                _ => continue,
            };
            if inst.operands.len() != 2 {
                continue;
            }
            let (Some(dst), Some(src)) = (inst.operands[0].as_vreg(), inst.operands[1].as_vreg())
            else {
                continue;
            };
            // The signed load writes `dst`; it must be a GPR (32 or 64 bit — the
            // encoder picks the sign-extension width) and a single def so
            // redirecting the load to write it is safe.
            if !matches!(dst.class, RegClass::Gpr32 | RegClass::Gpr64)
                || def_counts.get(&dst).copied().unwrap_or(0) != 1
            {
                continue;
            }
            let Some(load_def) = load_defs.get(&src) else {
                continue;
            };
            // The load result must feed ONLY this extend, and the extend width
            // must match the load width (a byte load's bits 31:8 are already
            // zero, so a `Sxth` over it would be an identity, not a sign change).
            if sxt_width == load_def.width && use_counts.get(&src).copied().unwrap_or(0) == 1 {
                foldable.push((inst_id, load_def.load_id, dst, load_def.signed_opcode));
            }
        }
    }

    if foldable.is_empty() {
        return false;
    }

    let mut to_delete: std::collections::HashSet<InstId> = std::collections::HashSet::new();
    let pass = PassId::new("ext-addr");
    for (sxt_id, load_id, dst, signed_opcode) in &foldable {
        let sxt_loc = func.inst(*sxt_id).source_loc;
        let load = func.inst_mut(*load_id);
        load.opcode = *signed_opcode;
        load.operands[0] = MachOperand::VReg(*dst);
        load.flags = signed_opcode.default_flags();
        if load.source_loc.is_none() {
            load.source_loc = sxt_loc;
        }
        to_delete.insert(*sxt_id);
        if let Some(provenance) = provenance.as_deref_mut() {
            provenance.record_merge(&[*sxt_id, *load_id], *load_id, pass.clone());
        }
    }

    for block_id in func.block_order.clone() {
        let block = func.block_mut(block_id);
        block.insts.retain(|id| !to_delete.contains(id));
    }
    true
}

/// Fold (C): a byte load (`LdrbRI`/`LdrbRO`) zero-extends its result into all 32
/// bits of the W register, and a halfword load (`LdrhRI`/`LdrhRO`) clears bits
/// 16+, so a `Uxtb`/`Uxth` of that result is the IDENTITY. Phase 2
/// (`fold_redundant_narrow_zext`) already erases such an extend when the load
/// result feeds ONLY the extend — it does so by redirecting the load to write
/// the extend's destination. This phase handles the COMPLEMENTARY case where the
/// load result ALSO feeds other consumers, so the load cannot be redirected. The
/// exemplar is the hash inner loop `for (; *key; ++key) val = 5*val + *key`,
/// where the byte load feeds BOTH the `*key != 0` guard (`Uxtb`+`Cbnz`) AND the
/// signed-char value (`Sxtb`):
///
/// ```text
/// LDRB Wt, [Xn]        ; Wt already zero-extends the byte into bits 31:8
/// UXTB Wd, Wt          ; Wd = Wt & 0xFF  == Wt  (identity)
/// CBNZ Wd, ...         ; guard consumer of Wd
/// ...
/// SXTB Xv, Wt          ; unrelated signed-value consumer of Wt (untouched)
///   =>
/// LDRB Wt, [Xn]
/// CBNZ Wt, ...         ; every use of Wd rewritten to Wt; UXTB deleted
/// ...
/// SXTB Xv, Wt
/// ```
///
/// SOUND: the load already produced the zero-extended value, so `Wd == Wt` bit
/// for bit; substituting `Wt` for `Wd` at every use is value-preserving. This
/// runs pre-register-allocation on virtual registers, so extending the load
/// result's live range across the extend's former uses is safe. Fail-closed
/// unless: the extend's destination is a single def (this extend), it shares the
/// load result's register class (both `Gpr32`, so the substitution is
/// well-typed), and the load clears every bit at/above the extend width. A
/// `Sxtb`/`Sxth` is untouched (sign extension is a genuine value change). Kill
/// switch: `TCG_NO_EXT_ADDR_ZEXT_IDENTITY`.
fn fold_identity_narrow_zext(
    func: &mut MachFunction,
    provenance: Option<&mut ProvenanceMap>,
) -> bool {
    let def_counts = count_vreg_defs(func);

    // Map each single-def narrow-load result vreg to (load inst, bits cleared
    // above): 8 for byte loads (makes Uxtb — and Uxth — redundant), 16 for
    // halfword loads (makes Uxth redundant).
    struct LoadDef {
        load_id: InstId,
        clears_bits_above: u32,
    }
    let mut load_defs: HashMap<VReg, LoadDef> = HashMap::new();
    for block_id in &func.block_order {
        for &inst_id in &func.block(*block_id).insts {
            let inst = func.inst(inst_id);
            let clears = match inst.opcode {
                AArch64Opcode::LdrbRI | AArch64Opcode::LdrbRO => 8,
                AArch64Opcode::LdrhRI | AArch64Opcode::LdrhRO => 16,
                _ => continue,
            };
            let Some(dst) = inst.operands.first().and_then(|op| op.as_vreg()) else {
                continue;
            };
            if def_counts.get(&dst).copied().unwrap_or(0) == 1 {
                load_defs.insert(
                    dst,
                    LoadDef {
                        load_id: inst_id,
                        clears_bits_above: clears,
                    },
                );
            }
        }
    }

    // Collect identity zero-extends: (uxt_inst, uxt_dst, load_result_src,
    // load_inst), in deterministic block/instruction order.
    let mut identity: Vec<(InstId, VReg, VReg, InstId)> = Vec::new();
    for block_id in &func.block_order {
        for &inst_id in &func.block(*block_id).insts {
            let inst = func.inst(inst_id);
            let width = match inst.opcode {
                AArch64Opcode::Uxtb => 8,
                AArch64Opcode::Uxth => 16,
                _ => continue,
            };
            if inst.operands.len() != 2 {
                continue;
            }
            let (Some(dst), Some(src)) = (inst.operands[0].as_vreg(), inst.operands[1].as_vreg())
            else {
                continue;
            };
            // The extend's destination must have a single def (this extend) so
            // rewriting every use to `src` is total, and must share the load
            // result's register class so the substitution is well-typed.
            if def_counts.get(&dst).copied().unwrap_or(0) != 1 || dst.class != src.class {
                continue;
            }
            let Some(load_def) = load_defs.get(&src) else {
                continue;
            };
            // Redundant iff the load already cleared every bit at/above the
            // extend's width.
            if load_def.clears_bits_above <= width {
                identity.push((inst_id, dst, src, load_def.load_id));
            }
        }
    }

    if identity.is_empty() {
        return false;
    }

    // `dst -> src` substitution for every collected identity extend. Each `dst`
    // is single-def (its extend) and each `src` is a load result (never another
    // collected `dst`, since a `dst` is defined by a Uxt not a load), so the
    // substitutions are independent — one rewrite pass suffices.
    let subst: HashMap<VReg, VReg> = identity
        .iter()
        .map(|&(_, dst, src, _)| (dst, src))
        .collect();
    let delete_ids: std::collections::HashSet<InstId> =
        identity.iter().map(|&(id, ..)| id).collect();

    // Rewrite USE operands equal to any folded `dst` to the load result `src`.
    // Iterating block_order + insts (both deterministic) with a read-only
    // HashMap lookup keeps the rewrite order stable.
    for block_id in func.block_order.clone() {
        for inst_id in func.block(block_id).insts.clone() {
            if delete_ids.contains(&inst_id) {
                continue;
            }
            let inst = func.inst(inst_id);
            let mut rewrites: Vec<(usize, VReg)> = Vec::new();
            for idx in aarch64_use_operand_positions(inst.opcode, inst.operands.len()) {
                if let Some(MachOperand::VReg(v)) = inst.operands.get(idx)
                    && let Some(&new) = subst.get(v)
                {
                    rewrites.push((idx, new));
                }
            }
            if !rewrites.is_empty() {
                let inst = func.inst_mut(inst_id);
                for (idx, new) in rewrites {
                    inst.operands[idx] = MachOperand::VReg(new);
                }
            }
        }
    }

    if let Some(provenance) = provenance {
        let pass = PassId::new("ext-addr");
        // The extend collapses into the load that produced its source; the load
        // remains the surviving representative (unchanged).
        for &(uxt_id, _, _, load_id) in &identity {
            provenance.record_merge(&[uxt_id, load_id], load_id, pass.clone());
        }
    }

    for block_id in func.block_order.clone() {
        let block = func.block_mut(block_id);
        block.insts.retain(|id| !delete_ids.contains(id));
    }
    true
}

// ---------------------------------------------------------------------------
// Analysis helpers
// ---------------------------------------------------------------------------

/// True if any instruction in `block_insts[from..to]` (half-open, positions
/// within the SAME block) defines `vreg`.
fn defines_in_range(
    func: &MachFunction,
    block_insts: &[InstId],
    from: usize,
    to: usize,
    vreg: VReg,
) -> bool {
    block_insts[from..to].iter().any(|&inst_id| {
        let inst = func.inst(inst_id);
        aarch64_def_operand_positions(inst.opcode, inst.operands.len())
            .into_iter()
            .any(|idx| inst.operands.get(idx).and_then(|op| op.as_vreg()) == Some(vreg))
    })
}

fn count_vreg_uses(func: &MachFunction) -> HashMap<VReg, u32> {
    let mut counts: HashMap<VReg, u32> = HashMap::new();
    for block_id in &func.block_order {
        let block = func.block(*block_id);
        for &inst_id in &block.insts {
            let inst = func.inst(inst_id);
            for idx in aarch64_use_operand_positions(inst.opcode, inst.operands.len()) {
                if let Some(MachOperand::VReg(vreg)) = inst.operands.get(idx) {
                    *counts.entry(*vreg).or_insert(0) += 1;
                }
            }
        }
    }
    counts
}

fn count_vreg_defs(func: &MachFunction) -> HashMap<VReg, u32> {
    let mut counts: HashMap<VReg, u32> = HashMap::new();
    for block_id in &func.block_order {
        let block = func.block(*block_id);
        for &inst_id in &block.insts {
            let inst = func.inst(inst_id);
            for idx in aarch64_def_operand_positions(inst.opcode, inst.operands.len()) {
                if let Some(vreg) = inst.operands.get(idx).and_then(|op| op.as_vreg()) {
                    *counts.entry(vreg).or_insert(0) += 1;
                }
            }
        }
    }
    counts
}

/// Whole-function map of single-def `Movz #es` scale constants with
/// es in {1, 2, 4, 8}. The Movz may live in any block (LICM hoists it to
/// the entry block) and may have multiple uses — it is only READ here,
/// never deleted.
fn collect_single_def_movz_scales(
    func: &MachFunction,
    def_counts: &HashMap<VReg, u32>,
) -> HashMap<VReg, i64> {
    let mut scales: HashMap<VReg, i64> = HashMap::new();
    for block_id in &func.block_order {
        let block = func.block(*block_id);
        for &inst_id in &block.insts {
            let inst = func.inst(inst_id);
            if inst.opcode == AArch64Opcode::Movz
                && inst.operands.len() == 2
                && let (Some(dst), Some(imm)) =
                    (inst.operands[0].as_vreg(), inst.operands[1].as_imm())
                && dst.class == RegClass::Gpr64
                && matches!(imm, 1 | 2 | 4 | 8)
                && def_counts.get(&dst).copied().unwrap_or(0) == 1
            {
                scales.insert(dst, imm);
            }
        }
    }
    scales
}

fn collect_single_def_ext_sites(
    func: &MachFunction,
    def_counts: &HashMap<VReg, u32>,
) -> HashMap<VReg, InstSite> {
    let mut sites: HashMap<VReg, InstSite> = HashMap::new();
    for block_id in &func.block_order {
        let block = func.block(*block_id);
        for (position, &inst_id) in block.insts.iter().enumerate() {
            let inst = func.inst(inst_id);
            if matches!(inst.opcode, AArch64Opcode::Sxtw | AArch64Opcode::Uxtw)
                && inst.operands.len() == 2
                && let Some(dst) = inst.operands[0].as_vreg()
                && dst.class == RegClass::Gpr64
                && def_counts.get(&dst).copied().unwrap_or(0) == 1
            {
                sites.insert(
                    dst,
                    InstSite {
                        inst_id,
                        block_id: *block_id,
                        position,
                    },
                );
            }
        }
    }
    sites
}

fn collect_single_def_madd_sites(
    func: &MachFunction,
    def_counts: &HashMap<VReg, u32>,
) -> HashMap<VReg, InstSite> {
    let mut sites: HashMap<VReg, InstSite> = HashMap::new();
    for block_id in &func.block_order {
        let block = func.block(*block_id);
        for (position, &inst_id) in block.insts.iter().enumerate() {
            let inst = func.inst(inst_id);
            if inst.opcode == AArch64Opcode::Madd
                && inst.operands.len() == 4
                && let Some(dst) = inst.operands[0].as_vreg()
                && dst.class == RegClass::Gpr64
                && def_counts.get(&dst).copied().unwrap_or(0) == 1
            {
                sites.insert(
                    dst,
                    InstSite {
                        inst_id,
                        block_id: *block_id,
                        position,
                    },
                );
            }
        }
    }
    sites
}

/// Single-def `AddRR Xd, Xn, Xm` sites — the scale-1 (byte) address derivation
/// the isel emits for `gep i8, ptr, idx` (no Movz-scaled multiply needed). The
/// dst must be a whole-function single def (its value at the load is exactly
/// `Xn + Xm`).
fn collect_single_def_add_sites(
    func: &MachFunction,
    def_counts: &HashMap<VReg, u32>,
) -> HashMap<VReg, InstSite> {
    let mut sites: HashMap<VReg, InstSite> = HashMap::new();
    for block_id in &func.block_order {
        let block = func.block(*block_id);
        for (position, &inst_id) in block.insts.iter().enumerate() {
            let inst = func.inst(inst_id);
            if inst.opcode == AArch64Opcode::AddRR
                && inst.operands.len() == 3
                && let Some(dst) = inst.operands[0].as_vreg()
                && dst.class == RegClass::Gpr64
                && def_counts.get(&dst).copied().unwrap_or(0) == 1
            {
                sites.insert(
                    dst,
                    InstSite {
                        inst_id,
                        block_id: *block_id,
                        position,
                    },
                );
            }
        }
    }
    sites
}

#[cfg(test)]
mod tests;
