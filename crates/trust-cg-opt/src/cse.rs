// trust-cg-opt - Common Subexpression Elimination
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Common Subexpression Elimination (CSE) for machine-level IR.
//!
//! Identifies and eliminates redundant computations: when two instructions
//! compute the same value (same opcode and operands), the second can be
//! replaced with a reference to the first's result.
//!
//! # Safety Requirements
//!
//! **Only Pure instructions are CSE'd.** The memory-effects model in
//! [`crate::effects`] classifies each opcode; only `MemoryEffect::Pure` instructions
//! are candidates. Loads, stores, and calls are never CSE'd because:
//! - Loads may return different values if memory was modified between them.
//! - Stores have side effects.
//! - Calls may have arbitrary side effects.
//!
//! Instructions with implicit physical-register uses or defs are also skipped:
//! those registers are semantic operands, but CSE keys only include explicit
//! operands.
//!
//! Call barriers clear the available-expression table. This prevents CSE from
//! extending a value's live range across ABI clobbers until the backend has a
//! precise value-preservation proof for that shape.
//!
//! **Dominator-based:** An instruction can only be CSE'd if a dominating
//! instruction with the same opcode and operands exists. This prevents
//! using a value from a non-dominating block (which might not have executed).
//!
//! # Commutative Instructions
//!
//! For commutative operations (add, mul, and, or, xor), operands are
//! canonicalized by sorting before hashing. This allows `add v1, v2` to
//! match `add v2, v1`.
//!
//! # Algorithm
//!
//! 1. Compute dominator tree.
//! 2. Walk blocks in dominator-tree preorder (ensures we see dominators first).
//! 3. For each Pure instruction, compute a canonical key (opcode + sorted operands).
//! 4. Look up in the available-expressions table:
//!    - If found AND the available instruction dominates this one, mark for replacement.
//!    - If not found, insert into the table.
//! 5. Apply replacements: rewrite uses of the eliminated instruction's def
//!    to use the original instruction's def.
//!
//! Reference: LLVM `MachineCSE.cpp`, GVN

use std::collections::{HashMap, HashSet};

use trust_cg_ir::{
    AArch64Opcode, BlockId, InstId, MachFunction, MachOperand, OpcodeCategory, PassId,
    ProofAnnotation, ProvenanceMap, RegClass, VReg,
};

use crate::dom::DomTree;
use crate::effects::{
    MemoryEffect, has_tied_def_use, opcode_effect, produces_value, reads_flags, writes_flags,
};
use crate::pass_manager::{AnalysisCache, MachinePass};

/// Common Subexpression Elimination pass.
pub struct CommonSubexprElim;

/// A canonical key for an instruction: (category, opcode, canonicalized operands).
///
/// Uses [`OpcodeCategory`] to group semantically related opcodes, but ALSO
/// includes the target-specific opcode discriminant so that two opcodes in
/// the same category with differing per-operand semantics do NOT collide.
///
/// **Why opcode discriminant matters (issue #432).** Multiple target opcodes
/// can share the same [`OpcodeCategory`] yet interpret their immediate
/// operand differently. For AArch64:
/// - `Movz Xd, #imm16` materializes `+imm16` (zero-extended).
/// - `Movn Xd, #imm16` materializes `~imm16` (bitwise NOT → small negative).
///
/// Both are categorized as [`OpcodeCategory::MovRI`]. Without opcode
/// disambiguation, `Movz #2` (= +2) and `Movn #2` (= -3) produce the same
/// key, and CSE silently collapses them — a soundness bug that miscompiles
/// any function referencing both a small positive and small negative
/// constant whose encoded immediates coincide. Including the opcode in the
/// key keeps category-based filtering (used for the skip checks) while
/// making the hash key precise.
///
/// Instructions whose category is [`OpcodeCategory::Other`] are excluded
/// from CSE because distinct target-specific opcodes may map to `Other`
/// yet have different semantics.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct ExprKey {
    category: OpcodeCategory,
    /// Exact target opcode — distinguishes opcodes that share a category
    /// but have different per-operand semantics (e.g., `Movz` vs `Movn`).
    opcode: AArch64Opcode,
    /// Register class of the produced value. Some opcodes share a mnemonic
    /// and explicit operands across widths, but a GPR32 zero is not
    /// interchangeable with a GPR64 zero in later address arithmetic.
    result_class: RegClass,
    /// Source operands only (excludes the def in operand[0]).
    /// For commutative ops, sorted for canonical form.
    operands: Vec<CanonOperand>,
}

/// A canonicalized operand for hashing purposes.
///
/// VReg operands include a "definition version" to distinguish different
/// definitions of the same virtual register. This is critical for correctness
/// in non-SSA IR: after phi elimination, the same VReg can be defined multiple
/// times (e.g., in phi-resolution copy blocks), and expressions using different
/// definitions of the same VReg must NOT be considered equivalent.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum CanonOperand {
    /// (vreg, definition_version) — version distinguishes multiple defs.
    VReg(VReg, u32),
    Imm(i64),
    FImm(u64), // f64 bits for hashing
    /// Relocation symbol name (globals, TLS, call targets). A symbol is a
    /// link-time constant: two address-materialization pseudos (`Adrp` /
    /// `AddPCRel`) naming the same symbol compute the identical page/offset,
    /// so they are legal CSE keys. Kept distinct from `Other` so that the
    /// unhashable-operand guard below does not reject symbol-bearing keys.
    Symbol(String),
    Other, // non-hashable operands (blocks, etc.)
}

impl CanonOperand {
    /// Create a canonical operand from a MachOperand, using version info
    /// from the vreg_versions map.
    fn from_operand(op: &MachOperand, vreg_versions: &HashMap<VReg, u32>) -> Self {
        match op {
            MachOperand::VReg(v) => {
                let version = vreg_versions.get(v).copied().unwrap_or(0);
                CanonOperand::VReg(*v, version)
            }
            MachOperand::Imm(i) => CanonOperand::Imm(*i),
            MachOperand::FImm(f) => CanonOperand::FImm(f.to_bits()),
            MachOperand::Symbol(s) => CanonOperand::Symbol(s.clone()),
            _ => CanonOperand::Other,
        }
    }
}

/// Entry in the available-expressions table.
#[derive(Debug, Clone)]
struct AvailExpr {
    /// The instruction that first computed this expression.
    inst_id: InstId,
    /// The block containing the instruction.
    block: BlockId,
    /// The VReg defined by the instruction (operand[0]).
    def_vreg: VReg,
}

/// Relocation-pseudo CSE fixpoint (Dhrystone lever): collapse dependent
/// `AddPCRel` pseudos onto a shared `Adrp` leader so a globals-heavy function
/// materializes one base register per global + immediate offsets (clang's x19
/// model) instead of a fresh adrp+add per field access.
///
/// **Default ON** (kill switch: `TCG_ADRP_CSE_FIXPOINT_OFF`). It is SOUND: the
/// latent spill-address miscompile it once exposed (`pr28982b`) was root-caused
/// and FIXED in codegen (pipeline.rs ldp-split + frame.rs fail-closed
/// IP-scratch guard, commit eafc04f1), and gcc-c-torture is clean with it on.
///
/// The earlier net-negative verdict (7b041054, geomean on/off ≈ 1.006) is
/// FALSIFIED on current HEAD: a fresh full-suite sweep measured raw geomean
/// on/off 0.9830 (n=57, corrected ≈ neutral-to-positive), zero stdout
/// mismatches, and CSE-on adds ZERO spills and ZERO extra callee-saved pairs
/// in every function checked across 12 programs — the register-pressure
/// regression thesis does not hold on today's allocator. The surviving
/// "regressions" (sieve 1.19, huffbench 1.04) are instruction-identical code
/// whose delta is a 32-byte fetch-alignment placement artifact, not a codegen
/// quality difference. Reproducible wins banked: Quicksort 0.76–0.81,
/// dry 0.937–0.944, Puzzle 0.945, fbench 0.979, himenobmtxpa 0.979,
/// richards 0.987.
fn reloc_fixpoint_enabled() -> bool {
    std::env::var_os("TCG_ADRP_CSE_FIXPOINT_OFF").is_none()
}

impl MachinePass for CommonSubexprElim {
    fn name(&self) -> &str {
        "cse"
    }

    fn run(&mut self, func: &mut MachFunction) -> bool {
        let dom = DomTree::compute(func);
        run_cse(func, &dom, None, reloc_fixpoint_enabled())
    }

    fn run_with_analyses(&mut self, func: &mut MachFunction, analyses: &mut AnalysisCache) -> bool {
        let dom = analyses.domtree(func).clone();
        run_cse(func, &dom, None, reloc_fixpoint_enabled())
    }

    fn run_with_provenance(
        &mut self,
        func: &mut MachFunction,
        provenance: &mut ProvenanceMap,
    ) -> bool {
        let dom = DomTree::compute(func);
        run_cse(func, &dom, Some(provenance), reloc_fixpoint_enabled())
    }

    fn run_with_analyses_and_provenance(
        &mut self,
        func: &mut MachFunction,
        analyses: &mut AnalysisCache,
        provenance: &mut ProvenanceMap,
    ) -> bool {
        let dom = analyses.domtree(func).clone();
        run_cse(func, &dom, Some(provenance), reloc_fixpoint_enabled())
    }
}

/// Run CSE on the function, returning true if any changes were made.
///
/// `reloc_fixpoint` enables the relocation-pseudo fixpoint (collapse
/// dependent `AddPCRel`s onto a shared `Adrp` leader in a single pass); it is
/// ON in the default pipeline, disabled by the `TCG_ADRP_CSE_FIXPOINT_OFF`
/// kill switch (see [`reloc_fixpoint_enabled`]).
fn run_cse(
    func: &mut MachFunction,
    dom: &DomTree,
    mut provenance: Option<&mut ProvenanceMap>,
    reloc_fixpoint: bool,
) -> bool {
    // Table of available expressions: key -> first occurrence.
    let mut available: HashMap<ExprKey, AvailExpr> = HashMap::new();
    let def_counts = count_defs(func);
    let tied_def_use_vregs = collect_tied_def_use_vregs(func);

    // Relocation-pseudo CSE fixpoint (Dhrystone lever), controlled by the
    // `reloc_fixpoint` parameter. When enabled, an `AddPCRel dst, base, @g`
    // whose `base` (an `Adrp @g`) was itself CSE-eliminated to a dominating
    // leader EARLIER in this same walk is value-numbered as though it already
    // read the leader, so the dependent `AddPCRel` collapses in ONE pass
    // instead of requiring a second CSE run. Globals-heavy code (Dhrystone)
    // materializes a fresh `Adrp`+`AddPCRel` per field access; deduping the
    // `Adrp`s alone leaves the `AddPCRel`s distinct only by their
    // (now-identical) base until a later pass. Default ON; kill switch
    // `TCG_ADRP_CSE_FIXPOINT_OFF` — see [`reloc_fixpoint_enabled`].
    let adrp_cse_fixpoint = reloc_fixpoint;

    // VRegs consumed as the BASE of a GOT/TLVP page-offset load anywhere in
    // the function. An `Adrp` feeding such a load is NOT a plain
    // page-of-symbol value: its RELOCATION KIND is decided at encode time by
    // in-block consumer pairing (`ADR_GOT_PAGE`/`TLVP_PAGE21` vs direct
    // `PAGE21`), and the direct and GOT page values differ (`page(sym)` vs
    // `page(GOT(sym))`). Deduping one across blocks strands the `LdrGot` /
    // `LdrTlvp` without a same-block pairing ADRP (a mixed direct/GOT
    // relocation pair — a wild load; the `try_statx` -O1/-O2 class), and
    // merging a GOT-consumed ADRP with a direct-consumed one gives one of
    // the consumers the wrong page value outright. Exclude them from CSE.
    let got_page_base_vregs: std::collections::HashSet<VReg> = {
        let mut bases = std::collections::HashSet::new();
        for block_id in func.block_order.clone() {
            for &inst_id in &func.block(block_id).insts {
                let inst = func.inst(inst_id);
                if matches!(
                    inst.opcode,
                    AArch64Opcode::LdrGot | AArch64Opcode::LdrTlvp | AArch64Opcode::LdrGottprel
                ) && let Some(MachOperand::VReg(base)) = inst.operands.get(1)
                {
                    bases.insert(*base);
                }
            }
        }
        bases
    };

    // Replacement map: (vreg, def_version) of eliminated def -> vreg of
    // original def. The version is required because this IR is not SSA:
    // the same VReg may be redefined later, and only uses of the specific
    // eliminated definition are safe to rewrite.
    let mut replacements: HashMap<(VReg, u32), VReg> = HashMap::new();

    // Instructions to remove (marked dead).
    let mut dead_insts: Vec<InstId> = Vec::new();

    // Proof annotations to merge onto surviving instructions.
    // Maps surviving inst_id -> proof from eliminated duplicate.
    let mut proof_merges: Vec<(InstId, Option<ProofAnnotation>)> = Vec::new();

    // Provenance merges from eliminated duplicate instructions onto their
    // available-expression leader.
    let mut provenance_merges: Vec<(InstId, InstId)> = Vec::new();

    // VReg definition versions: tracks how many times each VReg has been
    // defined so far. This is critical for correctness in non-SSA IR:
    // after phi elimination, the same VReg can be defined multiple times
    // (e.g., `v20 = mov v21; v21 = mov v23` in phi-resolution blocks).
    // Expressions using different definitions of the same VReg must get
    // different keys to prevent unsound CSE.
    let mut vreg_versions: HashMap<VReg, u32> = HashMap::new();

    // Walk in dominator-tree preorder to see definitions before uses.
    let preorder = dom_preorder(dom, func.entry);

    for &block_id in &preorder {
        let block = func.block(block_id);
        for &inst_id in &block.insts {
            let inst = func.inst(inst_id);

            // Track VReg definitions: increment version for each def.
            // This must happen for ALL instructions (not just CSE candidates)
            // so that subsequent expressions using redefined VRegs get new keys.
            let def_version = if produces_value(inst.opcode) {
                if let Some(MachOperand::VReg(def_v)) = inst.operands.first() {
                    let ver = vreg_versions.entry(*def_v).or_insert(0);
                    *ver += 1;
                    Some(*ver)
                } else {
                    None
                }
            } else {
                None
            };

            let effect = opcode_effect(inst.opcode);
            if effect.is_barrier() || !inst.implicit_defs.is_empty() {
                available.clear();
            }

            // Only CSE pure instructions that produce a value.
            if effect != MemoryEffect::Pure {
                continue;
            }
            if !produces_value(inst.opcode) {
                continue;
            }

            // Implicit physical registers are semantic operands/clobbers
            // outside the explicit operand list used for CSE keys. Until the
            // key models them precisely, merging these instructions can
            // silently drop a fixed-register dependency.
            if !inst.implicit_defs.is_empty() || !inst.implicit_uses.is_empty() {
                continue;
            }

            // Skip instructions that read or write implicit NZCV flags.
            // Flag readers depend on state not captured in explicit operands;
            // flag writers have an observable side effect for the next reader.
            // Eliminating a duplicate ADDS/SUBS would preserve the arithmetic
            // value but leave a following overflow branch reading stale flags.
            if reads_flags(inst.opcode) || writes_flags(inst.opcode) {
                continue;
            }
            if has_tied_def_use(inst.opcode) {
                continue;
            }

            // Categorize the opcode for the CSE key. Instructions that
            // map to OpcodeCategory::Other are target-specific opcodes
            // without a generic category — different opcodes may map to
            // Other yet have different semantics, so we skip them.
            let category = inst.opcode.categorize();
            // `Adrp` and `AddPCRel` categorize as `Other` (they are
            // target-specific relocation pseudos with no generic category),
            // but they ARE sound and highly profitable CSE candidates: each is
            // pure, deterministic, and its only source operand is a
            // link-time-constant `Symbol`, so two of them naming the same
            // symbol compute the identical page/offset regardless of the
            // instruction's own PC (the PAGE21/PAGEOFF12 relocation is
            // re-resolved at link time). Bypass the generic `Other` gate for
            // EXACTLY these two opcodes — NOT generically: other
            // `Other`-category opcodes stay excluded (e.g. `Bl`, whose `Symbol`
            // names a *call target* with arbitrary side effects). This is the
            // ADRP-DEDUP win: it collapses the redundant in-loop/in-block
            // global-address materialization that dominates globals-heavy code
            // (Towers, Bubblesort) within the existing dominance/purity/
            // versioning framework, adding zero new analysis.
            let is_dedupable_relocation_address =
                matches!(inst.opcode, AArch64Opcode::Adrp | AArch64Opcode::AddPCRel)
                    && !(inst.opcode == AArch64Opcode::Adrp
                        && inst
                            .operands
                            .first()
                            .and_then(|op| op.as_vreg())
                            .is_some_and(|def| got_page_base_vregs.contains(&def)));
            if category == OpcodeCategory::Other && !is_dedupable_relocation_address {
                continue;
            }

            // Get the def vreg (operand[0]).
            let def_vreg = match &inst.operands.first() {
                Some(MachOperand::VReg(v)) => *v,
                _ => continue,
            };
            if tied_def_use_vregs.contains(&def_vreg) {
                continue;
            }
            let def_version = match def_version {
                Some(version) => version,
                None => continue,
            };
            if has_multi_def(def_vreg, &def_counts) {
                continue;
            }
            if has_multi_def_vreg_operand(&inst.operands[1..], &def_counts) {
                continue;
            }

            // Build canonical key from category, opcode, and source operands,
            // including VReg definition versions to distinguish different
            // definitions. The opcode is part of the key so that two opcodes
            // sharing a category but with different per-operand semantics
            // (e.g., `Movz` vs `Movn` in `MovRI`) do not collide — see #432.
            //
            // For the relocation address pseudos ONLY, thread the in-progress
            // replacement map so a source `Adrp` already merged to a leader is
            // value-numbered as the leader (the AddPCRel-fixpoint lever). This
            // is bounded to `Adrp`/`AddPCRel` (`is_dedupable_relocation_address`)
            // to keep other CSE value-numbering unchanged: the apply phase
            // rewrites the operand to exactly this leader, so keying on the
            // leader matches the instruction's post-rewrite form.
            let reloc_leaders = if adrp_cse_fixpoint && is_dedupable_relocation_address {
                Some(&replacements)
            } else {
                None
            };
            let key = make_expr_key(
                category,
                inst.opcode,
                def_vreg.class,
                inst.opcode.is_commutative(),
                &inst.operands,
                &vreg_versions,
                reloc_leaders,
            );

            // Check if we have a key with "Other" operands — skip those
            // as they're not reliably hashable.
            if key
                .operands
                .iter()
                .any(|o| matches!(o, CanonOperand::Other))
            {
                continue;
            }

            // Look up in available expressions.
            if let Some(avail) = available.get(&key) {
                if has_multi_def(avail.def_vreg, &def_counts) {
                    continue;
                }

                // Verify dominance: the available instruction's block must
                // dominate the current block.
                if dom.dominates(avail.block, block_id) {
                    // CSE: replace all uses of def_vreg with avail.def_vreg.
                    replacements.insert((def_vreg, def_version), avail.def_vreg);
                    dead_insts.push(inst_id);

                    // Merge proof annotation from eliminated instruction
                    // onto the surviving one.
                    let eliminated_proof = inst.proof;
                    proof_merges.push((avail.inst_id, eliminated_proof));
                    provenance_merges.push((avail.inst_id, inst_id));
                    continue;
                }
                // If the available doesn't dominate, we could update the table
                // if WE dominate it, but that's complex. Keep it simple:
                // first-in-preorder wins.
            }

            // Insert into available expressions table.
            available.insert(
                key,
                AvailExpr {
                    inst_id,
                    block: block_id,
                    def_vreg,
                },
            );
        }
    }

    if replacements.is_empty() {
        return false;
    }

    // Apply proof merges: for each surviving instruction, merge in the
    // proof annotation from the eliminated duplicate.
    for (surviving_id, eliminated_proof) in proof_merges {
        let surviving = func.inst_mut(surviving_id);
        surviving.proof = ProofAnnotation::merge(surviving.proof, eliminated_proof);
    }

    if let Some(provenance) = provenance.as_deref_mut() {
        let pass = PassId::new("cse");
        for (surviving_id, eliminated_id) in &provenance_merges {
            provenance.record_merge(
                &[*surviving_id, *eliminated_id],
                *surviving_id,
                pass.clone(),
            );
        }
    }

    // Apply replacements: rewrite uses in the same dominator-preorder used
    // to build versioned CSE keys, so each use sees the matching definition
    // version for its VReg operands.
    let mut rewrite_versions: HashMap<VReg, u32> = HashMap::new();
    let mut rewritten_inst_ids: HashSet<InstId> = HashSet::new();
    for &block_id in &preorder {
        let inst_ids = func.block(block_id).insts.clone();
        for inst_id in inst_ids {
            let inst = func.inst_mut(inst_id);
            let use_start = if produces_value(inst.opcode) { 1 } else { 0 };
            let mut rewritten = false;

            for i in use_start..inst.operands.len() {
                let vreg = match &inst.operands[i] {
                    MachOperand::VReg(vreg) => *vreg,
                    _ => continue,
                };
                let version = rewrite_versions.get(&vreg).copied().unwrap_or(0);
                if let Some(replacement) = replacements.get(&(vreg, version)) {
                    inst.operands[i] = MachOperand::VReg(*replacement);
                    rewritten = true;
                }
            }

            if rewritten {
                rewritten_inst_ids.insert(inst_id);
            }

            if produces_value(inst.opcode)
                && let Some(MachOperand::VReg(def_v)) = inst.operands.first()
            {
                let ver = rewrite_versions.entry(*def_v).or_insert(0);
                *ver += 1;
            }
        }
    }

    if let Some(provenance) = provenance {
        let pass = PassId::new("cse");
        for inst_id in rewritten_inst_ids {
            if !provenance_merges
                .iter()
                .any(|(surviving_id, eliminated_id)| {
                    *surviving_id == inst_id || *eliminated_id == inst_id
                })
            {
                provenance.record_in_place_transform(inst_id, pass.clone());
            }
        }
    }

    // Remove dead instructions.
    let dead_set: std::collections::HashSet<InstId> = dead_insts.into_iter().collect();
    for block_id in func.block_order.clone() {
        let block = func.block_mut(block_id);
        block.insts.retain(|id| !dead_set.contains(id));
    }

    true
}

/// Build a canonical expression key for an instruction.
///
/// The key consists of the [`OpcodeCategory`], the exact target opcode, and
/// the source operands (excluding the def in operand[0]). For commutative
/// operations, source operands are sorted to produce a canonical form.
///
/// [`OpcodeCategory`] remains in the key so that the generic skip checks
/// (`category == Other`) and any future cross-target reasoning stay meaningful.
/// The [`AArch64Opcode`] discriminant is included so that opcodes which share
/// a category but interpret their operands differently do NOT collide. For
/// example, `Movz` (materializes `+imm`) and `Movn` (materializes `~imm`)
/// both categorize as [`OpcodeCategory::MovRI`] but have divergent semantics
/// for the same immediate value — see issue #432.
///
/// VReg operands include their current definition version from
/// `vreg_versions`, ensuring that expressions using different definitions
/// of the same VReg are not considered equivalent.
fn make_expr_key(
    category: OpcodeCategory,
    opcode: AArch64Opcode,
    result_class: RegClass,
    is_commutative: bool,
    operands: &[MachOperand],
    vreg_versions: &HashMap<VReg, u32>,
    reloc_leaders: Option<&HashMap<(VReg, u32), VReg>>,
) -> ExprKey {
    // Source operands start at index 1 (operand[0] is the def).
    let mut canon_ops: Vec<CanonOperand> = operands[1..]
        .iter()
        .map(|op| {
            let canon = CanonOperand::from_operand(op, vreg_versions);
            // Relocation-pseudo fixpoint: when a source VReg was already
            // CSE-eliminated to a dominating leader earlier in this pass,
            // value-number it as the leader so the dependent AddPCRel collapses
            // in the same pass. Only supplied for the relocation address
            // pseudos (see call site); `None` leaves all other CSE unchanged.
            if let (Some(leaders), CanonOperand::VReg(v, ver)) = (reloc_leaders, &canon)
                && let Some(&leader) = leaders.get(&(*v, *ver))
            {
                // A CSE leader is single-def (the multi-def guards reject any
                // other case), so its version is stable; key on it exactly as
                // the leader's own defining instruction was keyed.
                let leader_ver = vreg_versions.get(&leader).copied().unwrap_or(0);
                return CanonOperand::VReg(leader, leader_ver);
            }
            canon
        })
        .collect();

    // For commutative operations, sort operands for canonical form.
    if is_commutative && canon_ops.len() == 2 {
        canon_ops.sort_by(canon_operand_cmp);
    }

    ExprKey {
        category,
        opcode,
        result_class,
        operands: canon_ops,
    }
}

fn count_defs(func: &MachFunction) -> HashMap<VReg, u32> {
    let mut counts = HashMap::new();

    for &block_id in &func.block_order {
        let block = func.block(block_id);
        for &inst_id in &block.insts {
            let inst = func.inst(inst_id);
            if produces_value(inst.opcode)
                && let Some(MachOperand::VReg(vreg)) = inst.operands.first()
            {
                *counts.entry(*vreg).or_insert(0) += 1;
            }
        }
    }

    counts
}

fn collect_tied_def_use_vregs(func: &MachFunction) -> HashSet<VReg> {
    let mut tied_vregs = HashSet::new();

    for &block_id in &func.block_order {
        let block = func.block(block_id);
        for &inst_id in &block.insts {
            let inst = func.inst(inst_id);
            if has_tied_def_use(inst.opcode)
                && let Some(MachOperand::VReg(vreg)) = inst.operands.first()
            {
                tied_vregs.insert(*vreg);
            }
        }
    }

    tied_vregs
}

fn has_multi_def(vreg: VReg, def_counts: &HashMap<VReg, u32>) -> bool {
    def_counts.get(&vreg).copied().unwrap_or(0) > 1
}

fn has_multi_def_vreg_operand(operands: &[MachOperand], def_counts: &HashMap<VReg, u32>) -> bool {
    operands.iter().any(|operand| {
        matches!(
            operand,
            MachOperand::VReg(vreg) if has_multi_def(*vreg, def_counts)
        )
    })
}

/// Comparison function for canonicalizing operand order.
fn canon_operand_cmp(a: &CanonOperand, b: &CanonOperand) -> std::cmp::Ordering {
    use std::cmp::Ordering;
    match (a, b) {
        (CanonOperand::VReg(a, a_ver), CanonOperand::VReg(b, b_ver)) => {
            a.cmp(b).then(a_ver.cmp(b_ver))
        }
        (CanonOperand::Imm(a), CanonOperand::Imm(b)) => a.cmp(b),
        (CanonOperand::FImm(a), CanonOperand::FImm(b)) => a.cmp(b),
        (CanonOperand::Symbol(a), CanonOperand::Symbol(b)) => a.cmp(b),
        (CanonOperand::VReg(_, _), _) => Ordering::Less,
        (_, CanonOperand::VReg(_, _)) => Ordering::Greater,
        (CanonOperand::Imm(_), _) => Ordering::Less,
        (_, CanonOperand::Imm(_)) => Ordering::Greater,
        (CanonOperand::FImm(_), _) => Ordering::Less,
        (_, CanonOperand::FImm(_)) => Ordering::Greater,
        (CanonOperand::Symbol(_), _) => Ordering::Less,
        (_, CanonOperand::Symbol(_)) => Ordering::Greater,
        (CanonOperand::Other, CanonOperand::Other) => Ordering::Equal,
    }
}

/// Walk dominator tree in preorder (parent before children).
fn dom_preorder(dom: &DomTree, entry: BlockId) -> Vec<BlockId> {
    let mut order = Vec::new();
    let mut stack = vec![entry];

    while let Some(block) = stack.pop() {
        order.push(block);
        // Push children in reverse order so we visit them left-to-right.
        let children = dom.children(block);
        for &child in children.iter().rev() {
            stack.push(child);
        }
    }

    order
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pass_manager::MachinePass;
    use trust_cg_ir::aarch64_regs::{X0, X1};
    use trust_cg_ir::{
        AArch64Opcode, MachFunction, MachInst, MachOperand, PReg, PassId, ProofAnnotation,
        RegClass, Signature, TransformKind, TrustIrInstId, VReg,
    };

    fn vreg(id: u32) -> MachOperand {
        MachOperand::VReg(VReg::new(id, RegClass::Gpr64))
    }

    fn vreg_class(id: u32, class: RegClass) -> MachOperand {
        MachOperand::VReg(VReg::new(id, class))
    }

    fn imm(val: i64) -> MachOperand {
        MachOperand::Imm(val)
    }

    fn make_func_with_insts(insts: Vec<MachInst>) -> MachFunction {
        let mut func = MachFunction::new("test_cse".to_string(), Signature::new(vec![], vec![]));
        let block = func.entry;
        for inst in insts {
            let id = func.push_inst(inst);
            func.append_inst(block, id);
        }
        func
    }

    /// Run CSE with the relocation-pseudo fixpoint explicitly ENABLED, without
    /// touching process env (which would race across parallel tests). This
    /// exercises the same code path the default pipeline takes (fixpoint ON
    /// unless the `TCG_ADRP_CSE_FIXPOINT_OFF` kill switch is set).
    fn run_cse_fixpoint(func: &mut MachFunction) -> bool {
        let dom = crate::dom::DomTree::compute(func);
        super::run_cse(func, &dom, None, true)
    }

    #[test]
    fn test_cse_identical_adds() {
        // v2 = add v0, v1
        // v3 = add v0, v1   → eliminated, v3 replaced with v2
        // v4 = sub v3, #1   → v4 = sub v2, #1
        // ret
        let a1 = MachInst::new(AArch64Opcode::AddRR, vec![vreg(2), vreg(0), vreg(1)]);
        let a2 = MachInst::new(AArch64Opcode::AddRR, vec![vreg(3), vreg(0), vreg(1)]);
        let sub = MachInst::new(AArch64Opcode::SubRI, vec![vreg(4), vreg(3), imm(1)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![a1, a2, sub, ret]);

        let mut cse = CommonSubexprElim;
        assert!(cse.run(&mut func));

        // a2 should be removed
        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 3); // a1, sub, ret

        // sub should now use v2 instead of v3
        let sub_inst = func.inst(block.insts[1]);
        assert_eq!(sub_inst.operands[1], vreg(2));
    }

    #[test]
    fn test_cse_commutative() {
        // v2 = add v0, v1
        // v3 = add v1, v0   → eliminated (commutative: v0+v1 == v1+v0)
        // ret
        let a1 = MachInst::new(AArch64Opcode::AddRR, vec![vreg(2), vreg(0), vreg(1)]);
        let a2 = MachInst::new(AArch64Opcode::AddRR, vec![vreg(3), vreg(1), vreg(0)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![a1, a2, ret]);

        let mut cse = CommonSubexprElim;
        assert!(cse.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 2); // a1, ret
    }

    #[test]
    fn test_cse_no_cse_loads() {
        // v2 = ldr v0, #8
        // v3 = ldr v0, #8   → NOT eliminated (loads are not pure)
        // ret
        let l1 = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(2), vreg(0), imm(8)]);
        let l2 = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(3), vreg(0), imm(8)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![l1, l2, ret]);

        let mut cse = CommonSubexprElim;
        assert!(!cse.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 3);
    }

    #[test]
    fn test_cse_skips_implicit_physical_register_operands() {
        static IMPLICIT_USES: &[PReg] = &[X0];
        static IMPLICIT_DEFS: &[PReg] = &[X1];

        let a1 = MachInst::new(AArch64Opcode::AddRR, vec![vreg(2), vreg(0), vreg(1)])
            .with_implicit_uses(IMPLICIT_USES);
        let a2 = MachInst::new(AArch64Opcode::AddRR, vec![vreg(3), vreg(0), vreg(1)])
            .with_implicit_uses(IMPLICIT_USES);
        let a3 = MachInst::new(AArch64Opcode::SubRR, vec![vreg(4), vreg(0), vreg(1)])
            .with_implicit_defs(IMPLICIT_DEFS);
        let a4 = MachInst::new(AArch64Opcode::SubRR, vec![vreg(5), vreg(0), vreg(1)])
            .with_implicit_defs(IMPLICIT_DEFS);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![a1, a2, a3, a4, ret]);

        let mut cse = CommonSubexprElim;
        assert!(
            !cse.run(&mut func),
            "CSE keys do not model implicit physical-register operands"
        );

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 5);
    }

    #[test]
    fn test_cse_different_operands() {
        // v2 = add v0, v1
        // v3 = add v0, v4   → different operands, not CSE'd
        // ret
        let a1 = MachInst::new(AArch64Opcode::AddRR, vec![vreg(2), vreg(0), vreg(1)]);
        let a2 = MachInst::new(AArch64Opcode::AddRR, vec![vreg(3), vreg(0), vreg(4)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![a1, a2, ret]);

        let mut cse = CommonSubexprElim;
        assert!(!cse.run(&mut func));
    }

    #[test]
    fn test_cse_same_numeric_id_different_class_def_does_not_block_merge() {
        // A same numeric id in another register class is a different VReg.
        // It must not make v2:Gpr64 look multiply defined.
        let unrelated = MachInst::new(
            AArch64Opcode::Movz,
            vec![vreg_class(2, RegClass::Gpr32), imm(13)],
        );
        let leader = MachInst::new(
            AArch64Opcode::Movz,
            vec![vreg_class(2, RegClass::Gpr64), imm(7)],
        );
        let duplicate = MachInst::new(
            AArch64Opcode::Movz,
            vec![vreg_class(3, RegClass::Gpr64), imm(7)],
        );
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![unrelated, leader, duplicate, ret]);

        let mut cse = CommonSubexprElim;
        assert!(cse.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 3);
        assert_eq!(
            func.inst(block.insts[1]).operands[0],
            vreg_class(2, RegClass::Gpr64)
        );
    }

    #[test]
    fn test_cse_same_numeric_id_different_class_source_operands_do_not_merge() {
        // Mixed-class MovR is meaningful: Gpr32 -> Gpr64 can model
        // zero-extension, while Gpr64 -> Gpr64 is a transparent copy. CSE must
        // not key both source operands as just v0.
        let zero_extend = MachInst::new(
            AArch64Opcode::MovR,
            vec![
                vreg_class(2, RegClass::Gpr64),
                vreg_class(0, RegClass::Gpr32),
            ],
        );
        let copy = MachInst::new(
            AArch64Opcode::MovR,
            vec![
                vreg_class(3, RegClass::Gpr64),
                vreg_class(0, RegClass::Gpr64),
            ],
        );
        let use_copy = MachInst::new(
            AArch64Opcode::AddRI,
            vec![
                vreg_class(4, RegClass::Gpr64),
                vreg_class(3, RegClass::Gpr64),
                imm(1),
            ],
        );
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![zero_extend, copy, use_copy, ret]);

        let mut cse = CommonSubexprElim;
        assert!(!cse.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 4);
        assert_eq!(
            func.inst(block.insts[2]).operands[1],
            vreg_class(3, RegClass::Gpr64)
        );
    }

    #[test]
    fn test_cse_different_opcodes() {
        // v2 = add v0, v1
        // v3 = sub v0, v1   → different opcode
        // ret
        let a1 = MachInst::new(AArch64Opcode::AddRR, vec![vreg(2), vreg(0), vreg(1)]);
        let s1 = MachInst::new(AArch64Opcode::SubRR, vec![vreg(3), vreg(0), vreg(1)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![a1, s1, ret]);

        let mut cse = CommonSubexprElim;
        assert!(!cse.run(&mut func));
    }

    #[test]
    fn test_cse_non_commutative() {
        // v2 = sub v0, v1
        // v3 = sub v1, v0   → NOT eliminated (sub is not commutative)
        // ret
        let s1 = MachInst::new(AArch64Opcode::SubRR, vec![vreg(2), vreg(0), vreg(1)]);
        let s2 = MachInst::new(AArch64Opcode::SubRR, vec![vreg(3), vreg(1), vreg(0)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![s1, s2, ret]);

        let mut cse = CommonSubexprElim;
        assert!(!cse.run(&mut func));
    }

    #[test]
    fn test_cse_dominator_based() {
        // Diamond CFG:
        //   bb0: v2 = add v0, v1
        //   bb1: v3 = add v0, v1  → CSE'd (bb0 dominates bb1)
        //   bb2: v4 = add v0, v1  → CSE'd (bb0 dominates bb2)
        //   bb3: ret
        let mut func =
            MachFunction::new("test_cse_dom".to_string(), Signature::new(vec![], vec![]));
        let bb0 = func.entry;
        let bb1 = func.create_block();
        let bb2 = func.create_block();
        let bb3 = func.create_block();

        // bb0: add + branch
        let a0 = func.push_inst(MachInst::new(
            AArch64Opcode::AddRR,
            vec![vreg(2), vreg(0), vreg(1)],
        ));
        func.append_inst(bb0, a0);
        let br0 = func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![MachOperand::Block(bb1), MachOperand::Block(bb2)],
        ));
        func.append_inst(bb0, br0);

        // bb1: same add + branch
        let a1 = func.push_inst(MachInst::new(
            AArch64Opcode::AddRR,
            vec![vreg(3), vreg(0), vreg(1)],
        ));
        func.append_inst(bb1, a1);
        let br1 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb3)],
        ));
        func.append_inst(bb1, br1);

        // bb2: same add + branch
        let a2 = func.push_inst(MachInst::new(
            AArch64Opcode::AddRR,
            vec![vreg(4), vreg(0), vreg(1)],
        ));
        func.append_inst(bb2, a2);
        let br2 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb3)],
        ));
        func.append_inst(bb2, br2);

        // bb3: ret
        let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb3, ret);

        func.add_edge(bb0, bb1);
        func.add_edge(bb0, bb2);
        func.add_edge(bb1, bb3);
        func.add_edge(bb2, bb3);

        let mut cse = CommonSubexprElim;
        assert!(cse.run(&mut func));

        // bb1 and bb2 should have their adds removed.
        assert_eq!(func.block(bb1).insts.len(), 1); // just branch
        assert_eq!(func.block(bb2).insts.len(), 1); // just branch
    }

    #[test]
    fn test_cse_no_domination() {
        // Diamond: bb1 has add, bb2 has same add.
        // Neither bb1 nor bb2 dominates the other → no CSE between them.
        let mut func = MachFunction::new("test_no_dom".to_string(), Signature::new(vec![], vec![]));
        let bb0 = func.entry;
        let bb1 = func.create_block();
        let bb2 = func.create_block();
        let bb3 = func.create_block();

        let br0 = func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![MachOperand::Block(bb1), MachOperand::Block(bb2)],
        ));
        func.append_inst(bb0, br0);

        let a1 = func.push_inst(MachInst::new(
            AArch64Opcode::AddRR,
            vec![vreg(2), vreg(0), vreg(1)],
        ));
        func.append_inst(bb1, a1);
        let br1 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb3)],
        ));
        func.append_inst(bb1, br1);

        let a2 = func.push_inst(MachInst::new(
            AArch64Opcode::AddRR,
            vec![vreg(3), vreg(0), vreg(1)],
        ));
        func.append_inst(bb2, a2);
        let br2 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb3)],
        ));
        func.append_inst(bb2, br2);

        let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb3, ret);

        func.add_edge(bb0, bb1);
        func.add_edge(bb0, bb2);
        func.add_edge(bb1, bb3);
        func.add_edge(bb2, bb3);

        let mut cse = CommonSubexprElim;
        assert!(!cse.run(&mut func));

        // Both adds should remain.
        assert_eq!(func.block(bb1).insts.len(), 2);
        assert_eq!(func.block(bb2).insts.len(), 2);
    }

    #[test]
    fn test_cse_idempotent() {
        let a1 = MachInst::new(AArch64Opcode::AddRR, vec![vreg(2), vreg(0), vreg(1)]);
        let a2 = MachInst::new(AArch64Opcode::AddRR, vec![vreg(3), vreg(0), vreg(1)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![a1, a2, ret]);

        let mut cse = CommonSubexprElim;
        assert!(cse.run(&mut func));
        // Second run should be a no-op.
        assert!(!cse.run(&mut func));
    }

    #[test]
    fn test_cse_does_not_rewrite_later_redefinition_of_same_vreg() {
        // v2 = add v0, v1
        // v3 = add v0, v1   → not eliminated: v3 is redefined below
        // v3 = mov v4       → later redefinition of v3 must remain distinct
        // v5 = sub v3, #1   → must keep using the later v3, not v2
        let a1 = MachInst::new(AArch64Opcode::AddRR, vec![vreg(2), vreg(0), vreg(1)]);
        let a2 = MachInst::new(AArch64Opcode::AddRR, vec![vreg(3), vreg(0), vreg(1)]);
        let mov = MachInst::new(AArch64Opcode::MovR, vec![vreg(3), vreg(4)]);
        let sub = MachInst::new(AArch64Opcode::SubRI, vec![vreg(5), vreg(3), imm(1)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![a1, a2, mov, sub, ret]);

        let mut cse = CommonSubexprElim;
        assert!(!cse.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 5);

        let mov_inst = func.inst(block.insts[2]);
        assert_eq!(mov_inst.operands[0], vreg(3));

        let sub_inst = func.inst(block.insts[3]);
        assert_eq!(sub_inst.operands[1], vreg(3));
    }

    #[test]
    fn test_cse_does_not_rewrite_to_survivor_that_is_redefined() {
        // Rewriting v3 to v2 is unsafe because v2 is redefined before v3's
        // later use. In non-SSA machine IR, a raw VReg id is not a stable
        // value identity.
        let seed_v2 = MachInst::new(AArch64Opcode::Movz, vec![vreg(2), imm(7)]);
        let dup_v3 = MachInst::new(AArch64Opcode::Movz, vec![vreg(3), imm(7)]);
        let redefine_v2 = MachInst::new(AArch64Opcode::Movz, vec![vreg(2), imm(9)]);
        let use_v3 = MachInst::new(AArch64Opcode::AddRR, vec![vreg(4), vreg(3), vreg(0)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![seed_v2, dup_v3, redefine_v2, use_v3, ret]);

        let mut cse = CommonSubexprElim;
        assert!(
            !cse.run(&mut func),
            "CSE must not rewrite to a VReg id with multiple definitions"
        );

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 5);
        let use_inst = func.inst(block.insts[3]);
        assert_eq!(use_inst.operands[1], vreg(3));
    }

    #[test]
    fn test_cse_does_not_reuse_available_expression_across_call() {
        let before_call = MachInst::new(AArch64Opcode::Movz, vec![vreg(2), imm(1)]);
        let call = MachInst::new(
            AArch64Opcode::Bl,
            vec![MachOperand::Symbol("callee".to_string())],
        );
        let after_call = MachInst::new(AArch64Opcode::Movz, vec![vreg(3), imm(1)]);
        let use_after_call = MachInst::new(AArch64Opcode::AddRR, vec![vreg(4), vreg(3), vreg(0)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func =
            make_func_with_insts(vec![before_call, call, after_call, use_after_call, ret]);

        let mut cse = CommonSubexprElim;
        assert!(
            !cse.run(&mut func),
            "CSE must not extend values across call barriers"
        );

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 5);
        let use_inst = func.inst(block.insts[3]);
        assert_eq!(use_inst.operands[1], vreg(3));
    }

    #[test]
    fn test_cse_does_not_eliminate_multidef_join_carrier() {
        // Non-SSA machine IR can reuse the same vreg id as a block-carried
        // value. Eliminating one dominated redefinition and rewriting later
        // join uses to the dominating temp is unsound because the join may
        // also be reached from a sibling definition of the same vreg id.
        let mut func = MachFunction::new(
            "test_cse_multidef_join_carrier".to_string(),
            Signature::new(vec![], vec![]),
        );
        let bb0 = func.entry;
        let bb1 = func.create_block();
        let bb2 = func.create_block();
        let bb3 = func.create_block();
        let bb4 = func.create_block();

        let br0 = func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![MachOperand::Block(bb1), MachOperand::Block(bb2)],
        ));
        func.append_inst(bb0, br0);

        let carry_seed =
            func.push_inst(MachInst::new(AArch64Opcode::MovR, vec![vreg(10), vreg(7)]));
        func.append_inst(bb1, carry_seed);
        let br1 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb3)],
        ));
        func.append_inst(bb1, br1);

        let alt_def = func.push_inst(MachInst::new(AArch64Opcode::MovR, vec![vreg(18), vreg(7)]));
        func.append_inst(bb2, alt_def);
        let br2 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb4)],
        ));
        func.append_inst(bb2, br2);

        let dom_def = func.push_inst(MachInst::new(AArch64Opcode::MovR, vec![vreg(18), vreg(7)]));
        func.append_inst(bb3, dom_def);
        let br3 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb4)],
        ));
        func.append_inst(bb3, br3);

        let use_join = func.push_inst(MachInst::new(
            AArch64Opcode::AddRR,
            vec![vreg(20), vreg(18), vreg(0)],
        ));
        func.append_inst(bb4, use_join);
        let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb4, ret);

        func.add_edge(bb0, bb1);
        func.add_edge(bb0, bb2);
        func.add_edge(bb1, bb3);
        func.add_edge(bb2, bb4);
        func.add_edge(bb3, bb4);

        let mut cse = CommonSubexprElim;
        assert!(!cse.run(&mut func));

        let join_block = func.block(bb4);
        let add_inst = func.inst(join_block.insts[0]);
        assert_eq!(add_inst.operands[1], vreg(18));
        assert_eq!(func.block(bb3).insts.len(), 2);
    }

    #[test]
    fn test_cse_mul_commutative() {
        // v2 = mul v0, v1
        // v3 = mul v1, v0   → CSE'd (mul is commutative)
        let m1 = MachInst::new(AArch64Opcode::MulRR, vec![vreg(2), vreg(0), vreg(1)]);
        let m2 = MachInst::new(AArch64Opcode::MulRR, vec![vreg(3), vreg(1), vreg(0)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![m1, m2, ret]);

        let mut cse = CommonSubexprElim;
        assert!(cse.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 2); // m1, ret
    }

    #[test]
    fn test_cse_immediate_operands() {
        // v1 = add v0, #5
        // v2 = add v0, #5   → CSE'd
        // ret
        let a1 = MachInst::new(AArch64Opcode::AddRI, vec![vreg(1), vreg(0), imm(5)]);
        let a2 = MachInst::new(AArch64Opcode::AddRI, vec![vreg(2), vreg(0), imm(5)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![a1, a2, ret]);

        let mut cse = CommonSubexprElim;
        assert!(cse.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 2); // a1, ret
    }

    #[test]
    fn test_cse_does_not_merge_different_result_register_classes() {
        // AArch64 uses the same opcode and immediate for 32-bit and 64-bit
        // MOVZ constants. They are not interchangeable: using a GPR32
        // replacement in a GPR64 address computation miscompiles native code.
        let zero32 = MachInst::new(
            AArch64Opcode::Movz,
            vec![MachOperand::VReg(VReg::new(1, RegClass::Gpr32)), imm(0)],
        );
        let zero64 = MachInst::new(
            AArch64Opcode::Movz,
            vec![MachOperand::VReg(VReg::new(2, RegClass::Gpr64)), imm(0)],
        );
        let use64 = MachInst::new(AArch64Opcode::AddRR, vec![vreg(3), vreg(0), vreg(2)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![zero32, zero64, use64, ret]);

        let mut cse = CommonSubexprElim;
        assert!(
            !cse.run(&mut func),
            "CSE result identity must include register class"
        );

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 4);
        let use_inst = func.inst(block.insts[2]);
        assert_eq!(use_inst.operands[2], vreg(2));
    }

    #[test]
    fn test_cse_does_not_eliminate_flag_writing_checked_arithmetic() {
        // ADDS produces a register value and writes NZCV. Even when two ADDS
        // instructions have identical explicit operands, the later flag write
        // is observable by a following overflow branch or CSET.
        let a1 = MachInst::new(AArch64Opcode::AddsRR, vec![vreg(2), vreg(0), vreg(1)]);
        let a2 = MachInst::new(AArch64Opcode::AddsRR, vec![vreg(3), vreg(0), vreg(1)]);
        let use_second = MachInst::new(AArch64Opcode::AddRR, vec![vreg(4), vreg(3), vreg(0)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![a1, a2, use_second, ret]);

        let mut cse = CommonSubexprElim;
        assert!(
            !cse.run(&mut func),
            "CSE must not remove flag-writing ADDS/SUBS instructions"
        );

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 4);
        let use_inst = func.inst(block.insts[2]);
        assert_eq!(use_inst.operands[1], vreg(3));
    }

    #[test]
    fn test_cse_preserves_movz_seed_for_tied_def_use_chain() {
        // MOVK reads and writes its destination register. The seed definition
        // of that destination is therefore an implicit input to the MOVK chain,
        // even though operand[0] normally looks like a pure def.
        let seed_v2 = MachInst::new(AArch64Opcode::Movz, vec![vreg(2), imm(0)]);
        let seed_v3 = MachInst::new(AArch64Opcode::Movz, vec![vreg(3), imm(0)]);
        let movk_v3 = MachInst::new(AArch64Opcode::Movk, vec![vreg(3), imm(0xabcd), imm(16)]);
        let use_v3 = MachInst::new(AArch64Opcode::AddRR, vec![vreg(4), vreg(3), vreg(0)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![seed_v2, seed_v3, movk_v3, use_v3, ret]);

        let mut cse = CommonSubexprElim;
        assert!(
            !cse.run(&mut func),
            "CSE must not remove a MOVZ seed used by a later MOVK"
        );

        let block = func.block(func.entry);
        let movz_v3_count = block
            .insts
            .iter()
            .filter(|id| {
                let inst = func.inst(**id);
                inst.opcode == AArch64Opcode::Movz && inst.operands[0] == vreg(3)
            })
            .count();
        assert_eq!(movz_v3_count, 1);

        let use_inst = func.inst(block.insts[3]);
        assert_eq!(use_inst.operands[1], vreg(3));
    }

    #[test]
    fn test_cse_preserves_movk_with_different_destinations() {
        // Equal MOVK immediates are not common subexpressions unless the prior
        // destination-register value is also equal. CSE does not model that
        // implicit input, so both tied def-use instructions must remain.
        let seed_v2 = MachInst::new(AArch64Opcode::Movz, vec![vreg(2), imm(0x1111)]);
        let movk_v2 = MachInst::new(AArch64Opcode::Movk, vec![vreg(2), imm(0xabcd), imm(16)]);
        let seed_v3 = MachInst::new(AArch64Opcode::Movz, vec![vreg(3), imm(0x2222)]);
        let movk_v3 = MachInst::new(AArch64Opcode::Movk, vec![vreg(3), imm(0xabcd), imm(16)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![seed_v2, movk_v2, seed_v3, movk_v3, ret]);

        let mut cse = CommonSubexprElim;
        assert!(
            !cse.run(&mut func),
            "CSE must not merge MOVK tied def-use instructions"
        );

        let block = func.block(func.entry);
        let movk_count = block
            .insts
            .iter()
            .filter(|id| func.inst(**id).opcode == AArch64Opcode::Movk)
            .count();
        assert_eq!(movk_count, 2);
    }

    // ---- Proof annotation preservation tests ----

    #[test]
    fn test_cse_preserves_surviving_proof() {
        // v2 = add v0, v1 [NoOverflow]
        // v3 = add v0, v1 (no proof) → eliminated, v3 → v2
        // Surviving instruction keeps its proof.
        let a1 = MachInst::new(AArch64Opcode::AddRR, vec![vreg(2), vreg(0), vreg(1)])
            .with_proof(ProofAnnotation::NoOverflow);
        let a2 = MachInst::new(AArch64Opcode::AddRR, vec![vreg(3), vreg(0), vreg(1)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![a1, a2, ret]);

        let mut cse = CommonSubexprElim;
        assert!(cse.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 2); // a1, ret
        let surviving = func.inst(block.insts[0]);
        assert_eq!(surviving.proof, Some(ProofAnnotation::NoOverflow));
    }

    #[test]
    fn test_cse_merges_proof_from_eliminated() {
        // v2 = add v0, v1 (no proof)
        // v3 = add v0, v1 [InBounds] → eliminated, proof merged onto v2
        // Surviving instruction gets the eliminated instruction's proof.
        let a1 = MachInst::new(AArch64Opcode::AddRR, vec![vreg(2), vreg(0), vreg(1)]);
        let a2 = MachInst::new(AArch64Opcode::AddRR, vec![vreg(3), vreg(0), vreg(1)])
            .with_proof(ProofAnnotation::InBounds);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![a1, a2, ret]);

        let mut cse = CommonSubexprElim;
        assert!(cse.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 2); // a1, ret
        let surviving = func.inst(block.insts[0]);
        assert_eq!(surviving.proof, Some(ProofAnnotation::InBounds));
    }

    #[test]
    fn test_cse_merges_same_proof() {
        // Both instructions have the same proof → surviving keeps it.
        let a1 = MachInst::new(AArch64Opcode::AddRR, vec![vreg(2), vreg(0), vreg(1)])
            .with_proof(ProofAnnotation::NotNull);
        let a2 = MachInst::new(AArch64Opcode::AddRR, vec![vreg(3), vreg(0), vreg(1)])
            .with_proof(ProofAnnotation::NotNull);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![a1, a2, ret]);

        let mut cse = CommonSubexprElim;
        assert!(cse.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 2);
        let surviving = func.inst(block.insts[0]);
        assert_eq!(surviving.proof, Some(ProofAnnotation::NotNull));
    }

    #[test]
    fn test_cse_drops_conflicting_proofs() {
        // Different proofs → conservative merge returns None.
        let a1 = MachInst::new(AArch64Opcode::AddRR, vec![vreg(2), vreg(0), vreg(1)])
            .with_proof(ProofAnnotation::NoOverflow);
        let a2 = MachInst::new(AArch64Opcode::AddRR, vec![vreg(3), vreg(0), vreg(1)])
            .with_proof(ProofAnnotation::InBounds);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![a1, a2, ret]);

        let mut cse = CommonSubexprElim;
        assert!(cse.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 2);
        let surviving = func.inst(block.insts[0]);
        // Different proofs → conservatively dropped
        assert!(surviving.proof.is_none());
    }

    // ---- Provenance preservation tests ----

    #[test]
    fn test_cse_provenance_merges_eliminated_expression_into_survivor() {
        // v2 = add v0, v1
        // v3 = add v0, v1   → eliminated, provenance merged into v2
        // v4 = sub v3, #1   → rewritten in place to use v2
        let a1 = MachInst::new(AArch64Opcode::AddRR, vec![vreg(2), vreg(0), vreg(1)]);
        let a2 = MachInst::new(AArch64Opcode::AddRR, vec![vreg(3), vreg(0), vreg(1)]);
        let sub = MachInst::new(AArch64Opcode::SubRI, vec![vreg(4), vreg(3), imm(1)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![a1, a2, sub, ret]);

        let block = func.block(func.entry);
        let leader_id = block.insts[0];
        let eliminated_id = block.insts[1];
        let rewritten_id = block.insts[2];
        let ret_id = block.insts[3];

        let mut provenance = ProvenanceMap::new();
        provenance.record_lowering(TrustIrInstId(50), &[leader_id], PassId::new("isel"));
        provenance.record_lowering(TrustIrInstId(51), &[eliminated_id], PassId::new("isel"));
        provenance.record_lowering(TrustIrInstId(52), &[rewritten_id], PassId::new("isel"));
        provenance.record_lowering(TrustIrInstId(53), &[ret_id], PassId::new("isel"));

        let mut cse = CommonSubexprElim;
        let mut analyses = AnalysisCache::new();
        assert!(cse.run_with_analyses_and_provenance(&mut func, &mut analyses, &mut provenance));

        let block = func.block(func.entry);
        assert_eq!(block.insts, vec![leader_id, rewritten_id, ret_id]);
        assert_eq!(func.inst(rewritten_id).operands[1], vreg(2));

        let leader_entry = provenance
            .get_entry(leader_id)
            .expect("surviving CSE leader keeps merged provenance");
        assert!(leader_entry.is_active());
        assert_eq!(
            leader_entry.trust_ir_origins,
            vec![TrustIrInstId(50), TrustIrInstId(51)]
        );
        assert!(
            leader_entry.transforms.iter().any(|record| {
                record.pass == PassId::new("cse")
                    && record.kind
                        == TransformKind::Merged {
                            sources: vec![leader_id, eliminated_id],
                        }
            }),
            "leader should record the duplicate merge"
        );
        assert!(
            provenance.get_entry(eliminated_id).is_none(),
            "eliminated duplicate provenance moves to the leader"
        );
        assert_eq!(
            provenance.get_mach_insts(TrustIrInstId(51)).unwrap(),
            &[leader_id]
        );

        let rewritten_entry = provenance
            .get_entry(rewritten_id)
            .expect("rewritten user keeps provenance");
        assert_eq!(rewritten_entry.trust_ir_origins, vec![TrustIrInstId(52)]);
        assert!(
            rewritten_entry.transforms.iter().any(|record| {
                record.pass == PassId::new("cse") && record.kind == TransformKind::Survived
            }),
            "use rewrite should be recorded as an in-place transform"
        );
        assert!(provenance.get_entry(ret_id).unwrap().transforms.len() == 1);
    }

    #[test]
    fn test_cse_direct_provenance_hook_records_commutative_merge() {
        let a1 = MachInst::new(AArch64Opcode::AddRR, vec![vreg(2), vreg(0), vreg(1)]);
        let a2 = MachInst::new(AArch64Opcode::AddRR, vec![vreg(3), vreg(1), vreg(0)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![a1, a2, ret]);

        let block = func.block(func.entry);
        let leader_id = block.insts[0];
        let eliminated_id = block.insts[1];

        let mut provenance = ProvenanceMap::new();
        provenance.record_lowering(TrustIrInstId(60), &[leader_id], PassId::new("isel"));
        provenance.record_lowering(TrustIrInstId(61), &[eliminated_id], PassId::new("isel"));

        let mut cse = CommonSubexprElim;
        assert!(cse.run_with_provenance(&mut func, &mut provenance));

        assert_eq!(func.block(func.entry).insts.len(), 2);
        let leader_entry = provenance.get_entry(leader_id).unwrap();
        assert_eq!(
            leader_entry.trust_ir_origins,
            vec![TrustIrInstId(60), TrustIrInstId(61)]
        );
        assert_eq!(
            provenance.get_mach_insts(TrustIrInstId(61)).unwrap(),
            &[leader_id]
        );
    }

    // ---- Regression tests for #432 (Movz/Movn opcode collision) ----

    #[test]
    fn test_cse_movz_movn_same_imm_not_merged() {
        // Issue #432: `Movz Xd, #2` materializes +2, `Movn Xd, #2` materializes
        // ~2 = -3. Both categorize as `OpcodeCategory::MovRI`. Without opcode
        // disambiguation, CSE silently collapses them — a soundness bug. The
        // fix includes the opcode discriminant in the CSE expression key so
        // that these two instructions produce distinct keys.
        //
        // This test MUST fail on main before the fix and pass after.
        let mz = MachInst::new(AArch64Opcode::Movz, vec![vreg(2), imm(2)]);
        let mn = MachInst::new(AArch64Opcode::Movn, vec![vreg(3), imm(2)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![mz, mn, ret]);

        let mut cse = CommonSubexprElim;
        // No CSE should happen: Movz and Movn have different semantics.
        assert!(!cse.run(&mut func), "CSE must not merge Movz and Movn");

        // Both instructions must remain.
        let block = func.block(func.entry);
        assert_eq!(
            block.insts.len(),
            3,
            "Expected Movz, Movn, Ret — got {} insts (CSE miscompiled Movz/Movn)",
            block.insts.len()
        );
        assert_eq!(func.inst(block.insts[0]).opcode, AArch64Opcode::Movz);
        assert_eq!(func.inst(block.insts[1]).opcode, AArch64Opcode::Movn);
    }

    #[test]
    fn test_cse_movz_movz_same_imm_merged() {
        // Sanity: two identical Movz still get CSE'd. Guards against an
        // over-aggressive fix that disables CSE across the whole MovRI
        // category.
        let mz1 = MachInst::new(AArch64Opcode::Movz, vec![vreg(2), imm(7)]);
        let mz2 = MachInst::new(AArch64Opcode::Movz, vec![vreg(3), imm(7)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![mz1, mz2, ret]);

        let mut cse = CommonSubexprElim;
        assert!(cse.run(&mut func), "Identical Movz #7 pair should CSE");

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 2); // Movz, Ret
    }

    #[test]
    fn test_cse_movn_movn_same_imm_merged() {
        // Sanity: two identical Movn still get CSE'd.
        let mn1 = MachInst::new(AArch64Opcode::Movn, vec![vreg(2), imm(3)]);
        let mn2 = MachInst::new(AArch64Opcode::Movn, vec![vreg(3), imm(3)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![mn1, mn2, ret]);

        let mut cse = CommonSubexprElim;
        assert!(cse.run(&mut func), "Identical Movn #3 pair should CSE");

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 2); // Movn, Ret
    }

    // ---- ADRP-DEDUP: symbol-bearing address materialization ----

    fn symbol(name: &str) -> MachOperand {
        MachOperand::Symbol(name.to_string())
    }

    #[test]
    fn test_cse_dedupes_identical_adrp_addpcrel_pair() {
        // The globals-heavy shape that dominates Towers/Bubblesort/Dhrystone:
        //   v2 = adrp   @g
        //   v3 = addpcrel v2, @g   (address of @g)
        //   v4 = adrp   @g         → eliminated: same symbol, same page
        //   v5 = addpcrel v4, @g   → eliminated: base folds to leader v2, so
        //                            this AddPCRel now matches v3 exactly
        //   ret
        // The AddPCRel-fixpoint lever collapses BOTH the redundant Adrp and the
        // dependent AddPCRel in a SINGLE pass: once adrp2 (v4) is merged to the
        // leader v2, add2's base is value-numbered as v2, matching add1.
        let adrp1 = MachInst::new(AArch64Opcode::Adrp, vec![vreg(2), symbol("g")]);
        let add1 = MachInst::new(AArch64Opcode::AddPCRel, vec![vreg(3), vreg(2), symbol("g")]);
        let adrp2 = MachInst::new(AArch64Opcode::Adrp, vec![vreg(4), symbol("g")]);
        let add2 = MachInst::new(AArch64Opcode::AddPCRel, vec![vreg(5), vreg(4), symbol("g")]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![adrp1, add1, adrp2, add2, ret]);

        assert!(
            run_cse_fixpoint(&mut func),
            "identical Adrp+AddPCRel @g must dedupe"
        );

        let block = func.block(func.entry);
        // Both the redundant adrp2 (v4) and add2 (v5) are gone in ONE pass:
        // adrp1, add1, ret.
        assert_eq!(block.insts.len(), 3);
        assert_eq!(func.inst(block.insts[0]).opcode, AArch64Opcode::Adrp);
        assert_eq!(func.inst(block.insts[1]).opcode, AArch64Opcode::AddPCRel);
        assert_eq!(func.inst(block.insts[2]).opcode, AArch64Opcode::Ret);

        // Idempotent: a second pass finds nothing left to collapse.
        assert!(
            !run_cse_fixpoint(&mut func),
            "fixpoint already reached in one pass"
        );
    }

    #[test]
    fn test_cse_adrp_addpcrel_fixpoint_shares_base_for_field_loads() {
        // Dhrystone shape: two field accesses of the SAME global each get a
        // fresh Adrp+AddPCRel base, then load at distinct immediate offsets.
        //   v2 = adrp   @g
        //   v3 = addpcrel v2, @g
        //   v6 = ldr [v3, #0x67c]
        //   v4 = adrp   @g
        //   v5 = addpcrel v4, @g
        //   v7 = ldr [v5, #0x680]
        // After the fixpoint pass both loads must read the SINGLE surviving
        // base v3 (clang's shared x19), and only ONE Adrp+AddPCRel remains.
        let adrp1 = MachInst::new(AArch64Opcode::Adrp, vec![vreg(2), symbol("g")]);
        let add1 = MachInst::new(AArch64Opcode::AddPCRel, vec![vreg(3), vreg(2), symbol("g")]);
        let ld1 = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(6), vreg(3), imm(0x67c)]);
        let adrp2 = MachInst::new(AArch64Opcode::Adrp, vec![vreg(4), symbol("g")]);
        let add2 = MachInst::new(AArch64Opcode::AddPCRel, vec![vreg(5), vreg(4), symbol("g")]);
        let ld2 = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(7), vreg(5), imm(0x680)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![adrp1, add1, ld1, adrp2, add2, ld2, ret]);

        assert!(
            run_cse_fixpoint(&mut func),
            "field-access bases must share one pointer"
        );

        let block = func.block(func.entry);
        // adrp1, add1, ld1, ld2, ret — adrp2 and add2 collapsed.
        assert_eq!(block.insts.len(), 5);
        // Both loads now read the surviving base v3.
        let ld1_inst = func.inst(block.insts[2]);
        let ld2_inst = func.inst(block.insts[3]);
        assert_eq!(ld1_inst.opcode, AArch64Opcode::LdrRI);
        assert_eq!(ld2_inst.opcode, AArch64Opcode::LdrRI);
        assert_eq!(ld1_inst.operands[1], vreg(3));
        assert_eq!(ld2_inst.operands[1], vreg(3));
        // Offsets are preserved and distinct.
        assert_eq!(ld1_inst.operands[2], imm(0x67c));
        assert_eq!(ld2_inst.operands[2], imm(0x680));
    }

    #[test]
    fn test_cse_adrp_addpcrel_fixpoint_respects_distinct_symbols() {
        // Two DIFFERENT globals: neither the Adrps nor the AddPCRels may merge,
        // even though each AddPCRel reads its own (single-def) Adrp base.
        let adrp_a = MachInst::new(AArch64Opcode::Adrp, vec![vreg(2), symbol("g1")]);
        let add_a = MachInst::new(
            AArch64Opcode::AddPCRel,
            vec![vreg(3), vreg(2), symbol("g1")],
        );
        let adrp_b = MachInst::new(AArch64Opcode::Adrp, vec![vreg(4), symbol("g2")]);
        let add_b = MachInst::new(
            AArch64Opcode::AddPCRel,
            vec![vreg(5), vreg(4), symbol("g2")],
        );
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![adrp_a, add_a, adrp_b, add_b, ret]);

        assert!(
            !run_cse_fixpoint(&mut func),
            "distinct symbols must never share a base pointer"
        );
        assert_eq!(func.block(func.entry).insts.len(), 5);
    }

    #[test]
    fn test_cse_dedupes_adrp_dominance_correctly() {
        // Diamond: bb0 materializes @g and dominates bb1 and bb2, which each
        // re-materialize @g. Both dominated Adrps are eliminated (bb0 dominates
        // them); the sibling relationship never matters because the leader is
        // the common dominator.
        let mut func =
            MachFunction::new("cse_adrp_dom".to_string(), Signature::new(vec![], vec![]));
        let bb0 = func.entry;
        let bb1 = func.create_block();
        let bb2 = func.create_block();
        let bb3 = func.create_block();

        let a0 = func.push_inst(MachInst::new(
            AArch64Opcode::Adrp,
            vec![vreg(2), symbol("g")],
        ));
        func.append_inst(bb0, a0);
        let br0 = func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![MachOperand::Block(bb1), MachOperand::Block(bb2)],
        ));
        func.append_inst(bb0, br0);

        let a1 = func.push_inst(MachInst::new(
            AArch64Opcode::Adrp,
            vec![vreg(3), symbol("g")],
        ));
        func.append_inst(bb1, a1);
        let br1 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb3)],
        ));
        func.append_inst(bb1, br1);

        let a2 = func.push_inst(MachInst::new(
            AArch64Opcode::Adrp,
            vec![vreg(4), symbol("g")],
        ));
        func.append_inst(bb2, a2);
        let br2 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb3)],
        ));
        func.append_inst(bb2, br2);

        let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb3, ret);

        func.add_edge(bb0, bb1);
        func.add_edge(bb0, bb2);
        func.add_edge(bb1, bb3);
        func.add_edge(bb2, bb3);

        let mut cse = CommonSubexprElim;
        assert!(cse.run(&mut func));

        // bb1 and bb2 keep only their branch: the dominated Adrps were removed.
        assert_eq!(func.block(bb1).insts.len(), 1);
        assert_eq!(func.block(bb2).insts.len(), 1);
    }

    #[test]
    fn test_cse_does_not_dedupe_adrp_different_symbols() {
        // Distinct symbols name distinct pages: never merge.
        let a1 = MachInst::new(AArch64Opcode::Adrp, vec![vreg(2), symbol("g1")]);
        let a2 = MachInst::new(AArch64Opcode::Adrp, vec![vreg(3), symbol("g2")]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![a1, a2, ret]);

        let mut cse = CommonSubexprElim;
        assert!(
            !cse.run(&mut func),
            "Adrp of different symbols must not merge"
        );
        assert_eq!(func.block(func.entry).insts.len(), 3);
    }

    #[test]
    fn test_cse_does_not_dedupe_bl_call_targets() {
        // The Adrp/AddPCRel bypass must NOT extend to `Bl`: a call has side
        // effects and clobbers ABI registers, so two calls to the same symbol
        // are never common subexpressions. (`Bl` also does not produce a value,
        // an independent reason it is skipped — this test pins BOTH the value
        // and the symbol-bypass boundaries.)
        let c1 = MachInst::new(AArch64Opcode::Bl, vec![symbol("callee")]);
        let c2 = MachInst::new(AArch64Opcode::Bl, vec![symbol("callee")]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![c1, c2, ret]);

        let mut cse = CommonSubexprElim;
        assert!(!cse.run(&mut func), "CSE must never merge Bl call targets");
        assert_eq!(func.block(func.entry).insts.len(), 3);
    }
}
