// trust-cg-opt - Global Value Numbering
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Global Value Numbering (GVN) for machine-level IR.
//!
//! GVN assigns a unique *value number* to each computed expression. Two
//! instructions that compute the same value (same opcode and same
//! value-numbered operands) receive the same value number. When a
//! dominating instruction already defines a value with the same number,
//! the later instruction is redundant and can be eliminated.
//!
//! # Differences from CSE
//!
//! CSE uses syntactic expression keys (opcode + literal operand lists).
//! GVN is strictly more powerful because it uses *value numbers*, which
//! enables transitive reasoning: if `v2 = add v0, v1` and later
//! `v3 = mov v2`, then any instruction using `v3` sees the same value
//! number as `v2`, enabling further elimination.
//!
//! # Memory Load Value Numbering
//!
//! Pure loads from the same address (same opcode, same base value number,
//! same offset) receive the same value number within a single basic block.
//! Stores and calls act as memory barriers that invalidate load value numbers,
//! because they may modify arbitrary memory locations. The only exception is a
//! proof-reorderable ordinary store, which may preserve value numbers from
//! proof-reorderable ordinary loads whose keyed byte ranges do not overlap the
//! store. The current pass intentionally does not carry load value numbers
//! across block boundaries; doing that safely needs path-sensitive memory
//! availability so a load before a branch is not reused after a merge that has
//! a store on one incoming path.
//!
//! # Scoped Value Table
//!
//! The value table uses scope push/pop aligned with the dominator tree
//! walk. When entering a dominator-tree subtree, a scope is pushed;
//! when leaving, entries added in that subtree are removed. This ensures
//! that value numbers from non-dominating blocks are never visible.
//!
//! # Algorithm
//!
//! 1. Compute dominator tree.
//! 2. Walk blocks in dominator-tree preorder (ensures dominators are
//!    processed before dominated blocks).
//! 3. For each instruction:
//!    - Stores and calls invalidate all load value numbers.
//!    - Loads that produce values look up the load table; matches are
//!      eliminated, and misses get fresh value numbers.
//!    - Pure value-producing instructions compute a value-numbered key,
//!      look it up in the value table, eliminate matches, and assign fresh
//!      value numbers on misses.
//! 4. Apply replacements: rewrite vreg uses.
//! 5. Remove dead instructions.
//!
//! # Commutative Instructions
//!
//! For commutative operations (add, mul, and, or, xor, fadd, fmul),
//! the value-numbered operands are sorted before lookup. This allows
//! `add v1, v0` to match `add v0, v1`.
//!
//! Reference: LLVM `GVN.cpp`, Briggs & Cooper "Value Numbering"

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};

use trust_cg_ir::regs::preg_class;
use trust_cg_ir::{
    AArch64Opcode, BlockId, InstFlags, InstId, MachFunction, MachInst, MachOperand, PassId,
    ProofAnnotation, ProvenanceMap, RegClass, SpecialReg, VReg,
};

use crate::cache::StableHasher;
use crate::dom::DomTree;
use crate::effects::{
    MemoryEffect, aarch64_def_operand_positions, aarch64_use_operand_positions, has_tied_def_use,
    opcode_effect, reads_flags, writes_flags,
};
use crate::pass_manager::{AnalysisCache, MachinePass};
use crate::proof_opts::{
    OptAdmissionRoute, OptCertificate, OptCertificateKind, OptConsumedProofFact,
    OptTransformIdentity,
};

const GVN_PROOF_LOAD_ELIM_TRANSFORM: &str = "gvn.valid-borrow.load-eliminated";
const GVN_PROOF_LOAD_ELIM_VERSION: u32 = 1;
const GVN_PROOF_LOAD_ELIM_ADMISSION: &str = "proof-reorderable-load-store";

/// Global Value Numbering pass.
pub struct GlobalValueNumbering;

/// Statistics from the most recent GVN run on the current thread.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct GvnStats {
    /// Load eliminations whose availability depended on at least one
    /// intervening `PROOF_REORDERABLE` store preserving a proven load.
    pub proof_reorderable_load_eliminations: u32,
}

#[derive(Debug, Clone, Default)]
struct GvnObservability {
    stats: GvnStats,
    certificates: Vec<OptCertificate>,
}

thread_local! {
    static LAST_GVN_OBSERVABILITY: RefCell<GvnObservability> =
        RefCell::new(GvnObservability::default());
}

impl GlobalValueNumbering {
    /// Return the statistics from the most recent GVN run on this thread.
    pub fn stats(&self) -> GvnStats {
        LAST_GVN_OBSERVABILITY.with(|observability| observability.borrow().stats)
    }

    /// Drain proof-consumption certificates from the most recent GVN run.
    pub fn take_certificates(&mut self) -> Vec<OptCertificate> {
        LAST_GVN_OBSERVABILITY
            .with(|observability| std::mem::take(&mut observability.borrow_mut().certificates))
    }
}

fn publish_gvn_observability(stats: GvnStats, certificates: Vec<OptCertificate>) {
    LAST_GVN_OBSERVABILITY.with(|observability| {
        *observability.borrow_mut() = GvnObservability {
            stats,
            certificates,
        };
    });
}

impl MachinePass for GlobalValueNumbering {
    fn name(&self) -> &str {
        "gvn"
    }

    fn run(&mut self, func: &mut MachFunction) -> bool {
        let dom = DomTree::compute(func);
        let run = run_gvn(func, &dom, None);
        publish_gvn_observability(run.stats, run.certificates);
        run.changed
    }

    fn run_with_analyses(&mut self, func: &mut MachFunction, analyses: &mut AnalysisCache) -> bool {
        let dom = analyses.domtree(func).clone();
        let run = run_gvn(func, &dom, None);
        publish_gvn_observability(run.stats, run.certificates);
        run.changed
    }

    fn run_with_provenance(
        &mut self,
        func: &mut MachFunction,
        provenance: &mut ProvenanceMap,
    ) -> bool {
        let dom = DomTree::compute(func);
        let run = run_gvn(func, &dom, Some(provenance));
        publish_gvn_observability(run.stats, run.certificates);
        run.changed
    }

    fn run_with_analyses_and_provenance(
        &mut self,
        func: &mut MachFunction,
        analyses: &mut AnalysisCache,
        provenance: &mut ProvenanceMap,
    ) -> bool {
        let dom = analyses.domtree(func).clone();
        let run = run_gvn(func, &dom, Some(provenance));
        publish_gvn_observability(run.stats, run.certificates);
        run.changed
    }

    fn take_proof_optimization_certificates(&mut self) -> Vec<OptCertificate> {
        self.take_certificates()
    }
}

// ---------------------------------------------------------------------------
// Value number types
// ---------------------------------------------------------------------------

/// A value number. Two expressions with the same value number compute
/// the same result.
type ValNum = u32;

/// Counter for allocating fresh value numbers.
struct ValNumAllocator {
    next: ValNum,
}

impl ValNumAllocator {
    fn new() -> Self {
        Self { next: 0 }
    }

    fn fresh(&mut self) -> ValNum {
        let vn = self.next;
        self.next += 1;
        vn
    }
}

// ---------------------------------------------------------------------------
// Expression key (opcode + value-numbered operands)
// ---------------------------------------------------------------------------

/// A value-numbered expression key.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct VNExprKey {
    opcode: AArch64Opcode,
    /// Result register class. Some AArch64 opcodes are shared across widths
    /// in MachIR, so `Movz Wn, #1` and `Movz Xn, #1` are not interchangeable.
    result_class: RegClass,
    /// Value numbers of source operands (value-numbered, not raw vreg ids).
    operand_vns: Vec<ValNum>,
}

/// A load expression key (opcode + base value number + offset).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct LoadKey {
    opcode: AArch64Opcode,
    /// Result register class for width-sensitive opcodes such as `LdrRI`.
    result_class: RegClass,
    base_vn: ValNum,
    offset: i64,
}

/// A store byte range keyed by value-numbered base and immediate offset.
#[derive(Debug, Clone, Copy)]
struct StoreAccess {
    base_vn: ValNum,
    offset: i64,
    size: i64,
}

impl StoreAccess {
    fn may_clobber_load(self, load_key: &LoadKey) -> bool {
        if self.base_vn != load_key.base_vn {
            return false;
        }

        let Some(load_size) = load_access_size(load_key) else {
            return true;
        };

        byte_ranges_overlap(self.offset, self.size, load_key.offset, load_size)
    }
}

// ---------------------------------------------------------------------------
// Leader: the canonical instruction for a value number
// ---------------------------------------------------------------------------

/// Information about the first (leader) instruction for a value number.
#[derive(Debug, Clone)]
struct Leader {
    inst_id: InstId,
    def_vreg: VReg,
}

// ---------------------------------------------------------------------------
// Scoped value table
// ---------------------------------------------------------------------------

/// A scoped value table that supports push/pop aligned with dominator
/// tree traversal. Entries added in a child scope are removed when that
/// scope is popped.
struct ScopedValueTable {
    /// VReg -> value number.
    vreg_to_vn: HashMap<VReg, ValNum>,
    /// Expression key -> (value number, leader).
    expr_table: HashMap<VNExprKey, (ValNum, Leader)>,
    /// Load key -> value number and leader metadata.
    load_table: HashMap<LoadKey, LoadEntry>,
    /// Scope stack: each entry records keys added in that scope so
    /// they can be removed on pop.
    scope_stack: Vec<ScopeFrame>,
}

/// Records what was added during a single scope (one dominator-tree node).
#[derive(Default)]
struct ScopeFrame {
    added_vregs: Vec<VReg>,
    added_exprs: Vec<VNExprKey>,
    added_loads: Vec<LoadKey>,
    /// Whether load table was cleared in this scope (stores/calls).
    /// If so, we need to restore the previous load table on pop.
    cleared_loads: Option<HashMap<LoadKey, LoadEntry>>,
}

#[derive(Debug, Clone)]
struct LoadEntry {
    vn: ValNum,
    leader: Leader,
    proof_reorderable: bool,
    proof_reorderable_stores_crossed: Vec<InstId>,
}

impl ScopedValueTable {
    fn new() -> Self {
        Self {
            vreg_to_vn: HashMap::new(),
            expr_table: HashMap::new(),
            load_table: HashMap::new(),
            scope_stack: Vec::new(),
        }
    }

    fn push_scope(&mut self) {
        self.scope_stack.push(ScopeFrame::default());
    }

    fn pop_scope(&mut self) {
        let frame = self.scope_stack.pop().expect("scope underflow");
        // Remove entries added in this scope.
        for vreg in &frame.added_vregs {
            self.vreg_to_vn.remove(vreg);
        }
        for key in &frame.added_exprs {
            self.expr_table.remove(key);
        }
        for key in &frame.added_loads {
            self.load_table.remove(key);
        }
        // Restore load table if it was cleared.
        if let Some(saved) = frame.cleared_loads {
            self.load_table = saved;
        }
    }

    /// Assign a value number to a vreg.
    fn set_vreg_vn(&mut self, vreg: VReg, vn: ValNum) {
        self.vreg_to_vn.insert(vreg, vn);
        if let Some(frame) = self.scope_stack.last_mut() {
            frame.added_vregs.push(vreg);
        }
    }

    /// Look up the value number for a vreg.
    fn get_vreg_vn(&self, vreg: VReg) -> Option<ValNum> {
        self.vreg_to_vn.get(&vreg).copied()
    }

    /// Look up an expression in the value table.
    fn lookup_expr(&self, key: &VNExprKey) -> Option<&(ValNum, Leader)> {
        self.expr_table.get(key)
    }

    /// Insert an expression into the value table.
    fn insert_expr(&mut self, key: VNExprKey, vn: ValNum, leader: Leader) {
        if let Some(frame) = self.scope_stack.last_mut() {
            frame.added_exprs.push(key.clone());
        }
        self.expr_table.insert(key, (vn, leader));
    }

    /// Look up a load in the load table.
    fn lookup_load(&self, key: &LoadKey) -> Option<&LoadEntry> {
        self.load_table.get(key)
    }

    /// Insert a load into the load table.
    fn insert_load(&mut self, key: LoadKey, vn: ValNum, leader: Leader, proof_reorderable: bool) {
        if let Some(frame) = self.scope_stack.last_mut() {
            frame.added_loads.push(key.clone());
        }
        self.load_table.insert(
            key,
            LoadEntry {
                vn,
                leader,
                proof_reorderable,
                proof_reorderable_stores_crossed: Vec::new(),
            },
        );
    }

    fn save_load_table_for_scope(&mut self) {
        if let Some(frame) = self.scope_stack.last_mut()
            && frame.cleared_loads.is_none()
        {
            let mut saved = self.load_table.clone();
            for key in &frame.added_loads {
                saved.remove(key);
            }
            frame.cleared_loads = Some(saved);
        }
    }

    /// Invalidate all load value numbers (called on unproven store/call).
    /// Saves the current load table so it can be restored on scope pop.
    fn kill_loads(&mut self) {
        self.save_load_table_for_scope();
        self.load_table.clear();
    }

    /// Preserve only proven load value numbers that cannot be clobbered by a
    /// proof-reorderable ordinary store at `store_access`.
    fn kill_unproven_loads(&mut self, store_access: StoreAccess, store_inst_id: InstId) {
        self.save_load_table_for_scope();
        self.load_table.retain(|load_key, entry| {
            let preserved = entry.proof_reorderable && !store_access.may_clobber_load(load_key);
            if preserved {
                entry.proof_reorderable_stores_crossed.push(store_inst_id);
            }
            preserved
        });
    }
}

// ---------------------------------------------------------------------------
// Commutative opcode detection
// ---------------------------------------------------------------------------

/// Returns true if the opcode is commutative (operand order doesn't matter).
///
/// Delegates to the generic [`AArch64Opcode::is_commutative`] method for
/// multi-target compatibility.
fn is_commutative(opcode: AArch64Opcode) -> bool {
    opcode.is_commutative()
}

fn is_proof_reorderable_ordinary_load(inst: &MachInst) -> bool {
    use AArch64Opcode::*;

    if !trust_cg_lower::guard_evidence::validator_guard_replay_authority_available() && !cfg!(test)
    {
        return false;
    }

    let disqualifying_flags =
        InstFlags::WRITES_MEMORY | InstFlags::HAS_SIDE_EFFECTS | InstFlags::IS_CALL;

    inst.flags.contains(InstFlags::PROOF_REORDERABLE)
        && inst.flags.intersection(disqualifying_flags).is_empty()
        && matches!(
            inst.opcode,
            LdrRI | LdrbRI | LdrhRI | LdrsbRI | LdrshRI | LdrRO | LdrswRO | LdrLiteral | LdpRI
        )
}

fn is_proof_reorderable_ordinary_store(inst: &MachInst) -> bool {
    use AArch64Opcode::*;

    if !trust_cg_lower::guard_evidence::validator_guard_replay_authority_available() && !cfg!(test)
    {
        return false;
    }

    let disqualifying_flags = InstFlags::READS_MEMORY | InstFlags::IS_CALL | InstFlags::IS_PSEUDO;

    inst.flags.contains(InstFlags::PROOF_REORDERABLE)
        && inst.flags.contains(InstFlags::WRITES_MEMORY)
        && inst.flags.intersection(disqualifying_flags).is_empty()
        && matches!(
            inst.opcode,
            StrRI | StrbRI | StrhRI | StrRO | STRWui | STRXui | STRSui | STRDui | StpRI
        )
}

// ---------------------------------------------------------------------------
// Value number computation for an operand
// ---------------------------------------------------------------------------

/// Get the value number for a source operand. VRegs use the vreg map;
/// immediates get a deterministic value number derived from the value
/// (we use a separate per-immediate allocation to avoid collisions).
///
/// VRegs that have not yet been assigned a value number (e.g., function
/// parameters, vregs defined before the analyzed region) get a fresh
/// value number assigned on demand. This ensures every reachable vreg
/// has a stable value number.
fn operand_vn(
    op: &MachOperand,
    table: &mut ScopedValueTable,
    def_counts: &HashMap<VReg, u32>,
    imm_vns: &mut HashMap<i64, ValNum>,
    fimm_vns: &mut HashMap<u64, ValNum>,
    alloc: &mut ValNumAllocator,
) -> Option<ValNum> {
    match op {
        MachOperand::VReg(v) => {
            if def_counts.get(v).copied().unwrap_or(0) > 1 {
                // Machine IR is not in SSA form: ISel deliberately reuses
                // block-parameter vregs across predecessor copies. Value-numbering
                // or globally rewriting a multi-def vreg is unsound.
                return None;
            }
            if let Some(vn) = table.get_vreg_vn(*v) {
                Some(vn)
            } else {
                // First time seeing this vreg as a source — assign fresh VN.
                let vn = alloc.fresh();
                table.set_vreg_vn(*v, vn);
                Some(vn)
            }
        }
        MachOperand::Imm(i) => {
            let vn = *imm_vns.entry(*i).or_insert_with(|| alloc.fresh());
            Some(vn)
        }
        MachOperand::FImm(f) => {
            let bits = f.to_bits();
            let vn = *fimm_vns.entry(bits).or_insert_with(|| alloc.fresh());
            Some(vn)
        }
        // Non-hashable operands (blocks, pregs, etc.) — skip GVN.
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// Core GVN algorithm
// ---------------------------------------------------------------------------

/// Run GVN on the function, returning true if any changes were made.
fn run_gvn(
    func: &mut MachFunction,
    dom: &DomTree,
    provenance: Option<&mut ProvenanceMap>,
) -> GvnRun {
    let mut alloc = ValNumAllocator::new();
    let mut table = ScopedValueTable::new();
    let def_counts = count_defs(func);
    let mut imm_vns: HashMap<i64, ValNum> = HashMap::new();
    let mut fimm_vns: HashMap<u64, ValNum> = HashMap::new();
    let mut stats = GvnStats::default();

    // Replacement map: eliminated def vreg -> vreg of leader def.
    let mut replacements: HashMap<VReg, VReg> = HashMap::new();

    // Instructions to remove.
    let mut dead_insts: Vec<InstId> = Vec::new();

    // Eliminated instruction -> dominating leader that now supplies the value.
    let mut eliminated_merges: Vec<(InstId, InstId)> = Vec::new();

    // Proof annotations to merge onto surviving instructions.
    let mut proof_merges: Vec<(InstId, Option<ProofAnnotation>)> = Vec::new();

    // Proof-dependent load eliminations that need release-citable evidence.
    let mut proof_dependent_load_eliminations: Vec<ProofDependentLoadElimination> = Vec::new();

    // Pre-assign value numbers to function parameters (vregs with low ids
    // that appear as uses but never as defs within the function). We handle
    // this lazily: any vreg without a value number gets a fresh one when
    // first encountered as a source operand (see operand_vn + fallback below).

    // Walk dominator tree in preorder using a recursive-style iterative
    // traversal that pushes/pops scopes.
    dom_walk_gvn(
        func,
        dom,
        func.entry,
        &mut table,
        &mut alloc,
        &def_counts,
        &mut imm_vns,
        &mut fimm_vns,
        &mut replacements,
        &mut dead_insts,
        &mut eliminated_merges,
        &mut proof_merges,
        &mut proof_dependent_load_eliminations,
    );

    stats.proof_reorderable_load_eliminations = proof_dependent_load_eliminations.len() as u32;

    if replacements.is_empty() {
        return GvnRun {
            changed: false,
            stats,
            certificates: Vec::new(),
        };
    }

    // Apply proof merges.
    for (surviving_id, eliminated_proof) in proof_merges {
        let surviving = func.inst_mut(surviving_id);
        surviving.proof = ProofAnnotation::merge(surviving.proof, eliminated_proof);
    }

    if let Some(provenance) = provenance {
        let pass = PassId::new("gvn");
        eliminated_merges.sort_unstable();
        eliminated_merges.dedup();
        for (leader_id, eliminated_id) in eliminated_merges {
            provenance.record_merge(&[leader_id, eliminated_id], leader_id, pass.clone());
        }
    }

    // Apply replacements: rewrite all uses of eliminated vregs.
    for block_id in func.block_order.clone() {
        let block = func.block(block_id);
        for &inst_id in block.insts.clone().iter() {
            let inst = func.inst_mut(inst_id);
            let def_positions: HashSet<usize> =
                aarch64_def_operand_positions(inst.opcode, inst.operands.len())
                    .into_iter()
                    .collect();
            let use_positions = aarch64_use_operand_positions(inst.opcode, inst.operands.len());

            for i in use_positions {
                if def_positions.contains(&i) {
                    continue;
                }
                if let MachOperand::VReg(vreg) = &inst.operands[i]
                    && let Some(replacement) = replacements.get(vreg)
                {
                    inst.operands[i] = MachOperand::VReg(*replacement);
                }
            }
        }
    }

    // Remove dead instructions.
    let dead_set: HashSet<InstId> = dead_insts.into_iter().collect();
    for block_id in func.block_order.clone() {
        let block = func.block_mut(block_id);
        block.insts.retain(|id| !dead_set.contains(id));
    }

    let certificates = proof_dependent_load_eliminations
        .into_iter()
        .map(|elimination| make_proof_dependent_load_elimination_certificate(func, elimination))
        .collect();

    GvnRun {
        changed: true,
        stats,
        certificates,
    }
}

#[derive(Debug, Clone, Default)]
struct GvnRun {
    changed: bool,
    stats: GvnStats,
    certificates: Vec<OptCertificate>,
}

#[derive(Debug, Clone)]
struct ProofDependentLoadElimination {
    leader_inst: InstId,
    eliminated_inst: InstId,
    proof_reorderable_store_insts: Vec<InstId>,
    source_region_hash: u128,
}

fn count_defs(func: &MachFunction) -> HashMap<VReg, u32> {
    let mut counts: HashMap<VReg, u32> = HashMap::new();

    for block_id in &func.block_order {
        let block = func.block(*block_id);
        for &inst_id in &block.insts {
            let inst = func.inst(inst_id);
            for vreg in explicit_def_vregs(inst) {
                *counts.entry(vreg).or_insert(0) += 1;
            }
        }
    }

    counts
}

fn explicit_def_positions(inst: &MachInst) -> Vec<usize> {
    aarch64_def_operand_positions(inst.opcode, inst.operands.len())
}

fn explicit_def_vregs(inst: &MachInst) -> Vec<VReg> {
    explicit_def_positions(inst)
        .into_iter()
        .filter_map(|idx| match inst.operands.get(idx) {
            Some(MachOperand::VReg(vreg)) => Some(*vreg),
            _ => None,
        })
        .collect()
}

fn has_non_primary_def(inst: &MachInst) -> bool {
    explicit_def_positions(inst).into_iter().any(|idx| idx != 0)
}

/// Recursive dominator-tree walk with scope push/pop.
#[allow(clippy::too_many_arguments)]
fn dom_walk_gvn(
    func: &MachFunction,
    dom: &DomTree,
    block_id: BlockId,
    table: &mut ScopedValueTable,
    alloc: &mut ValNumAllocator,
    def_counts: &HashMap<VReg, u32>,
    imm_vns: &mut HashMap<i64, ValNum>,
    fimm_vns: &mut HashMap<u64, ValNum>,
    replacements: &mut HashMap<VReg, VReg>,
    dead_insts: &mut Vec<InstId>,
    eliminated_merges: &mut Vec<(InstId, InstId)>,
    proof_merges: &mut Vec<(InstId, Option<ProofAnnotation>)>,
    proof_dependent_load_eliminations: &mut Vec<ProofDependentLoadElimination>,
) {
    table.push_scope();
    let outer_load_table = std::mem::take(&mut table.load_table);

    let block = func.block(block_id);
    for &inst_id in &block.insts {
        let inst = func.inst(inst_id);
        let effect = opcode_effect(inst.opcode);

        // Stores and calls kill load value numbers. A proof-reorderable
        // ordinary store may preserve entries from proof-reorderable ordinary
        // loads at non-overlapping keyed addresses; every other write/barrier
        // stays conservative.
        if effect.writes_memory() || effect == MemoryEffect::Call {
            if is_proof_reorderable_ordinary_store(inst) {
                if let Some(store_access) =
                    make_store_access(inst, table, def_counts, imm_vns, fimm_vns, alloc)
                {
                    table.kill_unproven_loads(store_access, inst_id);
                } else {
                    table.kill_loads();
                }
            } else {
                table.kill_loads();
            }
        }

        let def_vregs = explicit_def_vregs(inst);
        if def_vregs.is_empty() {
            continue;
        }

        // Instructions with additional explicit defs, such as writeback
        // loads/stores, have observable register updates that are not modeled
        // by ordinary expression/load keys. Refresh all def VNs and do not
        // enter them into the elimination tables.
        if has_non_primary_def(inst) {
            for def_vreg in def_vregs {
                let vn = alloc.fresh();
                table.set_vreg_vn(def_vreg, vn);
            }
            continue;
        }

        // Skip instructions that read or write implicit NZCV flags. Flag
        // readers depend on state not captured in explicit operands; flag
        // writers have an observable side effect for the next reader. A value
        // number may still be needed for explicit uses of the result, but the
        // expression must not be entered into the elimination table.
        if reads_flags(inst.opcode) || writes_flags(inst.opcode) {
            // Assign fresh value numbers so downstream uses get unique
            // numbering, but do NOT insert into the expression table.
            for v in def_vregs {
                let vn = alloc.fresh();
                table.set_vreg_vn(v, vn);
            }
            continue;
        }

        // Get the def vreg (operand[0]).
        let def_vreg = match &inst.operands.first() {
            Some(MachOperand::VReg(v)) => *v,
            _ => continue,
        };

        if def_counts.get(&def_vreg).copied().unwrap_or(0) > 1 {
            // Do not let a multi-def vreg participate in the value table.
            // The later global replacement phase is keyed by full vreg.
            let vn = alloc.fresh();
            table.set_vreg_vn(def_vreg, vn);
            continue;
        }

        // Handle loads: value number via load table.
        if effect == MemoryEffect::Load {
            if let Some(load_key) = make_load_key(inst, table, def_counts, imm_vns, fimm_vns, alloc)
            {
                if let Some(entry) = table.lookup_load(&load_key) {
                    // Found a matching load — eliminate this one.
                    let vn = entry.vn;
                    let leader_clone = entry.leader.clone();
                    let proof_store_insts = entry.proof_reorderable_stores_crossed.clone();
                    if !proof_store_insts.is_empty() {
                        let mut source_region = Vec::with_capacity(proof_store_insts.len() + 2);
                        source_region.push(leader_clone.inst_id);
                        source_region.extend(proof_store_insts.iter().copied());
                        source_region.push(inst_id);
                        proof_dependent_load_eliminations.push(ProofDependentLoadElimination {
                            leader_inst: leader_clone.inst_id,
                            eliminated_inst: inst_id,
                            proof_reorderable_store_insts: proof_store_insts,
                            source_region_hash: gvn_region_hash(func, &source_region),
                        });
                    }
                    table.set_vreg_vn(def_vreg, vn);
                    replacements.insert(def_vreg, leader_clone.def_vreg);
                    dead_insts.push(inst_id);
                    eliminated_merges.push((leader_clone.inst_id, inst_id));
                    proof_merges.push((leader_clone.inst_id, inst.proof));
                    continue;
                }
                // New load — assign fresh value number.
                let vn = alloc.fresh();
                table.set_vreg_vn(def_vreg, vn);
                table.insert_load(
                    load_key,
                    vn,
                    Leader { inst_id, def_vreg },
                    is_proof_reorderable_ordinary_load(inst),
                );
                continue;
            }
            // Could not form a load key (e.g., non-standard operands).
            // Assign a fresh value number and move on.
            let vn = alloc.fresh();
            table.set_vreg_vn(def_vreg, vn);
            continue;
        }

        // Handle pure instructions.
        if effect == MemoryEffect::Pure
            && let Some(expr_key) = make_expr_key(inst, table, def_counts, imm_vns, fimm_vns, alloc)
        {
            if let Some((existing_vn, leader)) = table.lookup_expr(&expr_key) {
                // Found a matching expression — eliminate this one.
                let vn = *existing_vn;
                let leader_clone = leader.clone();
                table.set_vreg_vn(def_vreg, vn);
                replacements.insert(def_vreg, leader_clone.def_vreg);
                dead_insts.push(inst_id);
                eliminated_merges.push((leader_clone.inst_id, inst_id));
                proof_merges.push((leader_clone.inst_id, inst.proof));
                continue;
            }
            // New expression — assign fresh value number.
            let vn = alloc.fresh();
            table.set_vreg_vn(def_vreg, vn);
            table.insert_expr(expr_key, vn, Leader { inst_id, def_vreg });
            continue;
        }

        // Fallback: non-matchable instruction, assign fresh value number.
        let vn = alloc.fresh();
        table.set_vreg_vn(def_vreg, vn);
    }

    // Load value numbers are block-local. A dominator-tree scoped load table is
    // not enough to prove memory availability at CFG merges: a sibling branch
    // may store to the same address before control reaches the merge block.
    table.load_table.clear();

    // Recurse into dominator-tree children.
    for &child in dom.children(block_id) {
        dom_walk_gvn(
            func,
            dom,
            child,
            table,
            alloc,
            def_counts,
            imm_vns,
            fimm_vns,
            replacements,
            dead_insts,
            eliminated_merges,
            proof_merges,
            proof_dependent_load_eliminations,
        );
    }

    table.load_table.clear();
    table.pop_scope();
    table.load_table = outer_load_table;
}

/// Build a value-numbered expression key for a pure instruction.
///
/// Returns `None` if any source operand cannot be value-numbered
/// (e.g., block operands, physical registers) OR if the instruction
/// has a tied def-use operand whose prior value is an implicit input
/// (e.g., MOVK).
fn make_expr_key(
    inst: &trust_cg_ir::MachInst,
    table: &mut ScopedValueTable,
    def_counts: &HashMap<VReg, u32>,
    imm_vns: &mut HashMap<i64, ValNum>,
    fimm_vns: &mut HashMap<u64, ValNum>,
    alloc: &mut ValNumAllocator,
) -> Option<VNExprKey> {
    // Instructions with tied def-use (e.g., MOVK) cannot be value-numbered
    // using just (opcode, source operands): the destination register's
    // prior value is also an input. Two MOVKs with identical (imm, shift)
    // but different dest registers compute DIFFERENT values.
    //
    // We could value-number them by including the def's prior VN in the
    // key, but that requires tracking pre-def VNs which the current
    // scheme does not. Conservatively skip them.
    if has_tied_def_use(inst.opcode) {
        return None;
    }

    let result_class = inst.operands.first().and_then(|op| op.as_vreg())?.class;

    // Source operands start at index 1 (operand[0] is the def).
    let mut op_vns = Vec::with_capacity(inst.operands.len() - 1);
    for op in &inst.operands[1..] {
        {
            let vn = operand_vn(op, table, def_counts, imm_vns, fimm_vns, alloc)?;
            op_vns.push(vn)
        }
    }

    // Canonicalize commutative operations.
    if is_commutative(inst.opcode) && op_vns.len() == 2 && op_vns[0] > op_vns[1] {
        op_vns.swap(0, 1);
    }

    Some(VNExprKey {
        opcode: inst.opcode,
        result_class,
        operand_vns: op_vns,
    })
}

/// Build a load key for a load instruction.
///
/// Load instructions typically have the form: `def, base, offset`.
/// Returns `None` if the operands don't match this pattern.
fn make_load_key(
    inst: &trust_cg_ir::MachInst,
    table: &mut ScopedValueTable,
    def_counts: &HashMap<VReg, u32>,
    imm_vns: &mut HashMap<i64, ValNum>,
    fimm_vns: &mut HashMap<u64, ValNum>,
    alloc: &mut ValNumAllocator,
) -> Option<LoadKey> {
    if has_non_primary_def(inst) {
        return None;
    }

    // Expect at least: def, base, offset
    if inst.operands.len() < 3 {
        return None;
    }

    let result_class = inst.operands.first().and_then(|op| op.as_vreg())?.class;

    // Base register (operand[1]) must be a VReg.
    let base_vn = operand_vn(
        &inst.operands[1],
        table,
        def_counts,
        imm_vns,
        fimm_vns,
        alloc,
    )?;

    // Offset (operand[2]) must be an immediate.
    let offset = match &inst.operands[2] {
        MachOperand::Imm(i) => *i,
        _ => return None,
    };

    Some(LoadKey {
        opcode: inst.opcode,
        result_class,
        base_vn,
        offset,
    })
}

fn make_store_access(
    inst: &trust_cg_ir::MachInst,
    table: &mut ScopedValueTable,
    def_counts: &HashMap<VReg, u32>,
    imm_vns: &mut HashMap<i64, ValNum>,
    fimm_vns: &mut HashMap<u64, ValNum>,
    alloc: &mut ValNumAllocator,
) -> Option<StoreAccess> {
    let (base_idx, offset_idx) = store_address_operand_indices(inst.opcode)?;
    if inst.operands.len() <= offset_idx {
        return None;
    }

    let base_vn = operand_vn(
        &inst.operands[base_idx],
        table,
        def_counts,
        imm_vns,
        fimm_vns,
        alloc,
    )?;

    let offset = match &inst.operands[offset_idx] {
        MachOperand::Imm(i) => *i,
        _ => return None,
    };

    Some(StoreAccess {
        base_vn,
        offset,
        size: store_access_size(inst)?,
    })
}

fn store_address_operand_indices(opcode: AArch64Opcode) -> Option<(usize, usize)> {
    use AArch64Opcode::*;

    match opcode {
        StrRI | StrbRI | StrhRI | STRWui | STRXui | STRSui | STRDui => Some((1, 2)),
        StpRI => Some((2, 3)),
        _ => None,
    }
}

fn store_access_size(inst: &trust_cg_ir::MachInst) -> Option<i64> {
    use AArch64Opcode::*;

    match inst.opcode {
        StrbRI => Some(1),
        StrhRI => Some(2),
        StrRI => transfer_operand_size(inst.operands.first()?),
        STRWui | STRSui => Some(4),
        STRXui | STRDui => Some(8),
        StpRI => pair_transfer_operand_size(inst.operands.first()?),
        _ => None,
    }
}

fn transfer_operand_size(op: &MachOperand) -> Option<i64> {
    match op {
        MachOperand::VReg(vreg) => Some(i64::from(vreg.class.size_bytes())),
        MachOperand::PReg(reg) => Some(i64::from(preg_class(*reg).size_bytes())),
        _ => None,
    }
}

fn pair_transfer_operand_size(op: &MachOperand) -> Option<i64> {
    transfer_operand_size(op)?.checked_mul(2)
}

fn load_access_size(load_key: &LoadKey) -> Option<i64> {
    use AArch64Opcode::*;

    match load_key.opcode {
        LdrbRI | LdrsbRI => Some(1),
        LdrhRI | LdrshRI => Some(2),
        LdrRI | LdrLiteral => Some(i64::from(load_key.result_class.size_bytes())),
        LdpRI => Some(i64::from(load_key.result_class.size_bytes()) * 2),
        _ => None,
    }
}

fn byte_ranges_overlap(
    left_offset: i64,
    left_size: i64,
    right_offset: i64,
    right_size: i64,
) -> bool {
    if left_size <= 0 || right_size <= 0 {
        return true;
    }

    let Some(left_end) = left_offset.checked_add(left_size) else {
        return true;
    };
    let Some(right_end) = right_offset.checked_add(right_size) else {
        return true;
    };

    left_offset < right_end && right_offset < left_end
}

fn make_proof_dependent_load_elimination_certificate(
    func: &MachFunction,
    elimination: ProofDependentLoadElimination,
) -> OptCertificate {
    let transform = OptTransformIdentity {
        name: GVN_PROOF_LOAD_ELIM_TRANSFORM.to_string(),
        version: GVN_PROOF_LOAD_ELIM_VERSION,
    };
    let route = OptAdmissionRoute {
        pass: "gvn".to_string(),
        admission: GVN_PROOF_LOAD_ELIM_ADMISSION.to_string(),
    };
    let kind = OptCertificateKind::PairEliminated;
    let consumed_fact_count = 1 + elimination.proof_reorderable_store_insts.len();
    let consumed_facts = vec![
        OptConsumedProofFact::LegacyAnnotation(ProofAnnotation::ValidBorrow);
        consumed_fact_count
    ];
    let mut target_region = Vec::with_capacity(1 + elimination.proof_reorderable_store_insts.len());
    target_region.push(elimination.leader_inst);
    target_region.extend(elimination.proof_reorderable_store_insts.iter().copied());
    let target_region_hash = gvn_region_hash(func, &target_region);
    let proof_hash = gvn_valid_borrow_proof_hash(consumed_fact_count);
    let validation_hash = gvn_validation_hash(
        &transform,
        &route,
        &kind,
        elimination.source_region_hash,
        target_region_hash,
        proof_hash,
    );
    let certificate_id = gvn_certificate_id(
        &transform,
        elimination.source_region_hash,
        target_region_hash,
        proof_hash,
        validation_hash,
    );
    let mut affected_insts = Vec::with_capacity(target_region.len());
    affected_insts.push(elimination.leader_inst);
    affected_insts.extend(elimination.proof_reorderable_store_insts.iter().copied());

    OptCertificate {
        certificate_id,
        transform,
        route,
        annotation: Some(ProofAnnotation::ValidBorrow),
        consumed_facts,
        description: format!(
            "GVN eliminated {} by reusing {} across {} proof-reorderable store(s)",
            elimination.eliminated_inst,
            elimination.leader_inst,
            elimination.proof_reorderable_store_insts.len()
        ),
        primary_inst: elimination.eliminated_inst,
        affected_insts,
        kind,
        source_region_hash: elimination.source_region_hash,
        target_region_hash,
        proof_hash,
        validation_hash,
        rejection: None,
    }
}

fn gvn_region_hash(func: &MachFunction, inst_ids: &[InstId]) -> u128 {
    let mut h = StableHasher::new();
    h.write_str("proof-opts.region.v2");
    h.write_str(&func.name);
    h.write_u64(inst_ids.len() as u64);
    for inst_id in inst_ids {
        gvn_hash_inst(&mut h, func.inst(*inst_id));
    }
    h.finish128()
}

fn gvn_hash_inst(h: &mut StableHasher, inst: &MachInst) {
    h.write_str("mach-inst.v1");
    h.write_str(&format!("{:?}", inst.opcode));
    h.write_u64(u64::from(inst.flags.bits()));
    gvn_hash_optional_annotation(h, inst.proof);

    h.write_u64(inst.operands.len() as u64);
    for operand in &inst.operands {
        gvn_hash_operand(h, operand);
    }

    h.write_u64(inst.implicit_defs.len() as u64);
    for reg in inst.implicit_defs {
        h.write_u64(u64::from(reg.encoding()));
    }

    h.write_u64(inst.implicit_uses.len() as u64);
    for reg in inst.implicit_uses {
        h.write_u64(u64::from(reg.encoding()));
    }

    match inst.source_loc {
        Some(loc) => {
            h.write_u8(1);
            h.write_u32(loc.file);
            h.write_u32(loc.line);
            h.write_u32(loc.col);
        }
        None => h.write_u8(0),
    }
}

fn gvn_hash_operand(h: &mut StableHasher, operand: &MachOperand) {
    match operand {
        MachOperand::VReg(vreg) => {
            h.write_u8(0);
            h.write_u32(vreg.id);
            gvn_hash_reg_class(h, vreg.class);
        }
        MachOperand::PReg(reg) => {
            h.write_u8(1);
            h.write_u64(u64::from(reg.encoding()));
        }
        MachOperand::Imm(value) => {
            h.write_u8(2);
            h.write(&value.to_le_bytes());
        }
        MachOperand::FImm(value) => {
            h.write_u8(3);
            h.write_u64(value.to_bits());
        }
        MachOperand::Block(block) => {
            h.write_u8(4);
            h.write_u32(block.0);
        }
        MachOperand::StackSlot(slot) => {
            h.write_u8(5);
            h.write_u32(slot.0);
        }
        MachOperand::FrameIndex(frame) => {
            h.write_u8(6);
            h.write(&frame.0.to_le_bytes());
        }
        MachOperand::MemOp { base, offset } => {
            h.write_u8(7);
            h.write_u64(u64::from(base.encoding()));
            h.write(&offset.to_le_bytes());
        }
        MachOperand::Special(reg) => {
            h.write_u8(8);
            gvn_hash_special_reg(h, *reg);
        }
        MachOperand::Symbol(symbol) => {
            h.write_u8(9);
            h.write_str(symbol);
        }
        MachOperand::JumpTableIndex(index) => {
            h.write_u8(10);
            h.write_u32(*index);
        }
        MachOperand::IncomingArg(offset) => {
            h.write_u8(11);
            h.write(&offset.to_le_bytes());
        }
    }
}

fn gvn_hash_reg_class(h: &mut StableHasher, class: RegClass) {
    let tag = match class {
        RegClass::Gpr64 => 0,
        RegClass::Gpr32 => 1,
        RegClass::Fpr128 => 2,
        RegClass::Fpr64 => 3,
        RegClass::Fpr32 => 4,
        RegClass::Fpr16 => 5,
        RegClass::Fpr8 => 6,
        RegClass::System => 7,
    };
    h.write_u8(tag);
}

fn gvn_hash_special_reg(h: &mut StableHasher, reg: SpecialReg) {
    let tag = match reg {
        SpecialReg::SP => 0,
        SpecialReg::XZR => 1,
        SpecialReg::WZR => 2,
    };
    h.write_u8(tag);
}

fn gvn_hash_optional_annotation(h: &mut StableHasher, annotation: Option<ProofAnnotation>) {
    match annotation {
        Some(annotation) => {
            h.write_u8(1);
            h.write_str(gvn_proof_annotation_stable_name(annotation));
        }
        None => h.write_u8(0),
    }
}

fn gvn_proof_annotation_stable_name(annotation: ProofAnnotation) -> &'static str {
    match annotation {
        ProofAnnotation::NoOverflow => "NoOverflow",
        ProofAnnotation::NoSignedOverflow => "NoSignedOverflow",
        ProofAnnotation::NoUnsignedOverflow => "NoUnsignedOverflow",
        ProofAnnotation::InBounds => "InBounds",
        ProofAnnotation::NotNull => "NotNull",
        ProofAnnotation::ValidBorrow => "ValidBorrow",
        ProofAnnotation::PositiveRefCount => "PositiveRefCount",
        ProofAnnotation::NonZeroDivisor => "NonZeroDivisor",
        ProofAnnotation::ValidShift => "ValidShift",
        ProofAnnotation::Pure => "Pure",
        ProofAnnotation::Associative => "Associative",
        ProofAnnotation::Commutative => "Commutative",
        ProofAnnotation::Idempotent => "Idempotent",
    }
}

fn gvn_valid_borrow_proof_hash(consumed_fact_count: usize) -> u128 {
    let mut h = StableHasher::new();
    h.write_str("proof-opts.proof.v1");
    h.write_str(gvn_proof_annotation_stable_name(
        ProofAnnotation::ValidBorrow,
    ));
    h.write_u64(consumed_fact_count as u64);
    for _ in 0..consumed_fact_count {
        h.write_u8(0);
        h.write_str(gvn_proof_annotation_stable_name(
            ProofAnnotation::ValidBorrow,
        ));
    }
    h.finish128()
}

fn gvn_validation_hash(
    transform: &OptTransformIdentity,
    route: &OptAdmissionRoute,
    kind: &OptCertificateKind,
    source_region_hash: u128,
    target_region_hash: u128,
    proof_hash: u128,
) -> u128 {
    let mut h = StableHasher::new();
    h.write_str("proof-opts.validation.v2");
    h.write_str(&transform.name);
    h.write_u32(transform.version);
    h.write_str(&route.pass);
    h.write_str(&route.admission);
    gvn_hash_certificate_kind(&mut h, kind);
    gvn_write_u128(&mut h, source_region_hash);
    gvn_write_u128(&mut h, target_region_hash);
    gvn_write_u128(&mut h, proof_hash);
    h.write_u8(0);
    h.finish128()
}

fn gvn_certificate_id(
    transform: &OptTransformIdentity,
    source_region_hash: u128,
    target_region_hash: u128,
    proof_hash: u128,
    validation_hash: u128,
) -> u128 {
    let mut h = StableHasher::new();
    h.write_str("proof-opts.certificate-id.v2");
    h.write_str(&transform.name);
    h.write_u32(transform.version);
    gvn_write_u128(&mut h, source_region_hash);
    gvn_write_u128(&mut h, target_region_hash);
    gvn_write_u128(&mut h, proof_hash);
    gvn_write_u128(&mut h, validation_hash);
    h.finish128()
}

fn gvn_hash_certificate_kind(h: &mut StableHasher, kind: &OptCertificateKind) {
    let stable = match kind {
        OptCertificateKind::CheckedToUnchecked => "checked-to-unchecked",
        OptCertificateKind::GuardEliminated => "guard-eliminated",
        OptCertificateKind::BranchSimplified => "branch-simplified",
        OptCertificateKind::FlagsRefined => "flags-refined",
        OptCertificateKind::PairEliminated => "pair-eliminated",
        OptCertificateKind::PairCombined => "pair-combined",
    };
    h.write_str(stable);
}

fn gvn_write_u128(h: &mut StableHasher, value: u128) {
    h.write(&value.to_le_bytes());
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pass_manager::{AnalysisCache, MachinePass, PassManager};
    use crate::proof_opts::OptConsumedProofFact;
    use trust_cg_ir::{
        AArch64Opcode, InstFlags, InstId, MachFunction, MachInst, MachOperand, ProofAnnotation,
        ProvenanceMap, RegClass, Signature, TransformKind, TrustIrInstId, VReg,
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

    fn proof_reorderable(mut inst: MachInst) -> MachInst {
        inst.flags.insert(InstFlags::PROOF_REORDERABLE);
        inst
    }

    fn make_func_with_insts(insts: Vec<MachInst>) -> MachFunction {
        let mut func = MachFunction::new("test_gvn".to_string(), Signature::new(vec![], vec![]));
        let block = func.entry;
        for inst in insts {
            let id = func.push_inst(inst);
            func.append_inst(block, id);
        }
        func
    }

    // ---- Basic value numbering tests ----

    #[test]
    fn test_gvn_identical_adds() {
        // v2 = add v0, v1
        // v3 = add v0, v1   -> eliminated, v3 replaced with v2
        // v4 = sub v3, #1   -> v4 = sub v2, #1
        // ret
        let a1 = MachInst::new(AArch64Opcode::AddRR, vec![vreg(2), vreg(0), vreg(1)]);
        let a2 = MachInst::new(AArch64Opcode::AddRR, vec![vreg(3), vreg(0), vreg(1)]);
        let sub = MachInst::new(AArch64Opcode::SubRI, vec![vreg(4), vreg(3), imm(1)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![a1, a2, sub, ret]);

        let mut gvn = GlobalValueNumbering;
        assert!(gvn.run(&mut func));

        // a2 should be removed
        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 3); // a1, sub, ret

        // sub should now use v2 instead of v3
        let sub_inst = func.inst(block.insts[1]);
        assert_eq!(sub_inst.operands[1], vreg(2));
    }

    #[test]
    fn test_gvn_provenance_merges_redundant_expression_into_leader() {
        let a1 = MachInst::new(AArch64Opcode::AddRR, vec![vreg(2), vreg(0), vreg(1)]);
        let a2 = MachInst::new(AArch64Opcode::AddRR, vec![vreg(3), vreg(0), vreg(1)]);
        let sub = MachInst::new(AArch64Opcode::SubRI, vec![vreg(4), vreg(3), imm(1)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![a1, a2, sub, ret]);
        let leader_id = func.block(func.entry).insts[0];
        let eliminated_id = func.block(func.entry).insts[1];
        let sub_id = func.block(func.entry).insts[2];
        let ret_id = func.block(func.entry).insts[3];

        let mut provenance = ProvenanceMap::new();
        provenance.record_lowering(TrustIrInstId(40), &[leader_id], PassId::new("isel"));
        provenance.record_lowering(TrustIrInstId(41), &[eliminated_id], PassId::new("isel"));
        provenance.record_lowering(TrustIrInstId(42), &[sub_id], PassId::new("isel"));
        provenance.record_lowering(TrustIrInstId(43), &[ret_id], PassId::new("isel"));

        let mut gvn = GlobalValueNumbering;
        let mut analyses = AnalysisCache::new();
        assert!(gvn.run_with_analyses_and_provenance(&mut func, &mut analyses, &mut provenance));

        let block = func.block(func.entry);
        assert_eq!(block.insts, vec![leader_id, sub_id, ret_id]);
        assert_eq!(func.inst(sub_id).operands[1], vreg(2));

        let leader_entry = provenance
            .get_entry(leader_id)
            .expect("surviving leader provenance");
        assert!(leader_entry.trust_ir_origins.contains(&TrustIrInstId(40)));
        assert!(leader_entry.trust_ir_origins.contains(&TrustIrInstId(41)));
        assert!(leader_entry.is_active());
        let transform = leader_entry.transforms.last().unwrap();
        assert_eq!(transform.pass, PassId::new("gvn"));
        assert_eq!(
            transform.kind,
            TransformKind::Merged {
                sources: vec![leader_id, eliminated_id],
            }
        );

        assert!(provenance.get_entry(eliminated_id).is_none());
        assert_eq!(
            provenance.get_mach_insts(TrustIrInstId(40)).unwrap(),
            &[leader_id]
        );
        assert_eq!(
            provenance.get_mach_insts(TrustIrInstId(41)).unwrap(),
            &[leader_id]
        );
        assert_eq!(provenance.get_entry(sub_id).unwrap().transforms.len(), 1);
        assert_eq!(provenance.get_entry(ret_id).unwrap().transforms.len(), 1);
    }

    #[test]
    fn test_gvn_commutative() {
        // v2 = add v0, v1
        // v3 = add v1, v0   -> eliminated (commutative)
        // ret
        let a1 = MachInst::new(AArch64Opcode::AddRR, vec![vreg(2), vreg(0), vreg(1)]);
        let a2 = MachInst::new(AArch64Opcode::AddRR, vec![vreg(3), vreg(1), vreg(0)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![a1, a2, ret]);

        let mut gvn = GlobalValueNumbering;
        assert!(gvn.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 2); // a1, ret
    }

    #[test]
    fn test_gvn_non_commutative() {
        // v2 = sub v0, v1
        // v3 = sub v1, v0   -> NOT eliminated (sub is not commutative)
        // ret
        let s1 = MachInst::new(AArch64Opcode::SubRR, vec![vreg(2), vreg(0), vreg(1)]);
        let s2 = MachInst::new(AArch64Opcode::SubRR, vec![vreg(3), vreg(1), vreg(0)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![s1, s2, ret]);

        let mut gvn = GlobalValueNumbering;
        assert!(!gvn.run(&mut func));
    }

    #[test]
    fn test_gvn_different_operands() {
        // v2 = add v0, v1
        // v3 = add v0, v4   -> different operands, not eliminated
        // ret
        let a1 = MachInst::new(AArch64Opcode::AddRR, vec![vreg(2), vreg(0), vreg(1)]);
        let a2 = MachInst::new(AArch64Opcode::AddRR, vec![vreg(3), vreg(0), vreg(4)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![a1, a2, ret]);

        let mut gvn = GlobalValueNumbering;
        assert!(!gvn.run(&mut func));
    }

    #[test]
    fn test_gvn_different_opcodes() {
        // v2 = add v0, v1
        // v3 = sub v0, v1   -> different opcode
        // ret
        let a1 = MachInst::new(AArch64Opcode::AddRR, vec![vreg(2), vreg(0), vreg(1)]);
        let s1 = MachInst::new(AArch64Opcode::SubRR, vec![vreg(3), vreg(0), vreg(1)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![a1, s1, ret]);

        let mut gvn = GlobalValueNumbering;
        assert!(!gvn.run(&mut func));
    }

    #[test]
    fn test_gvn_immediate_operands() {
        // v1 = add v0, #5
        // v2 = add v0, #5   -> eliminated
        // ret
        let a1 = MachInst::new(AArch64Opcode::AddRI, vec![vreg(1), vreg(0), imm(5)]);
        let a2 = MachInst::new(AArch64Opcode::AddRI, vec![vreg(2), vreg(0), imm(5)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![a1, a2, ret]);

        let mut gvn = GlobalValueNumbering;
        assert!(gvn.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 2); // a1, ret
    }

    #[test]
    fn test_gvn_keeps_same_immediate_different_result_class() {
        let mov64 = MachInst::new(AArch64Opcode::Movz, vec![vreg(1), imm(1)]);
        let mov32 = MachInst::new(
            AArch64Opcode::Movz,
            vec![vreg_class(2, RegClass::Gpr32), imm(1)],
        );
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![mov64, mov32, ret]);

        let mut gvn = GlobalValueNumbering;
        assert!(
            !gvn.run(&mut func),
            "GVN must not replace a Gpr32 value with a Gpr64 leader"
        );
    }

    #[test]
    fn test_gvn_keeps_same_load_address_different_result_class() {
        let load64 = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(1), vreg(0), imm(0)]);
        let load32 = MachInst::new(
            AArch64Opcode::LdrRI,
            vec![vreg_class(2, RegClass::Gpr32), vreg(0), imm(0)],
        );
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![load64, load32, ret]);

        let mut gvn = GlobalValueNumbering;
        assert!(
            !gvn.run(&mut func),
            "GVN must not replace a 32-bit load with a 64-bit load"
        );
    }

    #[test]
    fn test_gvn_same_id_different_class_def_does_not_block_same_class_elim() {
        let other_class_def = MachInst::new(
            AArch64Opcode::AddRR,
            vec![
                vreg_class(2, RegClass::Gpr32),
                vreg_class(0, RegClass::Gpr32),
                vreg_class(1, RegClass::Gpr32),
            ],
        );
        let leader = MachInst::new(AArch64Opcode::AddRR, vec![vreg(2), vreg(0), vreg(1)]);
        let redundant = MachInst::new(AArch64Opcode::AddRR, vec![vreg(3), vreg(0), vreg(1)]);
        let use_redundant = MachInst::new(AArch64Opcode::SubRI, vec![vreg(4), vreg(3), imm(1)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func =
            make_func_with_insts(vec![other_class_def, leader, redundant, use_redundant, ret]);

        let mut gvn = GlobalValueNumbering;
        assert!(
            gvn.run(&mut func),
            "same numeric id in another class must not make the Gpr64 leader look multi-defined"
        );

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 4);
        let sub_inst = func.inst(block.insts[2]);
        assert_eq!(sub_inst.operands[1], vreg(2));
    }

    #[test]
    fn test_gvn_replacement_does_not_rewrite_same_id_different_class_use() {
        let leader = MachInst::new(AArch64Opcode::AddRR, vec![vreg(2), vreg(0), vreg(1)]);
        let redundant = MachInst::new(AArch64Opcode::AddRR, vec![vreg(3), vreg(0), vreg(1)]);
        let other_class_use = MachInst::new(
            AArch64Opcode::AddRR,
            vec![
                vreg_class(4, RegClass::Gpr32),
                vreg_class(3, RegClass::Gpr32),
                vreg_class(5, RegClass::Gpr32),
            ],
        );
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![leader, redundant, other_class_use, ret]);

        let mut gvn = GlobalValueNumbering;
        assert!(gvn.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 3);
        let use_inst = func.inst(block.insts[1]);
        assert_eq!(use_inst.operands[1], vreg_class(3, RegClass::Gpr32));
    }

    #[test]
    fn test_gvn_mul_commutative() {
        // v2 = mul v0, v1
        // v3 = mul v1, v0   -> eliminated (commutative)
        let m1 = MachInst::new(AArch64Opcode::MulRR, vec![vreg(2), vreg(0), vreg(1)]);
        let m2 = MachInst::new(AArch64Opcode::MulRR, vec![vreg(3), vreg(1), vreg(0)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![m1, m2, ret]);

        let mut gvn = GlobalValueNumbering;
        assert!(gvn.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 2); // m1, ret
    }

    #[test]
    fn test_gvn_does_not_eliminate_flag_writing_checked_arithmetic() {
        // ADDS produces a register value and writes NZCV. The value may match
        // an earlier ADDS, but the later flag write is observable by the next
        // flag reader and must not be value-numbered away.
        let a1 = MachInst::new(AArch64Opcode::AddsRR, vec![vreg(2), vreg(0), vreg(1)]);
        let a2 = MachInst::new(AArch64Opcode::AddsRR, vec![vreg(3), vreg(0), vreg(1)]);
        let use_second = MachInst::new(AArch64Opcode::AddRR, vec![vreg(4), vreg(3), vreg(0)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![a1, a2, use_second, ret]);

        let mut gvn = GlobalValueNumbering;
        assert!(
            !gvn.run(&mut func),
            "GVN must not remove flag-writing ADDS/SUBS instructions"
        );

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 4);
        let use_inst = func.inst(block.insts[2]);
        assert_eq!(use_inst.operands[1], vreg(3));
    }

    // ---- Dominator-based tests ----

    #[test]
    fn test_gvn_dominator_based() {
        // Diamond CFG:
        //   bb0: v2 = add v0, v1
        //   bb1: v3 = add v0, v1  -> eliminated (bb0 dominates bb1)
        //   bb2: v4 = add v0, v1  -> eliminated (bb0 dominates bb2)
        //   bb3: ret
        let mut func =
            MachFunction::new("test_gvn_dom".to_string(), Signature::new(vec![], vec![]));
        let bb0 = func.entry;
        let bb1 = func.create_block();
        let bb2 = func.create_block();
        let bb3 = func.create_block();

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

        let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb3, ret);

        func.add_edge(bb0, bb1);
        func.add_edge(bb0, bb2);
        func.add_edge(bb1, bb3);
        func.add_edge(bb2, bb3);

        let mut gvn = GlobalValueNumbering;
        assert!(gvn.run(&mut func));

        // bb1 and bb2 should have their adds removed.
        assert_eq!(func.block(bb1).insts.len(), 1); // just branch
        assert_eq!(func.block(bb2).insts.len(), 1); // just branch
    }

    #[test]
    fn test_gvn_no_domination() {
        // Diamond: bb1 has add, bb2 has same add.
        // Neither bb1 nor bb2 dominates the other -> no elimination.
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

        let mut gvn = GlobalValueNumbering;
        assert!(!gvn.run(&mut func));

        // Both adds should remain.
        assert_eq!(func.block(bb1).insts.len(), 2);
        assert_eq!(func.block(bb2).insts.len(), 2);
    }

    #[test]
    fn test_gvn_does_not_replace_multi_def_join_vreg() {
        // Diamond CFG with non-SSA vreg reuse:
        //   bb1: v2 = add v0, v1
        //        v5 = add v0, v1   (locally redundant with v2)
        //   bb2: v5 = sub v0, v1   (same vreg id, different reaching def)
        //   bb3: v6 = mul v5, v1
        //
        // ISel reuses the same vreg id for block-parameter copies across
        // predecessor edges, so machine IR is not in SSA form. GVN must not
        // eliminate bb1's v5 and globally rewrite bb3's use of v5 -> v2.
        let mut func = MachFunction::new(
            "test_multi_def_join_vreg".to_string(),
            Signature::new(vec![], vec![]),
        );
        let bb0 = func.entry;
        let bb1 = func.create_block();
        let bb2 = func.create_block();
        let bb3 = func.create_block();

        let br0 = func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![MachOperand::Block(bb1), MachOperand::Block(bb2)],
        ));
        func.append_inst(bb0, br0);

        let bb1_leader = func.push_inst(MachInst::new(
            AArch64Opcode::AddRR,
            vec![vreg(2), vreg(0), vreg(1)],
        ));
        func.append_inst(bb1, bb1_leader);
        let bb1_redundant = func.push_inst(MachInst::new(
            AArch64Opcode::AddRR,
            vec![vreg(5), vreg(0), vreg(1)],
        ));
        func.append_inst(bb1, bb1_redundant);
        let br1 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb3)],
        ));
        func.append_inst(bb1, br1);

        let bb2_def = func.push_inst(MachInst::new(
            AArch64Opcode::SubRR,
            vec![vreg(5), vreg(0), vreg(1)],
        ));
        func.append_inst(bb2, bb2_def);
        let br2 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb3)],
        ));
        func.append_inst(bb2, br2);

        let join_use = func.push_inst(MachInst::new(
            AArch64Opcode::MulRR,
            vec![vreg(6), vreg(5), vreg(1)],
        ));
        func.append_inst(bb3, join_use);
        let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb3, ret);

        func.add_edge(bb0, bb1);
        func.add_edge(bb0, bb2);
        func.add_edge(bb1, bb3);
        func.add_edge(bb2, bb3);

        let mut gvn = GlobalValueNumbering;
        assert!(!gvn.run(&mut func));

        // bb1's locally redundant v5 must not be deleted.
        assert_eq!(func.block(bb1).insts.len(), 3);

        // The join must keep using the block-parameter vreg, not bb1's leader.
        let join_inst = func.inst(func.block(bb3).insts[0]);
        assert_eq!(join_inst.operands[1], vreg(5));
    }

    #[test]
    fn test_gvn_does_not_rewrite_across_later_redefinition() {
        // Single-block non-SSA reuse:
        //   v2 = add v0, v1
        //   v5 = add v0, v1   (would be redundant in SSA)
        //   v5 = sub v0, v1   (later redefinition, same bare vreg id)
        //   v6 = mul v5, v1
        //
        // The replacement map is keyed by bare vreg id, so eliminating the
        // second instruction would stale-rewrite the later use after the sub.
        // Any vreg with multiple definitions must be excluded from GVN
        // replacement, even when the first candidate looks locally redundant.
        let a1 = MachInst::new(AArch64Opcode::AddRR, vec![vreg(2), vreg(0), vreg(1)]);
        let would_be_redundant =
            MachInst::new(AArch64Opcode::AddRR, vec![vreg(5), vreg(0), vreg(1)]);
        let redef = MachInst::new(AArch64Opcode::SubRR, vec![vreg(5), vreg(0), vreg(1)]);
        let use_after_redef = MachInst::new(AArch64Opcode::MulRR, vec![vreg(6), vreg(5), vreg(1)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func =
            make_func_with_insts(vec![a1, would_be_redundant, redef, use_after_redef, ret]);

        let mut gvn = GlobalValueNumbering;
        assert!(!gvn.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 5);
        let use_inst = func.inst(block.insts[3]);
        assert_eq!(use_inst.operands[1], vreg(5));
    }

    // ---- Load value numbering tests ----

    #[test]
    fn test_gvn_load_value_numbering() {
        // v2 = ldr v0, #8
        // v3 = ldr v0, #8   -> eliminated (same load, no intervening store)
        // ret
        let l1 = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(2), vreg(0), imm(8)]);
        let l2 = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(3), vreg(0), imm(8)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![l1, l2, ret]);

        let mut gvn = GlobalValueNumbering;
        assert!(gvn.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 2); // l1, ret
    }

    #[test]
    fn test_gvn_does_not_eliminate_scalar_writeback_loads() {
        // Both write back v0. Even with identical operands, deleting either
        // instruction would drop an observable base-register update.
        let l1 = MachInst::new(AArch64Opcode::LdrPostIndex, vec![vreg(2), vreg(0), imm(8)]);
        let l2 = MachInst::new(AArch64Opcode::LdrPostIndex, vec![vreg(3), vreg(0), imm(8)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![l1, l2, ret]);

        let mut gvn = GlobalValueNumbering;
        assert!(!gvn.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 3);
        assert_eq!(
            func.inst(block.insts[0]).opcode,
            AArch64Opcode::LdrPostIndex
        );
        assert_eq!(
            func.inst(block.insts[1]).opcode,
            AArch64Opcode::LdrPostIndex
        );
    }

    #[test]
    fn test_gvn_scalar_writeback_load_refreshes_base_value_number() {
        // v2 = ldr v0, #0
        // v3 = ldr-post v0, #8   (updates v0)
        // v4 = ldr v0, #0        -> must observe the updated base
        let l1 = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(2), vreg(0), imm(0)]);
        let writeback = MachInst::new(AArch64Opcode::LdrPostIndex, vec![vreg(3), vreg(0), imm(8)]);
        let l2 = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(4), vreg(0), imm(0)]);
        let use_l2 = MachInst::new(AArch64Opcode::AddRR, vec![vreg(5), vreg(4), vreg(1)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![l1, writeback, l2, use_l2, ret]);

        let mut gvn = GlobalValueNumbering;
        assert!(!gvn.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 5);
        let use_inst = func.inst(block.insts[3]);
        assert_eq!(use_inst.operands[1], vreg(4));
    }

    #[test]
    fn test_gvn_scalar_writeback_store_refreshes_base_value_number() {
        // v2 = add v0, #1
        // str-post v5, v0, #8    (updates v0)
        // v3 = add v0, #1        -> must not reuse the stale pre-writeback VN
        let a1 = MachInst::new(AArch64Opcode::AddRI, vec![vreg(2), vreg(0), imm(1)]);
        let writeback = MachInst::new(AArch64Opcode::StrPostIndex, vec![vreg(5), vreg(0), imm(8)]);
        let a2 = MachInst::new(AArch64Opcode::AddRI, vec![vreg(3), vreg(0), imm(1)]);
        let use_a2 = MachInst::new(AArch64Opcode::MulRR, vec![vreg(6), vreg(3), vreg(1)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![a1, writeback, a2, use_a2, ret]);

        let mut gvn = GlobalValueNumbering;
        assert!(!gvn.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 5);
        let use_inst = func.inst(block.insts[3]);
        assert_eq!(use_inst.operands[1], vreg(3));
    }

    #[test]
    fn test_gvn_load_killed_by_store() {
        // v2 = ldr v0, #8
        // str v5, v0, #8   (store to same address)
        // v3 = ldr v0, #8   -> NOT eliminated (store kills loads)
        // ret
        let l1 = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(2), vreg(0), imm(8)]);
        let st = MachInst::new(AArch64Opcode::StrRI, vec![vreg(5), vreg(0), imm(8)]);
        let l2 = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(3), vreg(0), imm(8)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![l1, st, l2, ret]);

        let mut gvn = GlobalValueNumbering;
        assert!(!gvn.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 4); // all remain
    }

    #[test]
    fn test_gvn_proof_reorderable_store_preserves_proven_load() {
        // v2 = ldr v0, #8  [PROOF_REORDERABLE]
        // str v5, v1, #16 [PROOF_REORDERABLE]
        // v3 = ldr v0, #8  -> eliminated across the proven store
        // v4 = add v3, v6  -> v4 = add v2, v6
        // ret
        let l1 = proof_reorderable(MachInst::new(
            AArch64Opcode::LdrRI,
            vec![vreg(2), vreg(0), imm(8)],
        ));
        let st = proof_reorderable(MachInst::new(
            AArch64Opcode::StrRI,
            vec![vreg(5), vreg(1), imm(16)],
        ));
        let l2 = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(3), vreg(0), imm(8)]);
        let add = MachInst::new(AArch64Opcode::AddRR, vec![vreg(4), vreg(3), vreg(6)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![l1, st, l2, add, ret]);

        let mut gvn = GlobalValueNumbering;
        assert!(gvn.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 4); // l1, st, add, ret
        let add_inst = func.inst(block.insts[2]);
        assert_eq!(add_inst.operands[1], vreg(2));
    }

    #[test]
    fn test_gvn_proof_reorderable_store_kills_proven_load_same_address() {
        // v2 = ldr v0, #8  [PROOF_REORDERABLE]
        // str v5, v0, #8  [PROOF_REORDERABLE]
        // v3 = ldr v0, #8  -> NOT eliminated (store clobbers same address)
        // v4 = add v3, v6  -> must keep using v3
        // ret
        let l1 = proof_reorderable(MachInst::new(
            AArch64Opcode::LdrRI,
            vec![vreg(2), vreg(0), imm(8)],
        ));
        let st = proof_reorderable(MachInst::new(
            AArch64Opcode::StrRI,
            vec![vreg(5), vreg(0), imm(8)],
        ));
        let l2 = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(3), vreg(0), imm(8)]);
        let add = MachInst::new(AArch64Opcode::AddRR, vec![vreg(4), vreg(3), vreg(6)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![l1, st, l2, add, ret]);

        let mut gvn = GlobalValueNumbering;
        assert!(!gvn.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 5);
        let add_inst = func.inst(block.insts[3]);
        assert_eq!(add_inst.operands[1], vreg(3));
    }

    #[test]
    fn test_gvn_proof_reorderable_q_pair_store_kills_second_q_load() {
        // v2 = ldr q, [v0, #16]       [PROOF_REORDERABLE]
        // stp q, q, [v0, #0]          [PROOF_REORDERABLE]
        // v3 = ldr q, [v0, #16]       -> NOT eliminated
        //
        // A Q pair store at offset 0 writes 32 bytes. Treating every pair as
        // 16 bytes incorrectly makes the second qword lane look disjoint.
        let l1 = proof_reorderable(MachInst::new(
            AArch64Opcode::LdrRI,
            vec![vreg_class(2, RegClass::Fpr128), vreg(0), imm(16)],
        ));
        let st = proof_reorderable(MachInst::new(
            AArch64Opcode::StpRI,
            vec![
                vreg_class(5, RegClass::Fpr128),
                vreg_class(6, RegClass::Fpr128),
                vreg(0),
                imm(0),
            ],
        ));
        let l2 = MachInst::new(
            AArch64Opcode::LdrRI,
            vec![vreg_class(3, RegClass::Fpr128), vreg(0), imm(16)],
        );
        let add = MachInst::new(
            AArch64Opcode::FaddRR,
            vec![
                vreg_class(4, RegClass::Fpr128),
                vreg_class(3, RegClass::Fpr128),
                vreg_class(7, RegClass::Fpr128),
            ],
        );
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![l1, st, l2, add, ret]);

        let mut gvn = GlobalValueNumbering;
        assert!(!gvn.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 5);
        let add_inst = func.inst(block.insts[3]);
        assert_eq!(add_inst.operands[1], vreg_class(3, RegClass::Fpr128));
    }

    #[test]
    fn test_gvn_proof_reorderable_store_preserves_proven_load_different_offset() {
        // v2 = ldr v0, #8   [PROOF_REORDERABLE]
        // str v5, v0, #32  [PROOF_REORDERABLE]
        // v3 = ldr v0, #8   -> eliminated across the non-overlapping store
        // v4 = add v3, v6   -> v4 = add v2, v6
        // ret
        let l1 = proof_reorderable(MachInst::new(
            AArch64Opcode::LdrRI,
            vec![vreg(2), vreg(0), imm(8)],
        ));
        let st = proof_reorderable(MachInst::new(
            AArch64Opcode::StrRI,
            vec![vreg(5), vreg(0), imm(32)],
        ));
        let l2 = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(3), vreg(0), imm(8)]);
        let add = MachInst::new(AArch64Opcode::AddRR, vec![vreg(4), vreg(3), vreg(6)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![l1, st, l2, add, ret]);

        let mut gvn = GlobalValueNumbering;
        assert!(gvn.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 4); // l1, st, add, ret
        let add_inst = func.inst(block.insts[2]);
        assert_eq!(add_inst.operands[1], vreg(2));
    }

    #[test]
    fn test_gvn_proof_dependent_load_elimination_emits_certificate_and_stat() {
        // v2 = ldr v0, #8   [PROOF_REORDERABLE]
        // str v5, v0, #32  [PROOF_REORDERABLE]
        // v3 = ldr v0, #8   -> eliminated across the non-overlapping store
        // v4 = add v3, v6   -> v4 = add v2, v6
        //
        // The rewrite depends on the ValidBorrow-derived PROOF_REORDERABLE
        // flags because an ordinary store would kill the load table.
        let l1 = proof_reorderable(MachInst::new(
            AArch64Opcode::LdrRI,
            vec![vreg(2), vreg(0), imm(8)],
        ));
        let st = proof_reorderable(MachInst::new(
            AArch64Opcode::StrRI,
            vec![vreg(5), vreg(0), imm(32)],
        ));
        let l2 = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(3), vreg(0), imm(8)]);
        let add = MachInst::new(AArch64Opcode::AddRR, vec![vreg(4), vreg(3), vreg(6)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![l1, st, l2, add, ret]);

        let mut pm = PassManager::new().with_pass(Box::new(GlobalValueNumbering));
        let run_stats = pm.run_once_with_stats(&mut func);

        assert_eq!(run_stats.changes, 1);
        let gvn = GlobalValueNumbering;
        assert_eq!(gvn.stats().proof_reorderable_load_eliminations, 1);

        assert_eq!(run_stats.proof_optimization_certificates.len(), 1);
        let cert = &run_stats.proof_optimization_certificates[0];
        assert_eq!(cert.transform.name, GVN_PROOF_LOAD_ELIM_TRANSFORM);
        assert_eq!(cert.transform.version, GVN_PROOF_LOAD_ELIM_VERSION);
        assert_eq!(cert.route.pass, "gvn");
        assert_eq!(cert.route.admission, GVN_PROOF_LOAD_ELIM_ADMISSION);
        assert_eq!(cert.annotation, Some(ProofAnnotation::ValidBorrow));
        assert_eq!(
            cert.consumed_facts,
            vec![
                OptConsumedProofFact::LegacyAnnotation(ProofAnnotation::ValidBorrow),
                OptConsumedProofFact::LegacyAnnotation(ProofAnnotation::ValidBorrow),
            ]
        );
        assert_eq!(cert.primary_inst, InstId(2));
        assert_eq!(cert.affected_insts, vec![InstId(0), InstId(1)]);
        assert_eq!(cert.kind, OptCertificateKind::PairEliminated);
        assert!(cert.rejection.is_none());
        assert_ne!(cert.source_region_hash, cert.target_region_hash);

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 4);
        let add_inst = func.inst(block.insts[2]);
        assert_eq!(add_inst.operands[1], vreg(2));
    }

    #[test]
    fn test_gvn_ordinary_duplicate_load_elimination_emits_no_proof_evidence() {
        // v2 = ldr v0, #8
        // v3 = ldr v0, #8   -> eliminated, but no intervening proof-reorderable
        //                      store was crossed.
        // ret
        let l1 = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(2), vreg(0), imm(8)]);
        let l2 = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(3), vreg(0), imm(8)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![l1, l2, ret]);

        let mut pm = PassManager::new().with_pass(Box::new(GlobalValueNumbering));
        let run_stats = pm.run_once_with_stats(&mut func);

        assert_eq!(run_stats.changes, 1);
        let gvn = GlobalValueNumbering;
        assert_eq!(gvn.stats().proof_reorderable_load_eliminations, 0);
        assert!(run_stats.proof_optimization_certificates.is_empty());

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 2);
    }

    #[test]
    fn test_gvn_proof_reorderable_store_kills_unproven_load() {
        // v2 = ldr v0, #8
        // str v5, v1, #16 [PROOF_REORDERABLE]
        // v3 = ldr v0, #8  -> NOT eliminated (leader load lacks proof)
        // ret
        let l1 = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(2), vreg(0), imm(8)]);
        let st = proof_reorderable(MachInst::new(
            AArch64Opcode::StrRI,
            vec![vreg(5), vreg(1), imm(16)],
        ));
        let l2 = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(3), vreg(0), imm(8)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![l1, st, l2, ret]);

        let mut gvn = GlobalValueNumbering;
        assert!(!gvn.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 4);
    }

    #[test]
    fn test_gvn_unproven_store_kills_proven_load() {
        // v2 = ldr v0, #8  [PROOF_REORDERABLE]
        // str v5, v1, #16
        // v3 = ldr v0, #8  -> NOT eliminated (store lacks proof)
        // ret
        let l1 = proof_reorderable(MachInst::new(
            AArch64Opcode::LdrRI,
            vec![vreg(2), vreg(0), imm(8)],
        ));
        let st = MachInst::new(AArch64Opcode::StrRI, vec![vreg(5), vreg(1), imm(16)]);
        let l2 = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(3), vreg(0), imm(8)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![l1, st, l2, ret]);

        let mut gvn = GlobalValueNumbering;
        assert!(!gvn.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 4);
    }

    #[test]
    fn test_gvn_load_killed_by_call() {
        // v2 = ldr v0, #8
        // bl (call)
        // v3 = ldr v0, #8   -> NOT eliminated (call kills loads)
        // ret
        let l1 = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(2), vreg(0), imm(8)]);
        let call = MachInst::new(AArch64Opcode::Bl, vec![]);
        let l2 = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(3), vreg(0), imm(8)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![l1, call, l2, ret]);

        let mut gvn = GlobalValueNumbering;
        assert!(!gvn.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 4);
    }

    #[test]
    fn test_gvn_loads_different_addresses() {
        // v2 = ldr v0, #8
        // v3 = ldr v0, #16   -> different offset, not eliminated
        // ret
        let l1 = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(2), vreg(0), imm(8)]);
        let l2 = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(3), vreg(0), imm(16)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![l1, l2, ret]);

        let mut gvn = GlobalValueNumbering;
        assert!(!gvn.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 3);
    }

    #[test]
    fn test_gvn_load_store_different_addr_conservative() {
        // v2 = ldr v0, #8
        // str v5, v1, #16   (store to DIFFERENT address)
        // v3 = ldr v0, #8   -> still NOT eliminated (conservative: any store kills all loads)
        // ret
        let l1 = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(2), vreg(0), imm(8)]);
        let st = MachInst::new(AArch64Opcode::StrRI, vec![vreg(5), vreg(1), imm(16)]);
        let l2 = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(3), vreg(0), imm(8)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![l1, st, l2, ret]);

        let mut gvn = GlobalValueNumbering;
        assert!(!gvn.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 4);
    }

    #[test]
    fn test_gvn_does_not_reuse_preheader_load_in_loop_header() {
        let mut func = MachFunction::new(
            "test_loop_header_loads".to_string(),
            Signature::new(vec![], vec![]),
        );
        let preheader = func.entry;
        let header = func.create_block();
        let body = func.create_block();
        let exit = func.create_block();

        let pre_load = func.push_inst(MachInst::new(
            AArch64Opcode::LdrRI,
            vec![vreg(2), vreg(0), imm(8)],
        ));
        func.append_inst(preheader, pre_load);
        let pre_br = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(header)],
        ));
        func.append_inst(preheader, pre_br);

        let header_load = func.push_inst(MachInst::new(
            AArch64Opcode::LdrRI,
            vec![vreg(3), vreg(0), imm(8)],
        ));
        func.append_inst(header, header_load);
        let header_br = func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![MachOperand::Block(body), MachOperand::Block(exit)],
        ));
        func.append_inst(header, header_br);

        let body_store = func.push_inst(MachInst::new(
            AArch64Opcode::StrRI,
            vec![vreg(5), vreg(0), imm(8)],
        ));
        func.append_inst(body, body_store);
        let body_br = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(header)],
        ));
        func.append_inst(body, body_br);

        let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(exit, ret);

        func.add_edge(preheader, header);
        func.add_edge(header, body);
        func.add_edge(header, exit);
        func.add_edge(body, header);

        let mut gvn = GlobalValueNumbering;
        assert!(
            !gvn.run(&mut func),
            "GVN must preserve loop-header reloads invalidated by loop-body stores"
        );
        assert!(
            func.block(header).insts.contains(&header_load),
            "loop-header load must remain"
        );
    }

    #[test]
    fn test_gvn_does_not_reuse_prebranch_load_after_store_path_merge() {
        // bb0: v2 = ldr v0, #8
        //      br bb1, bb2
        // bb1: str v5, v0, #8
        //      br bb3
        // bb2: br bb3
        // bb3: v3 = ldr v0, #8
        //      v4 = add v3, v1
        //
        // The entry load dominates bb3 syntactically, but it is not available
        // on every path: bb1 may store before reaching the merge. GVN must not
        // replace the merge load with the pre-branch value.
        let mut func = MachFunction::new(
            "test_gvn_store_path_merge_load".to_string(),
            Signature::new(vec![], vec![]),
        );
        let bb0 = func.entry;
        let bb1 = func.create_block();
        let bb2 = func.create_block();
        let bb3 = func.create_block();

        let _entry_load = func.push_inst(MachInst::new(
            AArch64Opcode::LdrRI,
            vec![vreg(2), vreg(0), imm(8)],
        ));
        func.append_inst(bb0, _entry_load);
        let br0 = func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![MachOperand::Block(bb1), MachOperand::Block(bb2)],
        ));
        func.append_inst(bb0, br0);

        let store = func.push_inst(MachInst::new(
            AArch64Opcode::StrRI,
            vec![vreg(5), vreg(0), imm(8)],
        ));
        func.append_inst(bb1, store);
        let br1 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb3)],
        ));
        func.append_inst(bb1, br1);

        let br2 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb3)],
        ));
        func.append_inst(bb2, br2);

        let merge_load = func.push_inst(MachInst::new(
            AArch64Opcode::LdrRI,
            vec![vreg(3), vreg(0), imm(8)],
        ));
        func.append_inst(bb3, merge_load);
        let use_load = func.push_inst(MachInst::new(
            AArch64Opcode::AddRR,
            vec![vreg(4), vreg(3), vreg(1)],
        ));
        func.append_inst(bb3, use_load);
        let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb3, ret);

        func.add_edge(bb0, bb1);
        func.add_edge(bb0, bb2);
        func.add_edge(bb1, bb3);
        func.add_edge(bb2, bb3);

        let mut gvn = GlobalValueNumbering;
        assert!(
            !gvn.run(&mut func),
            "GVN must not reuse pre-branch loads at a merge with a store path"
        );
        assert!(func.block(bb3).insts.contains(&merge_load));
        let use_inst = func.inst(use_load);
        assert_eq!(use_inst.operands[1], vreg(3));
    }

    // ---- Idempotency test ----

    #[test]
    fn test_gvn_idempotent() {
        let a1 = MachInst::new(AArch64Opcode::AddRR, vec![vreg(2), vreg(0), vreg(1)]);
        let a2 = MachInst::new(AArch64Opcode::AddRR, vec![vreg(3), vreg(0), vreg(1)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![a1, a2, ret]);

        let mut gvn = GlobalValueNumbering;
        assert!(gvn.run(&mut func));
        // Second run should be a no-op.
        assert!(!gvn.run(&mut func));
    }

    // ---- Empty function test ----

    #[test]
    fn test_gvn_empty_function() {
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![ret]);

        let mut gvn = GlobalValueNumbering;
        assert!(!gvn.run(&mut func));
    }

    // ---- Transitive value numbering test ----

    #[test]
    fn test_gvn_transitive() {
        // v2 = add v0, v1
        // v3 = mov v2         (copy: v3 gets same value number as v2)
        // v4 = add v0, v1     -> eliminated, v4 replaced with v2
        // v5 = sub v4, #1     -> v5 = sub v2, #1
        // ret
        let a1 = MachInst::new(AArch64Opcode::AddRR, vec![vreg(2), vreg(0), vreg(1)]);
        let mov = MachInst::new(AArch64Opcode::MovR, vec![vreg(3), vreg(2)]);
        let a2 = MachInst::new(AArch64Opcode::AddRR, vec![vreg(4), vreg(0), vreg(1)]);
        let sub = MachInst::new(AArch64Opcode::SubRI, vec![vreg(5), vreg(4), imm(1)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![a1, mov, a2, sub, ret]);

        let mut gvn = GlobalValueNumbering;
        assert!(gvn.run(&mut func));

        // a2 should be eliminated
        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 4); // a1, mov, sub, ret

        // sub should use v2 instead of v4
        let sub_inst = func.inst(block.insts[2]);
        assert_eq!(sub_inst.operands[1], vreg(2));
    }

    // ---- Chain of redundancies ----

    #[test]
    fn test_gvn_chain_redundancies() {
        // v2 = add v0, v1
        // v3 = add v0, v1   -> eliminated, v3 -> v2
        // v4 = sub v3, #1   -> v4 = sub v2, #1
        // ret
        let a1 = MachInst::new(AArch64Opcode::AddRR, vec![vreg(2), vreg(0), vreg(1)]);
        let a2 = MachInst::new(AArch64Opcode::AddRR, vec![vreg(3), vreg(0), vreg(1)]);
        let sub = MachInst::new(AArch64Opcode::SubRI, vec![vreg(4), vreg(3), imm(1)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![a1, a2, sub, ret]);

        let mut gvn = GlobalValueNumbering;
        assert!(gvn.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 3); // a1, sub, ret
        let sub_inst = func.inst(block.insts[1]);
        assert_eq!(sub_inst.operands[1], vreg(2));
    }

    // ---- Proof annotation tests ----

    #[test]
    fn test_gvn_preserves_surviving_proof() {
        // v2 = add v0, v1 [NoOverflow]
        // v3 = add v0, v1 (no proof) -> eliminated
        // Surviving instruction keeps its proof.
        let a1 = MachInst::new(AArch64Opcode::AddRR, vec![vreg(2), vreg(0), vreg(1)])
            .with_proof(ProofAnnotation::NoOverflow);
        let a2 = MachInst::new(AArch64Opcode::AddRR, vec![vreg(3), vreg(0), vreg(1)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![a1, a2, ret]);

        let mut gvn = GlobalValueNumbering;
        assert!(gvn.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 2);
        let surviving = func.inst(block.insts[0]);
        assert_eq!(surviving.proof, Some(ProofAnnotation::NoOverflow));
    }

    #[test]
    fn test_gvn_merges_proof_from_eliminated() {
        // v2 = add v0, v1 (no proof)
        // v3 = add v0, v1 [InBounds] -> eliminated, proof merged onto v2
        let a1 = MachInst::new(AArch64Opcode::AddRR, vec![vreg(2), vreg(0), vreg(1)]);
        let a2 = MachInst::new(AArch64Opcode::AddRR, vec![vreg(3), vreg(0), vreg(1)])
            .with_proof(ProofAnnotation::InBounds);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![a1, a2, ret]);

        let mut gvn = GlobalValueNumbering;
        assert!(gvn.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 2);
        let surviving = func.inst(block.insts[0]);
        assert_eq!(surviving.proof, Some(ProofAnnotation::InBounds));
    }

    #[test]
    fn test_gvn_merges_same_proof() {
        // Both have the same proof -> surviving keeps it.
        let a1 = MachInst::new(AArch64Opcode::AddRR, vec![vreg(2), vreg(0), vreg(1)])
            .with_proof(ProofAnnotation::NotNull);
        let a2 = MachInst::new(AArch64Opcode::AddRR, vec![vreg(3), vreg(0), vreg(1)])
            .with_proof(ProofAnnotation::NotNull);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![a1, a2, ret]);

        let mut gvn = GlobalValueNumbering;
        assert!(gvn.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 2);
        let surviving = func.inst(block.insts[0]);
        assert_eq!(surviving.proof, Some(ProofAnnotation::NotNull));
    }

    #[test]
    fn test_gvn_drops_conflicting_proofs() {
        // Different proofs -> conservative merge returns None.
        let a1 = MachInst::new(AArch64Opcode::AddRR, vec![vreg(2), vreg(0), vreg(1)])
            .with_proof(ProofAnnotation::NoOverflow);
        let a2 = MachInst::new(AArch64Opcode::AddRR, vec![vreg(3), vreg(0), vreg(1)])
            .with_proof(ProofAnnotation::InBounds);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![a1, a2, ret]);

        let mut gvn = GlobalValueNumbering;
        assert!(gvn.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 2);
        let surviving = func.inst(block.insts[0]);
        // Different proofs -> conservatively dropped.
        assert!(surviving.proof.is_none());
    }

    // ---- Load proof annotation test ----

    #[test]
    fn test_gvn_load_proof_preserved() {
        // l1 = ldr v0, #8 [NotNull]
        // l2 = ldr v0, #8   -> eliminated, proof merged
        // ret
        let l1 = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(2), vreg(0), imm(8)])
            .with_proof(ProofAnnotation::NotNull);
        let l2 = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(3), vreg(0), imm(8)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![l1, l2, ret]);

        let mut gvn = GlobalValueNumbering;
        assert!(gvn.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 2);
        let surviving = func.inst(block.insts[0]);
        assert_eq!(surviving.proof, Some(ProofAnnotation::NotNull));
    }

    // ---- Scope isolation test ----

    #[test]
    fn test_gvn_scope_isolation_loads() {
        // bb0: v2 = ldr v0, #8
        //      br bb1, bb2
        // bb1: str v5, v0, #8   (store kills loads in this scope)
        //      v3 = ldr v0, #8  (cannot reuse bb0's load because of store)
        //      br bb3
        // bb2: v4 = ldr v0, #8  (kept; load value numbering is block-local)
        //      br bb3
        // bb3: ret
        let mut func = MachFunction::new(
            "test_scope_loads".to_string(),
            Signature::new(vec![], vec![]),
        );
        let bb0 = func.entry;
        let bb1 = func.create_block();
        let bb2 = func.create_block();
        let bb3 = func.create_block();

        // bb0
        let l0 = func.push_inst(MachInst::new(
            AArch64Opcode::LdrRI,
            vec![vreg(2), vreg(0), imm(8)],
        ));
        func.append_inst(bb0, l0);
        let br0 = func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![MachOperand::Block(bb1), MachOperand::Block(bb2)],
        ));
        func.append_inst(bb0, br0);

        // bb1: store + load
        let st = func.push_inst(MachInst::new(
            AArch64Opcode::StrRI,
            vec![vreg(5), vreg(0), imm(8)],
        ));
        func.append_inst(bb1, st);
        let l1 = func.push_inst(MachInst::new(
            AArch64Opcode::LdrRI,
            vec![vreg(3), vreg(0), imm(8)],
        ));
        func.append_inst(bb1, l1);
        let br1 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb3)],
        ));
        func.append_inst(bb1, br1);

        // bb2: just load (no store)
        let l2 = func.push_inst(MachInst::new(
            AArch64Opcode::LdrRI,
            vec![vreg(4), vreg(0), imm(8)],
        ));
        func.append_inst(bb2, l2);
        let br2 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb3)],
        ));
        func.append_inst(bb2, br2);

        // bb3
        let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb3, ret);

        func.add_edge(bb0, bb1);
        func.add_edge(bb0, bb2);
        func.add_edge(bb1, bb3);
        func.add_edge(bb2, bb3);

        let mut gvn = GlobalValueNumbering;
        assert!(!gvn.run(&mut func));

        // bb1: store killed the load, so bb1 still has 3 instructions
        assert_eq!(func.block(bb1).insts.len(), 3); // store, load, branch
        // bb2: load remains because GVN no longer carries load VNs across blocks.
        assert_eq!(func.block(bb2).insts.len(), 2); // load, branch
    }

    #[test]
    fn test_gvn_store_kill_does_not_leak_child_load_to_sibling() {
        // bb0 defines a shared base and branches to siblings.
        // bb1: load base; store base; branch exit
        // bb2: load base; use it; branch exit
        //
        // The load in bb1 is killed by the store before bb1 scope exits. It
        // must not be restored into the parent load table and reused by bb2.
        let mut func = MachFunction::new(
            "test_gvn_kill_no_sibling_leak".to_string(),
            Signature::new(vec![], vec![]),
        );
        let bb0 = func.entry;
        let bb1 = func.create_block();
        let bb2 = func.create_block();
        let exit = func.create_block();

        let base = func.push_inst(MachInst::new(
            AArch64Opcode::AddRI,
            vec![vreg(10), vreg(0), imm(0)],
        ));
        func.append_inst(bb0, base);
        let br0 = func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![MachOperand::Block(bb1), MachOperand::Block(bb2)],
        ));
        func.append_inst(bb0, br0);

        let _bb1_load = func.push_inst(MachInst::new(
            AArch64Opcode::LdrRI,
            vec![vreg(2), vreg(10), imm(8)],
        ));
        func.append_inst(bb1, _bb1_load);
        let bb1_store = func.push_inst(MachInst::new(
            AArch64Opcode::StrRI,
            vec![vreg(5), vreg(10), imm(8)],
        ));
        func.append_inst(bb1, bb1_store);
        let br1 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(exit)],
        ));
        func.append_inst(bb1, br1);

        let bb2_load = func.push_inst(MachInst::new(
            AArch64Opcode::LdrRI,
            vec![vreg(3), vreg(10), imm(8)],
        ));
        func.append_inst(bb2, bb2_load);
        let bb2_use = func.push_inst(MachInst::new(
            AArch64Opcode::AddRR,
            vec![vreg(4), vreg(3), vreg(1)],
        ));
        func.append_inst(bb2, bb2_use);
        let br2 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(exit)],
        ));
        func.append_inst(bb2, br2);

        let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(exit, ret);

        func.add_edge(bb0, bb1);
        func.add_edge(bb0, bb2);
        func.add_edge(bb1, exit);
        func.add_edge(bb2, exit);

        let mut gvn = GlobalValueNumbering;
        assert!(
            !gvn.run(&mut func),
            "GVN must not reuse a load from a non-dominating sibling"
        );
        assert!(func.block(bb2).insts.contains(&bb2_load));
        let use_inst = func.inst(bb2_use);
        assert_eq!(use_inst.operands[1], vreg(3));
    }

    // ---- MOVK tied def-use regression test (issue #366) ----

    /// Regression test for the #366 residual xxh3 miscompile.
    ///
    /// MOVK is a tied def-use instruction: `MOVK Rd, #imm16, LSL #shift`
    /// inserts `imm16` into Rd at position `shift` while preserving the
    /// other bits. The instruction depends on the *current* value of Rd,
    /// but that dependency is not captured in the explicit operand list.
    ///
    /// Before this fix, GVN treated two MOVKs with matching (imm, shift)
    /// as redundant, even when their destination registers held
    /// different prior values. This corrupted multi-register constant
    /// materialization chains (e.g., two unrelated 64-bit constants that
    /// happened to share some 16-bit chunks).
    ///
    /// The scenario below mimics xxh3: build two 64-bit constants
    /// 0x067e2f2a_6bfdd932 and 0x067e2f2a_6d83f618 that share the upper
    /// 32 bits (MOVKs at positions 32 and 48 have the same imm). GVN
    /// must NOT eliminate the second register's MOVKs.
    #[test]
    fn test_gvn_preserves_movk_with_different_dest() {
        // v2 = movz #0xd932
        // v2 = movk #0x6bfd, lsl 16
        // v2 = movk #0x2f2a, lsl 32  (shared with v3)
        // v2 = movk #0x067e, lsl 48  (shared with v3)
        //
        // v3 = movz #0xf618
        // v3 = movk #0x6d83, lsl 16
        // v3 = movk #0x2f2a, lsl 32  (same imm+shift as v2's but DIFFERENT dest)
        // v3 = movk #0x067e, lsl 48  (same imm+shift as v2's but DIFFERENT dest)
        // ret
        //
        // GVN must preserve all eight instructions — eliminating v3's
        // upper MOVKs would corrupt v3 to 0x0000_0000_6d83_f618.
        let m_movz_v2 = MachInst::new(AArch64Opcode::Movz, vec![vreg(2), imm(0xd932)]);
        let m_movk_v2_16 = MachInst::new(AArch64Opcode::Movk, vec![vreg(2), imm(0x6bfd), imm(16)]);
        let m_movk_v2_32 = MachInst::new(AArch64Opcode::Movk, vec![vreg(2), imm(0x2f2a), imm(32)]);
        let m_movk_v2_48 = MachInst::new(AArch64Opcode::Movk, vec![vreg(2), imm(0x067e), imm(48)]);

        let m_movz_v3 = MachInst::new(AArch64Opcode::Movz, vec![vreg(3), imm(0xf618)]);
        let m_movk_v3_16 = MachInst::new(AArch64Opcode::Movk, vec![vreg(3), imm(0x6d83), imm(16)]);
        let m_movk_v3_32 = MachInst::new(AArch64Opcode::Movk, vec![vreg(3), imm(0x2f2a), imm(32)]);
        let m_movk_v3_48 = MachInst::new(AArch64Opcode::Movk, vec![vreg(3), imm(0x067e), imm(48)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);

        let mut func = make_func_with_insts(vec![
            m_movz_v2,
            m_movk_v2_16,
            m_movk_v2_32,
            m_movk_v2_48,
            m_movz_v3,
            m_movk_v3_16,
            m_movk_v3_32,
            m_movk_v3_48,
            ret,
        ]);

        let mut gvn = GlobalValueNumbering;
        // GVN may report no changes for this input — but even if it does
        // report changes (via the MOVZs, which are safe to number), the
        // MOVKs must survive.
        let _ = gvn.run(&mut func);

        let block = func.block(func.entry);

        // Count remaining MOVKs — must still be 6 (three per constant).
        let movk_count = block
            .insts
            .iter()
            .filter(|id| func.inst(**id).opcode == AArch64Opcode::Movk)
            .count();
        assert_eq!(
            movk_count, 6,
            "GVN eliminated a MOVK — this is the #366 bug. All six MOVKs must survive."
        );

        // Verify each MOVK still targets the correct vreg (no def-vreg rewrite).
        for inst_id in &block.insts {
            let inst = func.inst(*inst_id);
            if inst.opcode == AArch64Opcode::Movk {
                match &inst.operands[0] {
                    MachOperand::VReg(v) => {
                        assert!(
                            v.id == 2 || v.id == 3,
                            "MOVK destination was rewritten to unexpected vreg {}",
                            v.id
                        );
                    }
                    _ => panic!("MOVK operand[0] is not a VReg"),
                }
            }
        }
    }

    /// Tighter version: check that running GVN on a MOVK chain doesn't
    /// drop or rewrite the MOVKs of either constant.
    #[test]
    fn test_gvn_movk_chain_preserves_both_constants() {
        // Same as above but simpler: just two parallel MOVZ+MOVK pairs
        // with the SAME (imm, shift) MOVK. GVN must NOT merge them.
        let m1 = MachInst::new(AArch64Opcode::Movz, vec![vreg(2), imm(0x1111)]);
        let m2 = MachInst::new(AArch64Opcode::Movk, vec![vreg(2), imm(0xabcd), imm(16)]);
        let m3 = MachInst::new(AArch64Opcode::Movz, vec![vreg(3), imm(0x2222)]);
        let m4 = MachInst::new(AArch64Opcode::Movk, vec![vreg(3), imm(0xabcd), imm(16)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![m1, m2, m3, m4, ret]);

        let mut gvn = GlobalValueNumbering;
        let _ = gvn.run(&mut func);

        let block = func.block(func.entry);
        let movk_count = block
            .insts
            .iter()
            .filter(|id| func.inst(**id).opcode == AArch64Opcode::Movk)
            .count();
        assert_eq!(
            movk_count, 2,
            "GVN incorrectly merged two MOVKs with different destinations"
        );
    }

    // -------------------------------------------------------------------
    // Regression tests for #408 / #409 — BFM tied def-use and ADC/SBC
    // carry-flag reads must be correctly classified so GVN does not fold
    // semantically-different instructions into one.
    // -------------------------------------------------------------------

    /// Regression for #408: two BFMs with identical explicit operands but
    /// different prior Rd values must NOT be value-numbered together.
    /// BFM preserves the uncovered bits of Rd, so the prior dest is an
    /// implicit input just like MOVK.
    #[test]
    fn test_gvn_preserves_bfm_with_different_dest() {
        // v2 = movz #0x1111
        // v2 = bfm v2, v0, #0, #7       (insert low byte of v0 into v2)
        // v3 = movz #0x2222
        // v3 = bfm v3, v0, #0, #7       (same explicit (src, immr, imms) but
        //                                different prior dest value)
        // ret
        //
        // Eliminating the second BFM and replacing v3 with v2 silently
        // corrupts v3 — its high bits were 0x2222 but would become 0x1111.
        let m_movz_v2 = MachInst::new(AArch64Opcode::Movz, vec![vreg(2), imm(0x1111)]);
        let m_bfm_v2 = MachInst::new(AArch64Opcode::Bfm, vec![vreg(2), vreg(0), imm(0), imm(7)]);
        let m_movz_v3 = MachInst::new(AArch64Opcode::Movz, vec![vreg(3), imm(0x2222)]);
        let m_bfm_v3 = MachInst::new(AArch64Opcode::Bfm, vec![vreg(3), vreg(0), imm(0), imm(7)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![m_movz_v2, m_bfm_v2, m_movz_v3, m_bfm_v3, ret]);

        let mut gvn = GlobalValueNumbering;
        let _ = gvn.run(&mut func);

        let block = func.block(func.entry);
        let bfm_count = block
            .insts
            .iter()
            .filter(|id| func.inst(**id).opcode == AArch64Opcode::Bfm)
            .count();
        assert_eq!(
            bfm_count, 2,
            "GVN merged two BFMs with different prior Rd values — this is the #408 bug"
        );

        // Every surviving BFM must keep its original destination.
        for inst_id in &block.insts {
            let inst = func.inst(*inst_id);
            if inst.opcode == AArch64Opcode::Bfm {
                match &inst.operands[0] {
                    MachOperand::VReg(v) => assert!(
                        v.id == 2 || v.id == 3,
                        "BFM destination was rewritten to unexpected vreg {}",
                        v.id
                    ),
                    _ => panic!("BFM operand[0] is not a VReg"),
                }
            }
        }
    }

    /// Regression for #409: two ADCs with the same explicit operands but
    /// preceded by different flag writers (different carry inputs) must
    /// NOT be GVN'd together. The carry flag is an implicit input.
    #[test]
    fn test_gvn_preserves_adc_across_flag_writers() {
        // v10 = adds v0, v1           (flag writer #1)
        // v2  = adc  v4, v5           (reads carry from #1)
        // v11 = adds v6, v7           (flag writer #2 — different inputs)
        // v3  = adc  v4, v5           (same explicit operands as above,
        //                               but carry comes from #2)
        // ret
        //
        // Merging v3 into v2 drops the dependency on the second ADDS and
        // silently miscompiles any i128 / multi-precision arithmetic.
        let adds1 = MachInst::new(AArch64Opcode::AddsRR, vec![vreg(10), vreg(0), vreg(1)]);
        let adc1 = MachInst::new(AArch64Opcode::Adc, vec![vreg(2), vreg(4), vreg(5)]);
        let adds2 = MachInst::new(AArch64Opcode::AddsRR, vec![vreg(11), vreg(6), vreg(7)]);
        let adc2 = MachInst::new(AArch64Opcode::Adc, vec![vreg(3), vreg(4), vreg(5)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![adds1, adc1, adds2, adc2, ret]);

        let mut gvn = GlobalValueNumbering;
        let _ = gvn.run(&mut func);

        let block = func.block(func.entry);
        let adc_count = block
            .insts
            .iter()
            .filter(|id| func.inst(**id).opcode == AArch64Opcode::Adc)
            .count();
        assert_eq!(
            adc_count, 2,
            "GVN merged two ADCs across different flag writers — this is the #409 bug"
        );

        // Each surviving ADC must keep its original destination vreg.
        let mut seen = std::collections::HashSet::new();
        for inst_id in &block.insts {
            let inst = func.inst(*inst_id);
            if inst.opcode == AArch64Opcode::Adc
                && let MachOperand::VReg(v) = &inst.operands[0]
            {
                seen.insert(v.id);
            }
        }
        assert!(
            seen.contains(&2) && seen.contains(&3),
            "ADC destinations were rewritten: surviving dests = {:?}",
            seen
        );
    }

    /// Matching SBC regression: symmetry with ADC.
    #[test]
    fn test_gvn_preserves_sbc_across_flag_writers() {
        let subs1 = MachInst::new(AArch64Opcode::SubsRR, vec![vreg(10), vreg(0), vreg(1)]);
        let sbc1 = MachInst::new(AArch64Opcode::Sbc, vec![vreg(2), vreg(4), vreg(5)]);
        let subs2 = MachInst::new(AArch64Opcode::SubsRR, vec![vreg(11), vreg(6), vreg(7)]);
        let sbc2 = MachInst::new(AArch64Opcode::Sbc, vec![vreg(3), vreg(4), vreg(5)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![subs1, sbc1, subs2, sbc2, ret]);

        let mut gvn = GlobalValueNumbering;
        let _ = gvn.run(&mut func);

        let block = func.block(func.entry);
        let sbc_count = block
            .insts
            .iter()
            .filter(|id| func.inst(**id).opcode == AArch64Opcode::Sbc)
            .count();
        assert_eq!(
            sbc_count, 2,
            "GVN merged two SBCs across different flag writers — #409 regression"
        );
    }
}
