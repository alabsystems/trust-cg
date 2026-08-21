// trust-cg-opt - Dead Code Elimination
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Dead Code Elimination (DCE) for machine-level IR.
//!
//! Removes instructions whose definitions are never used, provided they
//! have no side effects. This is a simple backward-scan DCE that operates
//! on each basic block independently.
//!
//! # Algorithm
//!
//! For each local removal wave:
//! 1. Build a set of "used" virtual registers by scanning all operands.
//! 2. Walk instructions. If an instruction:
//!    - Defines a VReg that is NOT in the used set, AND
//!    - Has no side effects (not a call, branch, store, or flag-setting op)
//!    - Then mark it for removal.
//! 3. Remove marked instructions from the block.
//! 4. Repeat until no more instructions can be removed. This reaches the local
//!    fixed point for pure dead value chains in a single pass invocation.
//!
//! # Side-Effect Barriers
//!
//! Instructions with any of these properties are NEVER eliminated:
//! - `IS_CALL` — may have arbitrary side effects
//! - `IS_BRANCH` / `IS_TERMINATOR` — control flow
//! - `IS_RETURN` — control flow
//! - `HAS_SIDE_EFFECTS` — flag-setting, stores, etc.
//! - `WRITES_MEMORY` — stores
//! - `READS_MEMORY` — loads (conservative; a more aggressive DCE could
//!   remove loads whose result is unused, but we keep it simple)
//! - any non-`Pure` effect in the authoritative `opcode_effect()` table
//!
//! Reference: LLVM `DeadMachineInstrElim.cpp`

use std::collections::HashSet;

use serde::{Deserialize, Serialize};
use trust_cg_ir::{InstFlags, InstId, MachFunction, MachOperand, PassId, ProvenanceMap, VReg};

use crate::cache::StableHasher;
use crate::effects::{
    MemoryEffect, aarch64_for_each_def_position, aarch64_for_each_use_position,
    aarch64_use_operand_positions, opcode_effect, single_inst_def,
};
use crate::pass_manager::{
    CertifiedPassCheckerRecord, CertifiedPassRunRecord, CertifiedPassRunStatus, MachinePass,
};

/// Dead Code Elimination pass.
pub struct DeadCodeElimination;

/// DCE wrapper that emits neutral certified pass run records.
#[derive(Default)]
pub struct CertifiedDeadCodeElimination {
    certified_pass_runs: Vec<CertifiedPassRunRecord>,
}

impl CertifiedDeadCodeElimination {
    /// Create a certified DCE wrapper.
    pub fn new() -> Self {
        Self::default()
    }

    fn record_run(&mut self, function_name: &str, run: &DceCertifiedRun) {
        self.certified_pass_runs
            .push(dce_certified_pass_record(function_name, run));
    }
}

/// Contract certified for this conservative DCE slice.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum DceContract {
    /// Removing a pure unused value preserves all observable graph/certificate
    /// outputs under bound-propagation semantics.
    PureUnusedValueUnobservable,
}

/// Result produced by the local certificate checker.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum DceCertificateResult {
    Verified,
    Failed,
}

/// Caller-provided visibility roots that certified DCE must treat as outputs.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct DceCertifiedOptions {
    pub graph_output_vregs: HashSet<u32>,
    pub certificate_visible_vregs: HashSet<u32>,
}

/// Use/def facts recorded for a removed instruction.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct DceUseDefFacts {
    pub def_vreg: Option<u32>,
    pub use_vregs: Vec<u32>,
    pub def_is_used: bool,
}

/// Side-effect and purity facts recorded for a removed instruction.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct DceSideEffectFacts {
    pub memory_effect: String,
    pub flags: String,
    pub is_pure: bool,
    pub has_side_effect_barrier: bool,
}

/// Output visibility facts recorded for a removed instruction.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct DceVisibilityFacts {
    pub graph_output_visible: bool,
    pub certificate_output_visible: bool,
}

/// One checked DCE pass certificate.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct DceCertificate {
    pub format_version: u32,
    pub pass_name: String,
    pub pass_version: u32,
    pub pass_instance_id: String,
    pub source_inst_id: u32,
    pub source_opcode: String,
    pub source_operands: Vec<String>,
    pub source_location: Option<String>,
    pub use_def: DceUseDefFacts,
    pub side_effects: DceSideEffectFacts,
    pub visibility: DceVisibilityFacts,
    pub contract: DceContract,
    pub domain: String,
    pub obligation_hash: String,
    pub checker: String,
    pub result: DceCertificateResult,
}

/// Failed/unsupported candidate observed while running in certified mode.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct DceCertificationFailure {
    pub source_inst_id: u32,
    pub source_opcode: String,
    pub reason: String,
}

/// Result of running DCE through the certified pass boundary.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct DceCertifiedRun {
    pub changed: bool,
    pub certificates: Vec<DceCertificate>,
    pub failures: Vec<DceCertificationFailure>,
}

impl DceCertifiedRun {
    /// A certified compile may consume this pass only when every emitted
    /// removal obligation checked and no fail-closed candidate was observed.
    pub fn is_certified(&self) -> bool {
        self.failures.is_empty()
            && self
                .certificates
                .iter()
                .all(|cert| cert.result == DceCertificateResult::Verified)
    }
}

impl DeadCodeElimination {
    /// Run DCE and emit checked per-removal certificates for the supported
    /// pure-unused-value subset.
    pub fn run_certified(&mut self, func: &mut MachFunction) -> DceCertifiedRun {
        self.run_certified_with_options(func, DceCertifiedOptions::default())
    }

    /// Run certified DCE with explicit graph/certificate visibility roots.
    pub fn run_certified_with_options(
        &mut self,
        func: &mut MachFunction,
        options: DceCertifiedOptions,
    ) -> DceCertifiedRun {
        run_impl(func, Some(&options), None)
    }

    /// Run certified DCE while preserving instruction provenance.
    pub fn run_certified_with_provenance(
        &mut self,
        func: &mut MachFunction,
        provenance: &mut ProvenanceMap,
    ) -> DceCertifiedRun {
        self.run_certified_with_options_and_provenance(
            func,
            DceCertifiedOptions::default(),
            provenance,
        )
    }

    /// Run certified DCE with explicit visibility roots and provenance.
    pub fn run_certified_with_options_and_provenance(
        &mut self,
        func: &mut MachFunction,
        options: DceCertifiedOptions,
        provenance: &mut ProvenanceMap,
    ) -> DceCertifiedRun {
        run_impl(func, Some(&options), Some(provenance))
    }
}

impl MachinePass for DeadCodeElimination {
    fn name(&self) -> &str {
        "dce"
    }

    fn run(&mut self, func: &mut MachFunction) -> bool {
        run_impl(func, None, None).changed
    }

    fn run_with_provenance(
        &mut self,
        func: &mut MachFunction,
        provenance: &mut ProvenanceMap,
    ) -> bool {
        run_impl(func, None, Some(provenance)).changed
    }

    fn run_with_analyses_and_provenance(
        &mut self,
        func: &mut MachFunction,
        _analyses: &mut crate::pass_manager::AnalysisCache,
        provenance: &mut ProvenanceMap,
    ) -> bool {
        self.run_with_provenance(func, provenance)
    }
}

impl MachinePass for CertifiedDeadCodeElimination {
    fn name(&self) -> &str {
        "dce"
    }

    fn run(&mut self, func: &mut MachFunction) -> bool {
        let mut pass = DeadCodeElimination;
        let run = pass.run_certified(func);
        self.record_run(&func.name, &run);
        run.changed
    }

    fn run_with_provenance(
        &mut self,
        func: &mut MachFunction,
        provenance: &mut ProvenanceMap,
    ) -> bool {
        let mut pass = DeadCodeElimination;
        let run = pass.run_certified_with_provenance(func, provenance);
        self.record_run(&func.name, &run);
        run.changed
    }

    fn run_with_analyses_and_provenance(
        &mut self,
        func: &mut MachFunction,
        _analyses: &mut crate::pass_manager::AnalysisCache,
        provenance: &mut ProvenanceMap,
    ) -> bool {
        self.run_with_provenance(func, provenance)
    }

    fn take_certified_pass_runs(&mut self) -> Vec<CertifiedPassRunRecord> {
        std::mem::take(&mut self.certified_pass_runs)
    }
}

fn dce_certified_pass_record(function_name: &str, run: &DceCertifiedRun) -> CertifiedPassRunRecord {
    let status = if run.is_certified() {
        CertifiedPassRunStatus::Verified
    } else {
        CertifiedPassRunStatus::Failed
    };
    CertifiedPassRunRecord {
        format_version: "trust-cg.opt.certified_pass_run.v1".to_string(),
        pass_name: "dce-pure-unused".to_string(),
        pass_version: 1,
        pass_instance_id: "dce:bound-propagation:pure-unused:v1".to_string(),
        function_name: function_name.to_string(),
        changed: run.changed,
        status,
        certificate_count: run.certificates.len(),
        failure_count: run.failures.len(),
        obligation_hash: dce_run_obligation_hash(function_name, run),
        local_checker: CertifiedPassCheckerRecord {
            kind: "trust-cg-opt-local".to_string(),
            name: "analytical bound-propagation DCE checker".to_string(),
            version: "1".to_string(),
            status,
        },
        summary: serde_json::to_value(run).expect("DCE certified run serializes"),
    }
}

fn dce_run_obligation_hash(function_name: &str, run: &DceCertifiedRun) -> String {
    let mut h = StableHasher::new();
    h.write_str("trust-cg.dce.certified-run.v1");
    h.write_str(function_name);
    h.write_u8(u8::from(run.changed));
    h.write_u32(run.certificates.len() as u32);
    for cert in &run.certificates {
        h.write_u32(cert.source_inst_id);
        h.write_str(&cert.source_opcode);
        h.write_str(&cert.obligation_hash);
        h.write_str(cert.result.as_str());
    }
    h.write_u32(run.failures.len() as u32);
    for failure in &run.failures {
        h.write_u32(failure.source_inst_id);
        h.write_str(&failure.source_opcode);
        h.write_str(&failure.reason);
    }
    format!("trust-cg-opt-certified-pass-run-v1:{:032x}", h.finish128())
}

impl DceCertificateResult {
    fn as_str(self) -> &'static str {
        match self {
            Self::Verified => "verified",
            Self::Failed => "failed",
        }
    }
}

fn run_impl(
    func: &mut MachFunction,
    certified_options: Option<&DceCertifiedOptions>,
    mut provenance: Option<&mut ProvenanceMap>,
) -> DceCertifiedRun {
    let mut changed = false;
    let mut certificates = Vec::new();
    let mut failures = Vec::new();
    let mut seen_failures = HashSet::new();

    loop {
        // Step 1: Collect all VRegs that are *used* (appear as source
        // operands) across the current function.
        let used_vregs = collect_used_vregs(func);

        // Step 2: Find instructions to remove. An instruction is dead if:
        //   (a) it defines a VReg not in the used set, AND
        //   (b) it has no side effects.
        let mut dead_insts: HashSet<InstId> = HashSet::new();

        for block_id in func.block_order.clone() {
            let block = func.block(block_id);
            for &inst_id in &block.insts {
                let inst = func.inst(inst_id);
                let def_vreg = get_def_vreg(inst);
                let is_dead_value = match def_vreg {
                    Some(vreg) => !used_vregs.contains(&vreg),
                    None => inst.is_nop(),
                };

                if let Some(options) = certified_options
                    && is_dead_value
                    && let Some(reason) = certification_failure_reason(inst, def_vreg, options)
                {
                    push_unique_dce_failure(
                        &mut failures,
                        &mut seen_failures,
                        inst_id,
                        inst,
                        reason,
                    );
                    continue;
                }

                // Never remove instructions with side effects.
                if has_side_effects(inst) {
                    continue;
                }

                // Check if any defined VReg is used.
                match def_vreg {
                    Some(vreg) => {
                        if !used_vregs.contains(&vreg) {
                            if let Some(options) = certified_options {
                                let cert =
                                    make_dce_certificate(inst_id, inst, &used_vregs, options);
                                if cert.result != DceCertificateResult::Verified {
                                    push_unique_dce_failure(
                                        &mut failures,
                                        &mut seen_failures,
                                        inst_id,
                                        inst,
                                        "local DCE removal checker failed".to_string(),
                                    );
                                    continue;
                                }
                                certificates.push(cert);
                            }
                            dead_insts.insert(inst_id);
                        }
                    }
                    // Instructions with no def (and no side effects) that are
                    // not branches/terminators are dead. But be conservative:
                    // only Nop qualifies here.
                    None => {
                        if inst.is_nop() {
                            if let Some(options) = certified_options {
                                let cert =
                                    make_dce_certificate(inst_id, inst, &used_vregs, options);
                                if cert.result != DceCertificateResult::Verified {
                                    push_unique_dce_failure(
                                        &mut failures,
                                        &mut seen_failures,
                                        inst_id,
                                        inst,
                                        "local DCE removal checker failed".to_string(),
                                    );
                                    continue;
                                }
                                certificates.push(cert);
                            }
                            dead_insts.insert(inst_id);
                        }
                    }
                }
            }
        }

        if dead_insts.is_empty() {
            break;
        }

        changed = true;

        // Step 3: Remove this dead-instruction wave from blocks, then repeat
        // so values used only by removed instructions can become removable.
        if let Some(provenance) = provenance.as_deref_mut() {
            let mut removed: Vec<_> = dead_insts.iter().copied().collect();
            removed.sort_unstable();
            for inst_id in removed {
                provenance.record_deletion(
                    inst_id,
                    PassId::new("dce"),
                    "unused instruction has no side effects",
                );
            }
        }

        for block_id in func.block_order.clone() {
            let block = func.block_mut(block_id);
            block.insts.retain(|id| !dead_insts.contains(id));
        }
    }

    DceCertifiedRun {
        changed,
        certificates,
        failures,
    }
}

fn push_unique_dce_failure(
    failures: &mut Vec<DceCertificationFailure>,
    seen_failures: &mut HashSet<(u32, String)>,
    inst_id: InstId,
    inst: &trust_cg_ir::MachInst,
    reason: String,
) {
    if seen_failures.insert((inst_id.0, reason.clone())) {
        failures.push(DceCertificationFailure {
            source_inst_id: inst_id.0,
            source_opcode: format!("{:?}", inst.opcode),
            reason,
        });
    }
}

/// Collect all VRegs that appear as source operands in the shared role model.
fn collect_used_vregs(func: &MachFunction) -> HashSet<VReg> {
    let mut used = HashSet::new();

    for block_id in &func.block_order {
        let block = func.block(*block_id);
        for &inst_id in &block.insts {
            let inst = func.inst(inst_id);

            // A removable pure tied instruction (for example `Movk`) must not
            // keep itself alive solely through its own def-use position. A
            // side-effecting tied form (for example CAS) still needs its input,
            // because deleting the producer would change the memory operation.
            let side_effecting = has_side_effects(inst);
            let mut def_positions = Vec::new();
            aarch64_for_each_def_position(inst.opcode, inst.operands.len(), |pos| {
                def_positions.push(pos);
            });
            aarch64_for_each_use_position(inst.opcode, inst.operands.len(), |pos| {
                if !side_effecting && def_positions.contains(&pos) {
                    return;
                }
                if let Some(MachOperand::VReg(vreg)) = inst.operands.get(pos) {
                    used.insert(*vreg);
                }
            });

            // Phi nodes: all operands except the first (def) are uses.
            // Already handled by use_start = 1 for Phi.
        }
    }

    used
}

/// Returns the sole VReg defined by this instruction, if any.
/// Multi-def instructions fail closed because this DCE has a one-result model.
fn get_def_vreg(inst: &trust_cg_ir::MachInst) -> Option<VReg> {
    single_inst_def(inst)
}

/// Returns true if this instruction has side effects that prevent removal.
fn has_side_effects(inst: &trust_cg_ir::MachInst) -> bool {
    let flags = inst.flags;
    let effect = opcode_effect(inst.opcode);

    // Any of these flags means the instruction cannot be removed.
    !effect.is_pure()
        || !inst.implicit_defs.is_empty()
        || !inst.implicit_uses.is_empty()
        || flags.contains(InstFlags::IS_CALL)
        || flags.contains(InstFlags::IS_BRANCH)
        || flags.contains(InstFlags::IS_TERMINATOR)
        || flags.contains(InstFlags::IS_RETURN)
        || flags.contains(InstFlags::HAS_SIDE_EFFECTS)
        || flags.contains(InstFlags::WRITES_MEMORY)
        || flags.contains(InstFlags::READS_MEMORY)
}

fn certification_failure_reason(
    inst: &trust_cg_ir::MachInst,
    def_vreg: Option<VReg>,
    options: &DceCertifiedOptions,
) -> Option<String> {
    if let Some(vreg) = def_vreg {
        let vreg_id = vreg.id;
        if options.graph_output_vregs.contains(&vreg_id) {
            return Some(format!("v{} is graph-output visible", vreg_id));
        }
        if options.certificate_visible_vregs.contains(&vreg_id) {
            return Some(format!("v{} is certificate-output visible", vreg_id));
        }
    }

    let flags = inst.flags;
    if flags.contains(InstFlags::IS_CALL) {
        return Some("call side effects are not certified for DCE".to_string());
    }
    if flags.contains(InstFlags::IS_BRANCH)
        || flags.contains(InstFlags::IS_TERMINATOR)
        || flags.contains(InstFlags::IS_RETURN)
    {
        return Some("control-flow instructions are not certified for DCE".to_string());
    }
    if flags.contains(InstFlags::WRITES_MEMORY) {
        return Some("memory writes are not certified for DCE".to_string());
    }
    if flags.contains(InstFlags::READS_MEMORY) {
        return Some("memory reads are not certified for DCE".to_string());
    }
    if flags.contains(InstFlags::HAS_SIDE_EFFECTS) {
        return Some("side-effecting instructions are not certified for DCE".to_string());
    }

    match opcode_effect(inst.opcode) {
        MemoryEffect::Pure => None,
        MemoryEffect::Load => Some("load effect is not certified for DCE".to_string()),
        MemoryEffect::Store => Some("store effect is not certified for DCE".to_string()),
        MemoryEffect::Call => Some("call/barrier effect is not certified for DCE".to_string()),
    }
}

fn make_dce_certificate(
    inst_id: InstId,
    inst: &trust_cg_ir::MachInst,
    used_vregs: &HashSet<VReg>,
    options: &DceCertifiedOptions,
) -> DceCertificate {
    let source_opcode = format!("{:?}", inst.opcode);
    let source_operands = inst.operands.iter().map(format_operand).collect::<Vec<_>>();
    let def_vreg = get_def_vreg(inst);
    let use_vregs = collect_inst_use_vregs(inst);
    let use_def = DceUseDefFacts {
        def_vreg: def_vreg.map(|vreg| vreg.id),
        use_vregs,
        def_is_used: def_vreg.is_some_and(|vreg| used_vregs.contains(&vreg)),
    };
    let side_effects = side_effect_facts(inst);
    let visibility = visibility_facts(def_vreg, options);
    let source_location = inst
        .source_loc
        .map(|loc| format!("file:{}:{}:{}", loc.file, loc.line, loc.col));
    let obligation_hash = dce_obligation_hash(
        inst_id,
        &source_opcode,
        &source_operands,
        &source_location,
        &use_def,
        &side_effects,
        &visibility,
    );
    let result = if check_dce_obligation(inst, &use_def, &side_effects, &visibility) {
        DceCertificateResult::Verified
    } else {
        DceCertificateResult::Failed
    };

    DceCertificate {
        format_version: 1,
        pass_name: "dce".to_string(),
        pass_version: 1,
        pass_instance_id: "dce:bound-propagation:pure-unused:v1".to_string(),
        source_inst_id: inst_id.0,
        source_opcode,
        source_operands,
        source_location,
        use_def,
        side_effects,
        visibility,
        contract: DceContract::PureUnusedValueUnobservable,
        domain: "bound-propagation;scalar-bv64;observable-outputs=graph+certificate".to_string(),
        obligation_hash,
        checker: "trust-cg-opt analytical bound-propagation DCE checker v1".to_string(),
        result,
    }
}

fn collect_inst_use_vregs(inst: &trust_cg_ir::MachInst) -> Vec<u32> {
    let mut uses = aarch64_use_operand_positions(inst.opcode, inst.operands.len())
        .into_iter()
        .filter_map(|idx| inst.operands.get(idx))
        .filter_map(|operand| match operand {
            MachOperand::VReg(vreg) => Some(vreg.id),
            _ => None,
        })
        .collect::<Vec<_>>();
    uses.sort_unstable();
    uses.dedup();
    uses
}

fn side_effect_facts(inst: &trust_cg_ir::MachInst) -> DceSideEffectFacts {
    let effect = opcode_effect(inst.opcode);
    DceSideEffectFacts {
        memory_effect: format!("{:?}", effect),
        flags: format!("{:?}", inst.flags),
        is_pure: effect == MemoryEffect::Pure,
        has_side_effect_barrier: has_side_effects(inst),
    }
}

fn visibility_facts(def_vreg: Option<VReg>, options: &DceCertifiedOptions) -> DceVisibilityFacts {
    DceVisibilityFacts {
        graph_output_visible: def_vreg
            .is_some_and(|vreg| options.graph_output_vregs.contains(&vreg.id)),
        certificate_output_visible: def_vreg
            .is_some_and(|vreg| options.certificate_visible_vregs.contains(&vreg.id)),
    }
}

fn format_operand(operand: &MachOperand) -> String {
    match operand {
        MachOperand::VReg(vreg) => format!("v{}:{:?}", vreg.id, vreg.class),
        MachOperand::Imm(value) => format!("#{}", value),
        other => format!("{:?}", other),
    }
}

fn dce_obligation_hash(
    inst_id: InstId,
    source_opcode: &str,
    source_operands: &[String],
    source_location: &Option<String>,
    use_def: &DceUseDefFacts,
    side_effects: &DceSideEffectFacts,
    visibility: &DceVisibilityFacts,
) -> String {
    let mut h = StableHasher::new();
    h.write_str("trust-cg.dce.cert.v1");
    h.write_u32(inst_id.0);
    h.write_str(source_opcode);
    for operand in source_operands {
        h.write_str(operand);
    }
    h.write_str(source_location.as_deref().unwrap_or("<none>"));
    match use_def.def_vreg {
        Some(vreg_id) => {
            h.write_u8(1);
            h.write_u32(vreg_id);
        }
        None => h.write_u8(0),
    }
    for vreg_id in &use_def.use_vregs {
        h.write_u32(*vreg_id);
    }
    h.write_u8(u8::from(use_def.def_is_used));
    h.write_str(&side_effects.memory_effect);
    h.write_str(&side_effects.flags);
    h.write_u8(u8::from(side_effects.is_pure));
    h.write_u8(u8::from(side_effects.has_side_effect_barrier));
    h.write_u8(u8::from(visibility.graph_output_visible));
    h.write_u8(u8::from(visibility.certificate_output_visible));
    format!("{:032x}", h.finish128())
}

fn check_dce_obligation(
    inst: &trust_cg_ir::MachInst,
    use_def: &DceUseDefFacts,
    side_effects: &DceSideEffectFacts,
    visibility: &DceVisibilityFacts,
) -> bool {
    (use_def.def_vreg.is_some() || inst.is_nop())
        && !use_def.def_is_used
        && side_effects.is_pure
        && !side_effects.has_side_effect_barrier
        && !visibility.graph_output_visible
        && !visibility.certificate_output_visible
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pass_manager::{AnalysisCache, MachinePass};
    use trust_cg_ir::aarch64_regs::X0;
    use trust_cg_ir::{
        AArch64Opcode, MachFunction, MachInst, MachOperand, ProvenanceStatus, RegClass, Signature,
        TrustIrInstId, VReg,
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
        let mut func = MachFunction::new("test_dce".to_string(), Signature::new(vec![], vec![]));
        let block = func.entry;
        for inst in insts {
            let id = func.push_inst(inst);
            func.append_inst(block, id);
        }
        func
    }

    #[test]
    fn test_dce_removes_unused_add() {
        // v0 = add v1, v2  -- v0 is never used → dead
        // ret
        let add = MachInst::new(AArch64Opcode::AddRR, vec![vreg(0), vreg(1), vreg(2)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![add, ret]);

        let mut dce = DeadCodeElimination;
        assert!(dce.run(&mut func));

        // Only ret should remain
        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 1);
    }

    #[test]
    fn test_dce_removes_unused_same_id_different_class_def() {
        let gpr_v0_def = MachInst::new(AArch64Opcode::AddRR, vec![vreg(0), vreg(1), vreg(2)]);
        let fpr_v0_store = MachInst::new(
            AArch64Opcode::StrRI,
            vec![vreg_class(0, RegClass::Fpr64), imm(8)],
        );
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![gpr_v0_def, fpr_v0_store, ret]);

        let mut dce = DeadCodeElimination;
        assert!(dce.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 2);
        assert_eq!(func.inst(block.insts[0]).opcode, AArch64Opcode::StrRI);
        assert_eq!(func.inst(block.insts[1]).opcode, AArch64Opcode::Ret);
    }

    #[test]
    fn test_dce_provenance_marks_removed_inst_optimized_away() {
        let add = MachInst::new(AArch64Opcode::AddRR, vec![vreg(0), vreg(1), vreg(2)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![add, ret]);
        let dead_id = func.block(func.entry).insts[0];
        let ret_id = func.block(func.entry).insts[1];

        let mut provenance = ProvenanceMap::new();
        provenance.record_lowering(TrustIrInstId(10), &[dead_id], PassId::new("isel"));
        provenance.record_lowering(TrustIrInstId(11), &[ret_id], PassId::new("isel"));

        let mut dce = DeadCodeElimination;
        let mut analyses = AnalysisCache::new();
        assert!(dce.run_with_analyses_and_provenance(&mut func, &mut analyses, &mut provenance));

        let block = func.block(func.entry);
        assert_eq!(block.insts, vec![ret_id]);

        let dead_entry = provenance.get_entry(dead_id).unwrap();
        match &dead_entry.status {
            ProvenanceStatus::OptimizedAway {
                pass,
                justification,
            } => {
                assert_eq!(pass.name(), "dce");
                assert_eq!(justification, "unused instruction has no side effects");
            }
            other => panic!("expected optimized-away provenance, got {other:?}"),
        }
        assert_eq!(provenance.optimized_away()[0].0, dead_id);
        assert!(provenance.get_entry(ret_id).unwrap().is_active());
    }

    #[test]
    fn test_dce_provenance_marks_transitive_dead_chain_once() {
        let add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(0), vreg(1), imm(5)]);
        let sub = MachInst::new(AArch64Opcode::SubRI, vec![vreg(2), vreg(0), imm(1)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![add, sub, ret]);
        let add_id = func.block(func.entry).insts[0];
        let sub_id = func.block(func.entry).insts[1];
        let ret_id = func.block(func.entry).insts[2];

        let mut provenance = ProvenanceMap::new();
        provenance.record_lowering(TrustIrInstId(10), &[add_id], PassId::new("isel"));
        provenance.record_lowering(TrustIrInstId(11), &[sub_id], PassId::new("isel"));
        provenance.record_lowering(TrustIrInstId(12), &[ret_id], PassId::new("isel"));

        let mut dce = DeadCodeElimination;
        assert!(dce.run_with_provenance(&mut func, &mut provenance));

        let block = func.block(func.entry);
        assert_eq!(block.insts, vec![ret_id]);
        assert!(provenance.get_entry(add_id).unwrap().is_optimized_away());
        assert!(provenance.get_entry(sub_id).unwrap().is_optimized_away());
        assert!(provenance.get_entry(ret_id).unwrap().is_active());

        let optimized_away = provenance.optimized_away();
        assert_eq!(optimized_away.len(), 2);
        assert!(optimized_away.iter().any(|(id, _)| *id == add_id));
        assert!(optimized_away.iter().any(|(id, _)| *id == sub_id));
    }

    #[test]
    fn test_certified_dce_records_tied_def_use_operand_zero() {
        let movk = MachInst::new(AArch64Opcode::Movk, vec![vreg(7), imm(0x1234), imm(16)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![movk, ret]);

        let mut dce = DeadCodeElimination;
        let run = dce.run_certified(&mut func);

        assert!(run.changed);
        assert!(run.is_certified());
        assert_eq!(run.certificates.len(), 1);

        let cert = &run.certificates[0];
        assert_eq!(cert.source_opcode, "Movk");
        assert_eq!(cert.use_def.def_vreg, Some(7));
        assert_eq!(cert.use_def.use_vregs, vec![7]);
        assert!(!cert.use_def.def_is_used);

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 1);
        assert_eq!(func.inst(block.insts[0]).opcode, AArch64Opcode::Ret);
    }

    #[test]
    fn test_dce_preserves_used_add() {
        // v0 = add v1, #5
        // v2 = sub v0, #1  -- uses v0, so add is live
        // str v2, [sp, #8] -- side-effecting root keeps v2 live
        // ret
        let add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(0), vreg(1), imm(5)]);
        let sub = MachInst::new(AArch64Opcode::SubRI, vec![vreg(2), vreg(0), imm(1)]);
        let store = MachInst::new(AArch64Opcode::StrRI, vec![vreg(2), imm(8)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![add, sub, store, ret]);

        let mut dce = DeadCodeElimination;
        assert!(!dce.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 4);
        assert_eq!(func.inst(block.insts[0]).opcode, AArch64Opcode::AddRI);
        assert_eq!(func.inst(block.insts[1]).opcode, AArch64Opcode::SubRI);
        assert_eq!(func.inst(block.insts[2]).opcode, AArch64Opcode::StrRI);
        assert_eq!(func.inst(block.insts[3]).opcode, AArch64Opcode::Ret);
    }

    #[test]
    fn test_dce_removes_transitive_dead_chain_in_one_run() {
        // v0 = add v1, #5
        // v2 = sub v0, #1  -- dead, making v0 dead in the same DCE invocation
        // ret
        let add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(0), vreg(1), imm(5)]);
        let sub = MachInst::new(AArch64Opcode::SubRI, vec![vreg(2), vreg(0), imm(1)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![add, sub, ret]);

        let mut dce = DeadCodeElimination;
        assert!(dce.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 1);
        assert_eq!(func.inst(block.insts[0]).opcode, AArch64Opcode::Ret);
        assert!(!dce.run(&mut func));
    }

    #[test]
    fn test_dce_preserves_stores() {
        // str v0, [sp, #8] — has WRITES_MEMORY, never removed
        let store = MachInst::new(AArch64Opcode::StrRI, vec![vreg(0), imm(8)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![store, ret]);

        let mut dce = DeadCodeElimination;
        assert!(!dce.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 2);
    }

    #[test]
    fn test_dce_preserves_opcode_effect_barriers_even_without_flags() {
        let dmb = MachInst::with_flags(AArch64Opcode::Dmb, vec![imm(0)], InstFlags::EMPTY);
        let dsb = MachInst::with_flags(AArch64Opcode::Dsb, vec![imm(0)], InstFlags::EMPTY);
        let isb = MachInst::with_flags(AArch64Opcode::Isb, vec![imm(0)], InstFlags::EMPTY);
        let mrs = MachInst::with_flags(
            AArch64Opcode::Mrs,
            vec![vreg(0), imm(0xde82)],
            InstFlags::EMPTY,
        );
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![dmb, dsb, isb, mrs, ret]);

        let mut dce = DeadCodeElimination;
        assert!(!dce.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 5);
        assert_eq!(func.inst(block.insts[0]).opcode, AArch64Opcode::Dmb);
        assert_eq!(func.inst(block.insts[1]).opcode, AArch64Opcode::Dsb);
        assert_eq!(func.inst(block.insts[2]).opcode, AArch64Opcode::Isb);
        assert_eq!(func.inst(block.insts[3]).opcode, AArch64Opcode::Mrs);
    }

    #[test]
    fn test_dce_preserves_stack_alloc_from_opcode_effect() {
        let stack_alloc = MachInst::with_flags(
            AArch64Opcode::StackAlloc,
            vec![vreg(0), imm(4), imm(8), imm(16)],
            InstFlags::EMPTY,
        );
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![stack_alloc, ret]);

        let mut dce = DeadCodeElimination;
        assert!(!dce.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 2);
        assert_eq!(func.inst(block.insts[0]).opcode, AArch64Opcode::StackAlloc);
    }

    #[test]
    fn test_dce_preserves_branches() {
        let branch = MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(trust_cg_ir::BlockId(1))],
        );
        let mut func = make_func_with_insts(vec![branch]);

        let mut dce = DeadCodeElimination;
        assert!(!dce.run(&mut func));
    }

    #[test]
    fn test_dce_removes_nop() {
        let nop = MachInst::new(AArch64Opcode::Nop, vec![]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![nop, ret]);

        let mut dce = DeadCodeElimination;
        assert!(dce.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 1); // only ret
    }

    #[test]
    fn test_dce_preserves_cmp() {
        // cmp v0, v1 — sets flags, has HAS_SIDE_EFFECTS
        let cmp = MachInst::new(AArch64Opcode::CmpRR, vec![vreg(0), vreg(1)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![cmp, ret]);

        let mut dce = DeadCodeElimination;
        assert!(!dce.run(&mut func));
    }

    #[test]
    fn test_dce_preserves_inst_with_implicit_uses() {
        static IMPLICIT_USES: &[trust_cg_ir::PReg] = &[X0];

        let add = MachInst::new(AArch64Opcode::AddRR, vec![vreg(0), vreg(1), vreg(2)])
            .with_implicit_uses(IMPLICIT_USES);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![add, ret]);

        let mut dce = DeadCodeElimination;
        assert!(!dce.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 2);
    }

    #[test]
    fn test_dce_idempotent() {
        let add = MachInst::new(AArch64Opcode::AddRR, vec![vreg(0), vreg(1), vreg(2)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![add, ret]);

        let mut dce = DeadCodeElimination;
        assert!(dce.run(&mut func)); // First pass removes dead add
        assert!(!dce.run(&mut func)); // Second pass: nothing to do
    }

    #[test]
    fn test_dce_certified_removes_unused_add_with_certificate() {
        let add = MachInst::new(AArch64Opcode::AddRR, vec![vreg(0), vreg(1), vreg(2)])
            .with_source_loc(trust_cg_ir::SourceLoc {
                file: 7,
                line: 11,
                col: 13,
            });
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![add, ret]);

        let mut dce = DeadCodeElimination;
        let run = dce.run_certified(&mut func);

        assert!(run.changed);
        assert!(run.is_certified());
        assert_eq!(run.certificates.len(), 1);
        assert!(run.failures.is_empty());

        let cert = &run.certificates[0];
        assert_eq!(cert.pass_name, "dce");
        assert_eq!(cert.source_opcode, "AddRR");
        assert_eq!(cert.source_location.as_deref(), Some("file:7:11:13"));
        assert_eq!(cert.use_def.def_vreg, Some(0));
        assert_eq!(cert.use_def.use_vregs, vec![1, 2]);
        assert!(!cert.use_def.def_is_used);
        assert_eq!(cert.side_effects.memory_effect, "Pure");
        assert!(cert.side_effects.is_pure);
        assert!(!cert.side_effects.has_side_effect_barrier);
        assert!(!cert.visibility.graph_output_visible);
        assert!(!cert.visibility.certificate_output_visible);
        assert_eq!(cert.result, DceCertificateResult::Verified);

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 1);
    }

    #[test]
    fn test_dce_certified_liveness_is_class_exact_with_numeric_certificate_facts() {
        let gpr_v0_def = MachInst::new(AArch64Opcode::AddRR, vec![vreg(0), vreg(1), vreg(2)]);
        let fpr_v0_store = MachInst::new(
            AArch64Opcode::StrRI,
            vec![vreg_class(0, RegClass::Fpr64), imm(8)],
        );
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![gpr_v0_def, fpr_v0_store, ret]);

        let mut dce = DeadCodeElimination;
        let run = dce.run_certified(&mut func);

        assert!(run.changed);
        assert!(run.is_certified());
        assert_eq!(run.certificates.len(), 1);

        let cert = &run.certificates[0];
        assert_eq!(cert.source_opcode, "AddRR");
        assert_eq!(cert.use_def.def_vreg, Some(0));
        assert_eq!(cert.use_def.use_vregs, vec![1, 2]);
        assert!(
            !cert.use_def.def_is_used,
            "same numeric id in a different register class must not keep the GPR def live"
        );

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 2);
        assert_eq!(func.inst(block.insts[0]).opcode, AArch64Opcode::StrRI);
        assert_eq!(func.inst(block.insts[1]).opcode, AArch64Opcode::Ret);
    }

    #[test]
    fn test_dce_certified_removes_transitive_dead_chain_with_certificates() {
        let add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(0), vreg(1), imm(5)]);
        let sub = MachInst::new(AArch64Opcode::SubRI, vec![vreg(2), vreg(0), imm(1)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![add, sub, ret]);

        let mut dce = DeadCodeElimination;
        let run = dce.run_certified(&mut func);

        assert!(run.changed);
        assert!(run.is_certified());
        assert_eq!(run.certificates.len(), 2);
        assert!(run.failures.is_empty());

        let mut opcodes = run
            .certificates
            .iter()
            .map(|cert| cert.source_opcode.as_str())
            .collect::<Vec<_>>();
        opcodes.sort_unstable();
        assert_eq!(opcodes, vec!["AddRI", "SubRI"]);
        assert!(
            run.certificates
                .iter()
                .all(|cert| cert.result == DceCertificateResult::Verified
                    && !cert.use_def.def_is_used)
        );

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 1);
        assert_eq!(func.inst(block.insts[0]).opcode, AArch64Opcode::Ret);
    }

    #[test]
    fn test_certified_dce_wrapper_drains_neutral_run_record() {
        let add = MachInst::new(AArch64Opcode::AddRR, vec![vreg(0), vreg(1), vreg(2)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![add, ret]);

        let mut pass = CertifiedDeadCodeElimination::new();
        assert!(pass.run(&mut func));
        let records = pass.take_certified_pass_runs();

        assert_eq!(records.len(), 1);
        let record = &records[0];
        assert!(record.is_verified());
        assert_eq!(record.pass_name, "dce-pure-unused");
        assert_eq!(record.function_name, "test_dce");
        assert_eq!(record.certificate_count, 1);
        assert_eq!(record.failure_count, 0);
        assert!(
            record
                .obligation_hash
                .starts_with("trust-cg-opt-certified-pass-run-v1:")
        );
        assert_eq!(
            record.summary["certificates"][0]["source_opcode"].as_str(),
            Some("AddRR")
        );
    }

    #[test]
    fn test_dce_certified_fails_closed_for_graph_output() {
        let add = MachInst::new(AArch64Opcode::AddRR, vec![vreg(0), vreg(1), vreg(2)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![add, ret]);

        let mut graph_outputs = HashSet::new();
        graph_outputs.insert(0);
        let mut dce = DeadCodeElimination;
        let run = dce.run_certified_with_options(
            &mut func,
            DceCertifiedOptions {
                graph_output_vregs: graph_outputs,
                certificate_visible_vregs: HashSet::new(),
            },
        );

        assert!(!run.changed);
        assert!(!run.is_certified());
        assert!(run.certificates.is_empty());
        assert_eq!(run.failures.len(), 1);
        assert!(run.failures[0].reason.contains("graph-output visible"));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 2);
    }

    #[test]
    fn test_dce_certified_fails_closed_for_certificate_visible_value() {
        let add = MachInst::new(AArch64Opcode::AddRR, vec![vreg(0), vreg(1), vreg(2)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![add, ret]);

        let mut certificate_visible = HashSet::new();
        certificate_visible.insert(0);
        let mut dce = DeadCodeElimination;
        let run = dce.run_certified_with_options(
            &mut func,
            DceCertifiedOptions {
                graph_output_vregs: HashSet::new(),
                certificate_visible_vregs: certificate_visible,
            },
        );

        assert!(!run.changed);
        assert!(!run.is_certified());
        assert!(run.certificates.is_empty());
        assert_eq!(run.failures.len(), 1);
        assert!(
            run.failures[0]
                .reason
                .contains("certificate-output visible")
        );

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 2);
    }

    #[test]
    fn test_dce_certified_fails_closed_for_unused_load() {
        let load = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(0), vreg(1), imm(8)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![load, ret]);

        let mut dce = DeadCodeElimination;
        let run = dce.run_certified(&mut func);

        assert!(!run.changed);
        assert!(!run.is_certified());
        assert!(run.certificates.is_empty());
        assert_eq!(run.failures.len(), 1);
        assert!(run.failures[0].reason.contains("memory reads"));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 2);
    }

    #[test]
    fn test_dce_certified_preserves_store_call_and_branch_without_certificates() {
        let store = MachInst::new(AArch64Opcode::StrRI, vec![vreg(0), imm(8)]);
        let call = MachInst::new(
            AArch64Opcode::Bl,
            vec![MachOperand::Symbol("callee".into())],
        );
        let branch = MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(trust_cg_ir::BlockId(1))],
        );
        let mut func = make_func_with_insts(vec![store, call, branch]);

        let mut dce = DeadCodeElimination;
        let run = dce.run_certified(&mut func);

        assert!(!run.changed);
        assert!(run.is_certified());
        assert!(run.certificates.is_empty());
        assert!(run.failures.is_empty());

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 3);
    }
}
