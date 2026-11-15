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

use crate::fast_hash::FxHashSet as HashSet;

use serde::{Deserialize, Serialize};
use trust_cg_ir::{
    AArch64Opcode, InstFlags, InstId, MachFunction, MachOperand, PassId, ProvenanceMap, VReg,
};

use crate::cache::StableHasher;
use crate::effects::{
    MemoryEffect, aarch64_for_each_def_position, aarch64_for_each_use_position,
    aarch64_use_operand_positions, definitely_writes_flags, nzcv_unknown, opcode_effect,
    reads_nzcv, single_inst_def,
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
    /// Removing a def-less NZCV writer (CMP/TST) whose flags are overwritten by
    /// the next NZCV writer in the same block before any reader, call, branch,
    /// terminator, or opaque pseudo preserves every observable output: the only
    /// state it writes is dead on every path.
    DeadNzcvWriteUnobservable,
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

/// Where the flags written by a removed dead flag write die
/// (`DceContract::DeadNzcvWriteUnobservable`).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum DeadFlagsExit {
    /// Overwritten by this NZCV writer later in the same block.
    NextWriter { inst_id: u32 },
    /// The block ends (in a non-flag-reading terminator) and NZCV is dead on
    /// entry to every listed successor: from each, every path reaches an NZCV
    /// writer, or the function's exit, before any reader.
    CfgDead { blocks: Vec<u32> },
}

/// NZCV facts recorded for a removed dead flag write
/// (`DceContract::DeadNzcvWriteUnobservable`).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct DceFlagsFacts {
    /// The opcode writes NZCV and defines no register (CMP/TST forms).
    pub flags_only_writer: bool,
    /// Instructions between the write and the end of the in-block scan, none
    /// of which reads NZCV, is an opaque pseudo, or carries implicit operands
    /// (calls are neutral: a reader after one still counts).
    pub insts_between: u32,
    /// How the flags die.
    pub exit: DeadFlagsExit,
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
    /// Present exactly for `DeadNzcvWriteUnobservable` certificates.
    #[serde(default)]
    pub nzcv: Option<DceFlagsFacts>,
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
    let mut seen_failures = HashSet::default();
    // Keep originals through every removal wave: certificates may name a
    // NextWriter that is itself removed later. Tombstones are not proof inputs.
    let mut retired_flag_writes = HashSet::default();

    loop {
        // Step 1: Collect all VRegs that are *used* (appear as source
        // operands) across the current function.
        let used_vregs = collect_used_vregs(func);

        // Step 2: Find instructions to remove. An instruction is dead if:
        //   (a) it defines a VReg not in the used set, AND
        //   (b) it has no side effects.
        let mut dead_insts: HashSet<InstId> = HashSet::default();
        let mut dead_flag_writes: HashSet<InstId> = HashSet::default();
        // NZCV liveness for this wave (removals change positions, so per wave).
        let nzcv = NzcvLiveness::compute(func);

        for block_id in func.block_order.clone() {
            let block = func.block(block_id);
            for (pos, &inst_id) in block.insts.iter().enumerate() {
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

                // Never remove instructions with side effects — except a
                // flags-only writer whose NZCV result is dead in its block
                // (`dead_flags_write`), whose only side effect is that write.
                let dead_nzcv = if def_vreg.is_none() && is_flags_only_writer(inst.opcode) {
                    nzcv.dead_flags_write(func, block_id.0 as usize, pos)
                } else {
                    None
                };
                if has_side_effects(inst) && dead_nzcv.is_none() {
                    continue;
                }

                // Check if any defined VReg is used.
                match def_vreg {
                    Some(vreg) => {
                        if !used_vregs.contains(&vreg) {
                            if let Some(options) = certified_options {
                                let cert =
                                    make_dce_certificate(inst_id, inst, &used_vregs, options, None);
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
                    // only Nop qualifies here — plus a flags-only writer whose
                    // NZCV result is provably dead within its block.
                    None => {
                        if inst.is_nop() {
                            if let Some(options) = certified_options {
                                let cert =
                                    make_dce_certificate(inst_id, inst, &used_vregs, options, None);
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
                        } else if let Some(nzcv) = dead_nzcv {
                            if let Some(options) = certified_options {
                                let cert = make_dce_certificate(
                                    inst_id,
                                    inst,
                                    &used_vregs,
                                    options,
                                    Some(nzcv),
                                );
                                if cert.result != DceCertificateResult::Verified {
                                    push_unique_dce_failure(
                                        &mut failures,
                                        &mut seen_failures,
                                        inst_id,
                                        inst,
                                        "local dead-NZCV-write checker failed".to_string(),
                                    );
                                    continue;
                                }
                                certificates.push(cert);
                            }
                            dead_flag_writes.insert(inst_id);
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
                if dead_flag_writes.contains(&inst_id) {
                    continue;
                }
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
        retired_flag_writes.extend(dead_flag_writes);
    }

    // One whole-function link scan, not one scan per removed ID. In particular,
    // a block omitted from block_order still owns its instruction references.
    // Never sweep unrelated pre-existing orphan arena entries.
    if !retired_flag_writes.is_empty() {
        for block in &func.blocks {
            for id in &block.insts {
                retired_flag_writes.remove(id);
            }
        }
        let mut retired: Vec<_> = retired_flag_writes.into_iter().collect();
        retired.sort_unstable();
        for id in retired {
            if let Some(provenance) = provenance.as_deref_mut() {
                provenance.record_deletion(
                    id,
                    PassId::new("dce"),
                    "flags-only write dead before any NZCV reader on every path",
                );
            }
            // Stable IDs and lowering-provenance sidecars remain historical.
            // Drop the removed instruction's executable operands/metadata only
            // after the original local checker snapshots have been retained.
            *func.inst_mut(id) = trust_cg_ir::MachInst::new(AArch64Opcode::Nop, vec![]);
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
    let mut used = HashSet::default();

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

/// A def-less NZCV writer: its ONLY effect is the flags (CMP/TST forms; not
/// ADDS/SUBS, which define a register, and not FCMP).
fn is_flags_only_writer(opcode: AArch64Opcode) -> bool {
    use AArch64Opcode::*;
    matches!(
        opcode,
        CmpRR | CmpRI | CMPWrr | CMPXrr | CMPWri | CMPXri | Tst
    )
}

/// The exact existing encoder grammar for the removable integer CMP/TST slice,
/// also admitting well-typed in-arena VRegs before register allocation. Invalid
/// effects/shapes stay visible for later refusal; an annotation is not licensed
/// for erasure merely because the instruction's NZCV result is dead.
fn canonical_flags_only_writer(func: &MachFunction, inst: &trust_cg_ir::MachInst) -> bool {
    use AArch64Opcode::*;
    if !is_flags_only_writer(inst.opcode)
        || inst.flags != inst.opcode.default_flags()
        || !inst.implicit_defs.is_empty()
        || !inst.implicit_uses.is_empty()
        || inst.proof.is_some()
    {
        return false;
    }
    let [lhs, rhs] = inst.operands.as_slice() else {
        return false;
    };
    let immediate_cmp = matches!(inst.opcode, CmpRI | CMPWri | CMPXri);
    let Some(width) = comparison_register_width(func, lhs, immediate_cmp) else {
        return false;
    };
    if matches!(inst.opcode, CMPWrr | CMPWri) && width != 32
        || matches!(inst.opcode, CMPXrr | CMPXri) && width != 64
    {
        return false;
    }
    if immediate_cmp {
        matches!(rhs, MachOperand::Imm(0..=4095))
    } else if inst.opcode == Tst
        && let MachOperand::Imm(mask) = rhs
    {
        crate::const_materialize::is_logical_immediate(*mask as u64, width)
    } else {
        comparison_register_width(func, rhs, false) == Some(width)
    }
}

/// Register 31 is SP for immediate CMP and ZR for register CMP/TST. These
/// encodable domains are intentionally not inferred from generic use roles.
fn comparison_register_width(
    func: &MachFunction,
    operand: &MachOperand,
    immediate_cmp: bool,
) -> Option<u32> {
    use trust_cg_ir::regs::{RegClass, SpecialReg};
    match operand {
        MachOperand::VReg(vreg) if vreg.id < func.next_vreg => match vreg.class {
            RegClass::Gpr32 => Some(32),
            RegClass::Gpr64 => Some(64),
            _ => None,
        },
        MachOperand::PReg(reg) => match (reg.encoding(), immediate_cmp) {
            (0..=30, _) | (31, true) | (160, false) => Some(64),
            (32..=62, _) | (63, true) | (161, false) => Some(32),
            _ => None,
        },
        MachOperand::Special(SpecialReg::SP) if immediate_cmp => Some(64),
        MachOperand::Special(SpecialReg::XZR) if !immediate_cmp => Some(64),
        MachOperand::Special(SpecialReg::WZR) if !immediate_cmp => Some(32),
        _ => None,
    }
}

/// `TCG_TRACE_DEADFLAGS=1`: why a cross-block flag-liveness scan answered
/// "live" (diagnostic; one line per refusal).
fn trace_dead_flags(msg: impl FnOnce() -> String) {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    if *ON.get_or_init(|| std::env::var_os("TCG_TRACE_DEADFLAGS").is_some()) {
        eprintln!("TCG_DEADFLAGS live: {}", msg());
    }
}

/// What an instruction does to a live NZCV value, for the liveness below.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum FlagEvent {
    /// Reads NZCV (CSET/CSEL family, ADC/SBC, B.cond): the value is live.
    Read,
    /// Writes NZCV without reading it: the previous value dies here.
    Kill,
    /// Unknown effect (an opaque pseudo, implicit operands): fail towards live.
    Opaque,
}

/// Block-level NZCV liveness for one DCE wave, computed once per function:
/// per block the positions of its flag events, and whether NZCV is LIVE on
/// entry (some path from the block's top reaches a reader before a writer).
/// Calls are transparent: NZCV is not an argument under AAPCS64, so a callee
/// cannot rely on it, but a reader after the call on the same path still
/// counts. Cycles of transparent blocks are dead (least fixpoint from
/// `false`), which is the same answer the verifier's visited-set walk gives.
struct NzcvLiveness {
    /// Per block (indexed by `BlockId`): `(position, event, inst id)`, in order.
    events: Vec<Vec<(usize, FlagEvent, u32)>>,
    /// Per block: NZCV live on entry.
    live_in: Vec<bool>,
    /// Flags-only IDs linked exactly once across ALL blocks. Removing a shared
    /// ID based on one dead occurrence must not erase another live occurrence.
    unique_flag_writes: HashSet<InstId>,
}

impl NzcvLiveness {
    fn event_of(func: &MachFunction, inst: &trust_cg_ir::MachInst) -> Option<FlagEvent> {
        let op = inst.opcode;
        if reads_nzcv(inst) {
            return Some(FlagEvent::Read);
        }
        if nzcv_unknown(inst) {
            return Some(FlagEvent::Opaque);
        }
        // Preserve DCE's conservative reader-after-call policy. Ordinary ABI
        // argument/clobber lists are not NZCV reads; explicit NZCV operands
        // have already been handled above. A forged IS_CALL bit is not an ABI.
        if op.default_flags().contains(InstFlags::IS_CALL) {
            return None;
        }
        if (inst.is_pseudo() && !inst.is_nop())
            || !inst.implicit_defs.is_empty()
            || !inst.implicit_uses.is_empty()
        {
            return Some(FlagEvent::Opaque);
        }
        if definitely_writes_flags(op) {
            // Do not let a malformed or annotated comparison hide an earlier
            // producer by claiming a well-formed guaranteed overwrite.
            return Some(
                if is_flags_only_writer(op) && !canonical_flags_only_writer(func, inst) {
                    FlagEvent::Opaque
                } else {
                    FlagEvent::Kill
                },
            );
        }
        None
    }

    fn compute(func: &MachFunction) -> Self {
        let nblocks = func.blocks.len();
        let mut events: Vec<Vec<(usize, FlagEvent, u32)>> = vec![Vec::new(); nblocks];
        let mut unique_flag_writes = HashSet::default();
        let mut shared_flag_writes = HashSet::default();
        for (b, block) in func.blocks.iter().enumerate() {
            for (pos, &inst_id) in block.insts.iter().enumerate() {
                let Some(inst) = func.insts.get(inst_id.0 as usize) else {
                    events[b].push((pos, FlagEvent::Opaque, inst_id.0));
                    continue;
                };
                if is_flags_only_writer(inst.opcode) && !unique_flag_writes.insert(inst_id) {
                    shared_flag_writes.insert(inst_id);
                }
                if let Some(ev) = Self::event_of(func, inst) {
                    events[b].push((pos, ev, inst_id.0));
                }
            }
        }
        unique_flag_writes.retain(|id| !shared_flag_writes.contains(id));
        // Least fixpoint: live_in[b] = first event is Read/Opaque, or (no
        // event) any successor live on entry.
        let mut live_in = vec![false; nblocks];
        loop {
            let mut changed = false;
            for (b, block) in func.blocks.iter().enumerate() {
                let v = match events[b].first() {
                    Some((_, FlagEvent::Read | FlagEvent::Opaque, _)) => true,
                    Some((_, FlagEvent::Kill, _)) => false,
                    None => block
                        .succs
                        .iter()
                        .any(|s| live_in.get(s.0 as usize).copied().unwrap_or(true)),
                };
                if v && !live_in[b] {
                    live_in[b] = true;
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        Self {
            events,
            live_in,
            unique_flag_writes,
        }
    }

    /// If the NZCV written by the flags-only writer at `pos` of block `b` is
    /// dead — the next flag event in the block is a writer, or the block ends
    /// with NZCV dead on entry to every successor — return the certificate
    /// facts; `None` when a reader or something opaque comes first.
    fn dead_flags_write(&self, func: &MachFunction, b: usize, pos: usize) -> Option<DceFlagsFacts> {
        let block = func.blocks.get(b)?;
        let id = *block.insts.get(pos)?;
        let inst = func.inst(id);
        if !self.unique_flag_writes.contains(&id) || !canonical_flags_only_writer(func, inst) {
            return None;
        }
        let evs = &self.events[b];
        let next = evs.partition_point(|(p, _, _)| *p <= pos);
        match evs.get(next) {
            Some((p, FlagEvent::Kill, id)) => Some(DceFlagsFacts {
                flags_only_writer: true,
                insts_between: (*p - pos - 1) as u32,
                exit: DeadFlagsExit::NextWriter { inst_id: *id },
            }),
            Some((_, FlagEvent::Read | FlagEvent::Opaque, _)) => None,
            None => {
                // The flags leave the block: dead iff dead on entry to every
                // successor (a return has none — NZCV is caller-saved).
                let live = block
                    .succs
                    .iter()
                    .filter(|s| self.live_in.get(s.0 as usize).copied().unwrap_or(true))
                    .map(|s| s.0)
                    .collect::<Vec<_>>();
                if !live.is_empty() {
                    trace_dead_flags(|| {
                        format!("block {b}: NZCV live on entry to successor(s) {live:?}")
                    });
                    return None;
                }
                Some(DceFlagsFacts {
                    flags_only_writer: true,
                    insts_between: (block.insts.len() - pos - 1) as u32,
                    exit: DeadFlagsExit::CfgDead {
                        blocks: block.succs.iter().map(|s| s.0).collect(),
                    },
                })
            }
        }
    }
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
    nzcv: Option<DceFlagsFacts>,
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
    let contract = if nzcv.is_some() {
        DceContract::DeadNzcvWriteUnobservable
    } else {
        DceContract::PureUnusedValueUnobservable
    };
    let obligation_hash = dce_obligation_hash(
        inst_id,
        &source_opcode,
        &source_operands,
        &source_location,
        &use_def,
        &side_effects,
        &visibility,
        nzcv.as_ref(),
    );
    let result = if check_dce_obligation(inst, &use_def, &side_effects, &visibility, nzcv.as_ref())
    {
        DceCertificateResult::Verified
    } else {
        DceCertificateResult::Failed
    };
    let (pass_instance_id, domain, checker) = match contract {
        DceContract::PureUnusedValueUnobservable => (
            "dce:bound-propagation:pure-unused:v1",
            "bound-propagation;scalar-bv64;observable-outputs=graph+certificate",
            "trust-cg-opt analytical bound-propagation DCE checker v1",
        ),
        DceContract::DeadNzcvWriteUnobservable => (
            "dce:nzcv:dead-write:v1",
            "block-local NZCV liveness;observable-outputs=graph+certificate+flags",
            "trust-cg-opt block-local dead-NZCV-write checker v1",
        ),
    };

    DceCertificate {
        format_version: 1,
        pass_name: "dce".to_string(),
        pass_version: 1,
        pass_instance_id: pass_instance_id.to_string(),
        source_inst_id: inst_id.0,
        source_opcode,
        source_operands,
        source_location,
        use_def,
        side_effects,
        visibility,
        nzcv,
        contract,
        domain: domain.to_string(),
        obligation_hash,
        checker: checker.to_string(),
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

#[allow(clippy::too_many_arguments)]
fn dce_obligation_hash(
    inst_id: InstId,
    source_opcode: &str,
    source_operands: &[String],
    source_location: &Option<String>,
    use_def: &DceUseDefFacts,
    side_effects: &DceSideEffectFacts,
    visibility: &DceVisibilityFacts,
    nzcv: Option<&DceFlagsFacts>,
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
    match nzcv {
        Some(f) => {
            h.write_str("nzcv-dead-write");
            h.write_u8(u8::from(f.flags_only_writer));
            h.write_u32(f.insts_between);
            match &f.exit {
                DeadFlagsExit::NextWriter { inst_id } => {
                    h.write_u8(1);
                    h.write_u32(*inst_id);
                }
                DeadFlagsExit::CfgDead { blocks } => {
                    h.write_u8(2);
                    h.write_u32(blocks.len() as u32);
                    for b in blocks {
                        h.write_u32(*b);
                    }
                }
            }
        }
        None => h.write_u8(0),
    }
    format!("{:032x}", h.finish128())
}

fn check_dce_obligation(
    inst: &trust_cg_ir::MachInst,
    use_def: &DceUseDefFacts,
    side_effects: &DceSideEffectFacts,
    visibility: &DceVisibilityFacts,
    nzcv: Option<&DceFlagsFacts>,
) -> bool {
    let unobservable = !use_def.def_is_used
        && side_effects.is_pure
        && !visibility.graph_output_visible
        && !visibility.certificate_output_visible;
    match nzcv {
        // A dead flag write: no register def, the flags are its only side
        // effect (the barrier bit is exactly HAS_SIDE_EFFECTS for NZCV), and
        // the recorded next writer follows with nothing between that could
        // read or carry the flags.
        Some(f) => {
            unobservable
                && use_def.def_vreg.is_none()
                && f.flags_only_writer
                && is_flags_only_writer(inst.opcode)
                && inst.implicit_defs.is_empty()
                && inst.implicit_uses.is_empty()
                && inst.flags.contains(InstFlags::HAS_SIDE_EFFECTS)
                && !inst.flags.contains(InstFlags::READS_MEMORY)
                && !inst.flags.contains(InstFlags::WRITES_MEMORY)
                && !inst.flags.contains(InstFlags::IS_CALL)
                && !inst.flags.contains(InstFlags::IS_BRANCH)
                && !inst.flags.contains(InstFlags::IS_TERMINATOR)
        }
        None => {
            (use_def.def_vreg.is_some() || inst.is_nop())
                && unobservable
                && !side_effects.has_side_effect_barrier
        }
    }
}

#[cfg(test)]
#[path = "dce_retirement_tests.rs"]
mod retirement_tests;

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
        func.try_sync_vreg_counter().expect("test VReg arena fits");
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
        // cmp v0, v1 — sets flags (HAS_SIDE_EFFECTS); its CSET reader, kept
        // live by a store, keeps it.
        let cmp = MachInst::new(AArch64Opcode::CmpRR, vec![vreg(0), vreg(1)]);
        let cset = MachInst::new(AArch64Opcode::CSet, vec![vreg(4), imm(0)]);
        let store = MachInst::new(AArch64Opcode::StrRI, vec![vreg(4), imm(8)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![cmp, cset, store, ret]);

        let mut dce = DeadCodeElimination;
        assert!(!dce.run(&mut func));
    }

    /// NZCV is caller-saved and meaningless after RET: a CMP whose flags reach
    /// the function's exit unread is a dead write and goes.
    #[test]
    fn test_dce_removes_cmp_whose_flags_die_at_return() {
        let mut func = make_func_with_insts(vec![
            MachInst::new(AArch64Opcode::CmpRR, vec![vreg(0), vreg(1)]),
            MachInst::new(AArch64Opcode::Ret, vec![]),
        ]);
        let mut dce = DeadCodeElimination;
        let run = dce.run_certified(&mut func);
        assert!(run.changed && run.is_certified());
        assert_eq!(func.block(func.entry).insts.len(), 1);
        assert!(matches!(
            run.certificates[0].nzcv.as_ref().unwrap().exit,
            DeadFlagsExit::CfgDead { ref blocks } if blocks.is_empty()
        ));
    }

    /// A CMP whose flags are overwritten by the next CMP before any reader is
    /// a dead flag write: removed, with a `DeadNzcvWriteUnobservable`
    /// certificate naming the overwriting instruction. The live CMP's CSET is
    /// kept alive by a store of its result.
    #[test]
    fn test_dce_removes_cmp_overwritten_before_any_reader() {
        let dead = MachInst::new(AArch64Opcode::CmpRR, vec![vreg(0), vreg(1)]);
        let nop = MachInst::new(AArch64Opcode::Nop, vec![]);
        let live = MachInst::new(AArch64Opcode::CmpRR, vec![vreg(2), vreg(3)]);
        let cset = MachInst::new(AArch64Opcode::CSet, vec![vreg(4), imm(2)]);
        let store = MachInst::new(AArch64Opcode::StrRI, vec![vreg(4), imm(8)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![dead, nop, live, cset, store, ret]);
        let live_id = func.block(func.entry).insts[2];

        let mut dce = DeadCodeElimination;
        let run = dce.run_certified(&mut func);
        assert!(run.changed);
        assert!(run.is_certified(), "failures: {:?}", run.failures);
        let opcodes: Vec<_> = func
            .block(func.entry)
            .insts
            .iter()
            .map(|id| func.inst(*id).opcode)
            .collect();
        assert_eq!(
            opcodes,
            vec![
                AArch64Opcode::CmpRR,
                AArch64Opcode::CSet,
                AArch64Opcode::StrRI,
                AArch64Opcode::Ret
            ],
            "the dead CMP and the Nop go, the live CMP stays"
        );
        let flag_certs: Vec<_> = run
            .certificates
            .iter()
            .filter(|c| c.contract == DceContract::DeadNzcvWriteUnobservable)
            .collect();
        assert_eq!(flag_certs.len(), 1);
        let cert = flag_certs[0];
        assert_eq!(cert.source_opcode, "CmpRR");
        assert_eq!(cert.result, DceCertificateResult::Verified);
        assert_eq!(cert.pass_instance_id, "dce:nzcv:dead-write:v1");
        let facts = cert.nzcv.as_ref().expect("nzcv facts");
        assert!(facts.flags_only_writer);
        assert_eq!(facts.exit, DeadFlagsExit::NextWriter { inst_id: live_id.0 });
        assert_eq!(facts.insts_between, 1);
    }

    /// Flags carried out of the block by a non-reading terminator (CBZ) are
    /// dead when every successor writes NZCV before reading it — including
    /// through a loop back-edge — and live as soon as one successor reads
    /// them first.
    #[test]
    fn test_dce_dead_flag_write_across_the_cfg() {
        // entry: cmp v0,v1 ; cbz v2 -> exit   (fallthrough -> body)
        // body:  cmp v2,v3 ; cset v4 ; str v4 ; cbz v2 -> body (loop)  (fallthrough -> exit)
        // exit:  ret
        let build = |exit_reads_first: bool| {
            let mut func = MachFunction::new("t".to_string(), Signature::new(vec![], vec![]));
            let entry = func.entry;
            let body = func.create_block();
            let exit = func.create_block();
            let add = |func: &mut MachFunction, b, i: MachInst| {
                let id = func.push_inst(i);
                func.append_inst(b, id);
                id
            };
            let dead = add(
                &mut func,
                entry,
                MachInst::new(AArch64Opcode::CmpRR, vec![vreg(0), vreg(1)]),
            );
            add(
                &mut func,
                entry,
                MachInst::new(AArch64Opcode::Cbz, vec![vreg(2), MachOperand::Block(exit)]),
            );
            add(
                &mut func,
                body,
                MachInst::new(AArch64Opcode::CmpRR, vec![vreg(2), vreg(3)]),
            );
            add(
                &mut func,
                body,
                MachInst::new(AArch64Opcode::CSet, vec![vreg(4), imm(0)]),
            );
            add(
                &mut func,
                body,
                MachInst::new(AArch64Opcode::StrRI, vec![vreg(4), imm(8)]),
            );
            add(
                &mut func,
                body,
                MachInst::new(AArch64Opcode::Cbz, vec![vreg(2), MachOperand::Block(body)]),
            );
            if exit_reads_first {
                add(
                    &mut func,
                    exit,
                    MachInst::new(AArch64Opcode::CSet, vec![vreg(5), imm(1)]),
                );
                add(
                    &mut func,
                    exit,
                    MachInst::new(AArch64Opcode::StrRI, vec![vreg(5), imm(16)]),
                );
            }
            add(&mut func, exit, MachInst::new(AArch64Opcode::Ret, vec![]));
            func.add_edge(entry, exit);
            func.add_edge(entry, body);
            func.add_edge(body, body);
            func.add_edge(body, exit);
            func.try_sync_vreg_counter().expect("test VReg arena fits");
            (func, dead)
        };

        let (mut func, dead) = build(false);
        let mut dce = DeadCodeElimination;
        let run = dce.run_certified(&mut func);
        assert!(run.is_certified(), "failures: {:?}", run.failures);
        assert!(
            !func.block(func.entry).insts.contains(&dead),
            "the entry CMP is dead across the CFG"
        );
        let cert = run
            .certificates
            .iter()
            .find(|c| c.contract == DceContract::DeadNzcvWriteUnobservable)
            .expect("a dead-flag certificate");
        match &cert.nzcv.as_ref().unwrap().exit {
            DeadFlagsExit::CfgDead { blocks } => {
                assert_eq!(blocks.len(), 2, "exit and body checked: {blocks:?}")
            }
            other => panic!("expected CfgDead, got {other:?}"),
        }
        assert_eq!(
            func.block(trust_cg_ir::BlockId(1)).insts.len(),
            4,
            "the body's live CMP stays"
        );

        let (mut func, dead) = build(true);
        let run = DeadCodeElimination.run_certified(&mut func);
        assert!(
            func.block(func.entry).insts.contains(&dead),
            "a successor reads the flags first: kept"
        );
        assert!(
            run.certificates
                .iter()
                .all(|c| c.contract != DceContract::DeadNzcvWriteUnobservable)
        );
    }

    /// Every way the flags can be read keeps the CMP under test (the first
    /// instruction): a live reader (CSET, CSEL, ADC — each kept live by a
    /// store of its result), a conditional branch, a reader after a call, or
    /// an unconditional branch to a block that reads before writing.
    #[test]
    fn test_dce_keeps_cmp_whose_flags_may_be_read() {
        let cmp = || MachInst::new(AArch64Opcode::CmpRR, vec![vreg(0), vreg(1)]);
        let ret = || MachInst::new(AArch64Opcode::Ret, vec![]);
        let keep = || MachInst::new(AArch64Opcode::StrRI, vec![vreg(4), imm(8)]);
        let block0 = MachOperand::Block(trust_cg_ir::BlockId(0));
        let cases: Vec<(&str, Vec<MachInst>)> = vec![
            (
                "cset reader",
                vec![
                    cmp(),
                    MachInst::new(AArch64Opcode::CSet, vec![vreg(4), imm(0)]),
                    keep(),
                    ret(),
                ],
            ),
            (
                "csel reader",
                vec![
                    cmp(),
                    MachInst::new(AArch64Opcode::Csel, vec![vreg(4), vreg(0), vreg(1), imm(0)]),
                    keep(),
                    ret(),
                ],
            ),
            (
                "conditional branch reader",
                vec![
                    cmp(),
                    MachInst::new(AArch64Opcode::BCond, vec![imm(0), block0.clone()]),
                ],
            ),
            (
                "reader after a call still counts",
                vec![
                    cmp(),
                    MachInst::new(
                        AArch64Opcode::Bl,
                        vec![MachOperand::Symbol("f".to_string())],
                    ),
                    MachInst::new(AArch64Opcode::CSet, vec![vreg(4), imm(0)]),
                    keep(),
                    ret(),
                ],
            ),
            (
                "adc reads the carry",
                vec![
                    cmp(),
                    MachInst::new(AArch64Opcode::Adc, vec![vreg(4), vreg(0), vreg(1)]),
                    keep(),
                    ret(),
                ],
            ),
        ];
        for (label, insts) in cases {
            let mut func = make_func_with_insts(insts);
            let under_test = func.block(func.entry).insts[0];
            let run = DeadCodeElimination.run_certified(&mut func);
            assert!(
                func.block(func.entry).insts.contains(&under_test),
                "{label}: the CMP under test was removed ({:?})",
                run.certificates
            );
        }

        // An unconditional branch into a block that READS the flags first
        // keeps them live across the edge: entry = [cset(stored) ; cmp ; b entry].
        let mut func = make_func_with_insts(vec![
            MachInst::new(AArch64Opcode::CSet, vec![vreg(4), imm(0)]),
            keep(),
            cmp(),
            MachInst::new(AArch64Opcode::B, vec![block0.clone()]),
        ]);
        let entry = func.entry;
        func.add_edge(entry, entry);
        let under_test = func.block(entry).insts[2];
        DeadCodeElimination.run_certified(&mut func);
        assert!(
            func.block(entry).insts.contains(&under_test),
            "loop edge into a reader: kept"
        );
    }

    /// CMP; CMP#imm; TST; CSET(stored) — the first two flag writes are dead,
    /// the TST is live; a second run changes nothing.
    #[test]
    fn test_dce_dead_flag_write_is_idempotent() {
        let mut func = make_func_with_insts(vec![
            MachInst::new(AArch64Opcode::CmpRR, vec![vreg(0), vreg(1)]),
            MachInst::new(AArch64Opcode::CmpRI, vec![vreg(0), imm(7)]),
            MachInst::new(AArch64Opcode::Tst, vec![vreg(0), vreg(1)]),
            MachInst::new(AArch64Opcode::CSet, vec![vreg(4), imm(1)]),
            MachInst::new(AArch64Opcode::StrRI, vec![vreg(4), imm(8)]),
            MachInst::new(AArch64Opcode::Ret, vec![]),
        ]);
        let mut dce = DeadCodeElimination;
        assert!(dce.run(&mut func));
        assert_eq!(func.block(func.entry).insts.len(), 4);
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

        let mut graph_outputs = HashSet::default();
        graph_outputs.insert(0);
        let mut dce = DeadCodeElimination;
        let run = dce.run_certified_with_options(
            &mut func,
            DceCertifiedOptions {
                graph_output_vregs: graph_outputs,
                certificate_visible_vregs: HashSet::default(),
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

        let mut certificate_visible = HashSet::default();
        certificate_visible.insert(0);
        let mut dce = DeadCodeElimination;
        let run = dce.run_certified_with_options(
            &mut func,
            DceCertifiedOptions {
                graph_output_vregs: HashSet::default(),
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

    fn mrs_observed_before_overwrite(with_mrs: bool) -> MachFunction {
        let mut insts = vec![
            MachInst::new(AArch64Opcode::CmpRR, vec![vreg(0), vreg(1)]).with_source_loc(
                trust_cg_ir::SourceLoc {
                    file: 3,
                    line: 8,
                    col: 5,
                },
            ),
        ];
        if with_mrs {
            insts.extend([
                MachInst::new(AArch64Opcode::Mrs, vec![vreg(2), imm(0xDA10)]).with_source_loc(
                    trust_cg_ir::SourceLoc {
                        file: 3,
                        line: 9,
                        col: 7,
                    },
                ),
                MachInst::new(AArch64Opcode::StrRI, vec![vreg(2), vreg(6), imm(0)]),
            ]);
        }
        insts.extend([
            MachInst::new(AArch64Opcode::CmpRR, vec![vreg(4), vreg(5)]),
            MachInst::new(AArch64Opcode::CSet, vec![vreg(3), imm(0)]),
            MachInst::new(AArch64Opcode::StrRI, vec![vreg(3), vreg(6), imm(8)]),
            MachInst::new(AArch64Opcode::Ret, vec![]),
        ]);
        make_func_with_insts(insts)
    }

    #[test]
    fn dce_mrs_nzcv_observation_preserves_original_writer_in_plain_and_certified_modes() {
        for certified in [false, true] {
            let mut func = mrs_observed_before_overwrite(true);
            let before = format!("{func:?}");
            let mut provenance = ProvenanceMap::new();
            for index in 0..func.insts.len() {
                provenance.record_lowering(
                    TrustIrInstId(index as u32),
                    &[InstId(index as u32)],
                    PassId::new("isel"),
                );
            }
            let before_provenance = format!("{provenance:?}");
            let mut pass = DeadCodeElimination;
            if certified {
                let run = pass.run_certified_with_provenance(&mut func, &mut provenance);
                assert!(!run.changed);
                assert!(run.is_certified(), "{run:?}");
                assert!(run.certificates.is_empty());
            } else {
                assert!(!pass.run_with_provenance(&mut func, &mut provenance));
            }
            assert_eq!(format!("{func:?}"), before);
            assert_eq!(format!("{provenance:?}"), before_provenance);
        }
    }

    #[test]
    fn dce_mrs_unobserved_overwrite_twin_preserves_exact_original_certificate_fields() {
        let mut func = mrs_observed_before_overwrite(false);
        let dead = func.block(func.entry).insts[0];
        let live = func.block(func.entry).insts[1];
        let original = func.inst(dead).clone();
        let expected_operands: Vec<_> = original.operands.iter().map(format_operand).collect();
        let run = DeadCodeElimination.run_certified(&mut func);
        assert!(run.changed && run.is_certified(), "{run:?}");
        assert_eq!(run.certificates.len(), 1);
        let certificate = &run.certificates[0];
        assert_eq!(certificate.source_opcode, "CmpRR");
        assert_eq!(certificate.source_operands, expected_operands);
        assert_eq!(certificate.source_location.as_deref(), Some("file:3:8:5"));
        assert_eq!(certificate.contract, DceContract::DeadNzcvWriteUnobservable);
        assert_eq!(
            certificate.nzcv.as_ref().unwrap().exit,
            DeadFlagsExit::NextWriter { inst_id: live.0 }
        );
        assert_eq!(func.inst(dead).opcode, AArch64Opcode::Nop);
        assert!(!func.block(func.entry).insts.contains(&dead));
        assert!(func.block(func.entry).insts.contains(&live));
        assert!(!DeadCodeElimination.run(&mut func));
    }
}
