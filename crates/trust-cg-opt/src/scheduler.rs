// trust-cg-opt - Instruction scheduling
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Pre-register-allocation instruction scheduling for AArch64.
//!
//! Reorders instructions within a basic block to maximize instruction-level
//! parallelism (ILP) and minimize pipeline stalls on wide-dispatch cores
//! (Apple M-series: 8-wide decode, 6 ALU + 2 LD/ST + 4 FP/NEON units).
//!
//! # Algorithm
//!
//! List scheduling with a critical-path priority heuristic:
//!
//! 1. **Build DAG**: Construct a dependency graph from data dependencies (RAW),
//!    memory ordering from the authoritative `opcode_effect()` table
//!    (memory-affecting instructions are serialized in original order, except
//!    proven-reorderable ordinary AArch64 loads may omit load-load edges, and
//!    proven non-overlapping ordinary `StrRI` -> `LdrRI` pairs may omit the
//!    store-load edge),
//!    and control dependencies (terminators depend on all prior instructions).
//!
//! 2. **Compute priorities**: For each node, compute the longest path to any
//!    exit node (critical-path length). Higher priority = longer remaining
//!    critical path = should be scheduled earlier.
//!
//! 3. **Schedule**: Maintain a ready set. At each cycle, pick the highest-
//!    priority ready node, schedule it, and update dependents.
//!
//! # Provenance
//!
//! Scheduling is provenance-neutral: mutation sites replace `MachBlock::insts`
//! with a permutation of the same `InstId`s. The scheduler does not mutate
//! `MachInst`s or create/delete/replace instruction IDs, and final encoding
//! offsets are assigned after scheduling, so provenance-aware hooks leave
//! `ProvenanceMap` unchanged.
//!
//! # Latency Model
//!
//! Approximate Apple M-series (Firestorm) latencies:
//!
//! | Category | Latency | Port |
//! |----------|---------|------|
//! | ALU (add, sub, logic, shift, move, cmp, csel) | 1 cycle | IntAlu |
//! | MUL (mul, msub, smull, umull) | 3 cycles | IntMul |
//! | DIV (sdiv, udiv) | 10 cycles | IntDiv |
//! | Load (ldr, ldp, ldrb, etc.) | 4 cycles | LoadStore |
//! | Store (str, stp, strb, etc.) | 1 cycle | LoadStore |
//! | Branch/Ret | 1 cycle | Branch |
//! | FP arith (fadd, fsub, fmul, fdiv, fcvt) | 3 cycles | FpAlu |
//!
//! Reference: Dougall Johnson, "Apple M1 Firestorm Microarchitecture"

use crate::fast_hash::{FxHashMap as HashMap, FxHashSet as HashSet};
use std::collections::{BTreeSet, VecDeque};

use trust_cg_ir::regs::{
    ALLOCATABLE_FPRS, ALLOCATABLE_GPRS, CALL_CLOBBER_GPRS, CALLER_SAVED_FPRS, PReg, regs_overlap,
};
use trust_cg_ir::{
    AArch64Opcode, BlockId, InstFlags, InstId, MachFunction, MachInst, MachOperand, ProvenanceMap,
    RegClass, VReg,
};

use crate::effects::{
    aarch64_for_each_def_position, aarch64_for_each_use_position, opcode_effect, reads_flags,
    writes_flags,
};
use crate::pass_manager::{AnalysisCache, MachinePass};

// ---------------------------------------------------------------------------
// Execution port model
// ---------------------------------------------------------------------------

/// Execution port classification for Apple M-series cores.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ExecutionPort {
    /// Integer ALU (6 units on M1 Firestorm).
    IntAlu,
    /// Integer multiply (2 complex-integer units).
    IntMul,
    /// Integer divide (1 unit, fully pipelined for throughput but high latency).
    IntDiv,
    /// Load/store unit (2 units).
    LoadStore,
    /// Branch unit (1 unit).
    Branch,
    /// Floating-point / NEON ALU (4 units: 2 FADD + 2 FMUL).
    FpAlu,
}

// ---------------------------------------------------------------------------
// Latency model
// ---------------------------------------------------------------------------

/// Returns `(latency_cycles, execution_port)` for an AArch64 opcode.
///
/// Latencies are approximate for Apple M1 Firestorm core.
pub fn opcode_latency(opcode: AArch64Opcode) -> (u32, ExecutionPort) {
    use AArch64Opcode::*;
    match opcode {
        // Integer ALU: 1 cycle
        AddRR | AddRI | AddRIShift12 | SubRR | SubRI | Neg => (1, ExecutionPort::IntAlu),
        AndRR | AndRI | OrrRR | OrrRI | EorRR | EorRI | OrnRR | BicRR => (1, ExecutionPort::IntAlu),
        // EOR with ROR-shifted source: 1-cycle ALU op (fuses the rotate that
        // would otherwise be a separate serial node on the critical path).
        EorRRShift | EorRRLsl | EorRRLsr => (1, ExecutionPort::IntAlu),
        // ADD/SUB with an LSL-shifted source (and ADD with an LSR-shifted
        // source): 1-cycle ALU op (fuses the shift that would otherwise be a
        // separate serial node on the critical path).
        AddRRShift | SubRRShift | AddRRShiftLsr => (1, ExecutionPort::IntAlu),
        LslRR | LsrRR | AsrRR | LslRI | LsrRI | AsrRI | RorRI | Rbit => (1, ExecutionPort::IntAlu),
        CmpRR | CmpRI | CMPWrr | CMPXrr | CMPWri | CMPXri | Tst => (1, ExecutionPort::IntAlu),
        Csel | CSet | Csinc | Csinv | Csneg => (1, ExecutionPort::IntAlu),
        MovR | MovI | Movz | Movn | Movk | MOVWrr | MOVXrr | MOVZWi | MOVZXi => {
            (1, ExecutionPort::IntAlu)
        }
        Sxtw | Uxtw | Sxtb | Sxth | Uxtb | Uxth | Ubfm | Sbfm | Bfm => (1, ExecutionPort::IntAlu),
        Adrp | Adr | AddPCRel => (1, ExecutionPort::IntAlu),
        AddTprelHi12 | AddTprelLo12 => (1, ExecutionPort::IntAlu),
        AddsRR | AddsRI | SubsRR | SubsRI => (1, ExecutionPort::IntAlu),
        // i128 multi-register: ADC/SBC are 1-cycle ALU, UMULH/MADD are 3-cycle multiply
        Adc | Sbc => (1, ExecutionPort::IntAlu),
        Umulh | Smulh | Madd => (3, ExecutionPort::IntMul),

        // Integer multiply: 3 cycles
        MulRR | Msub | Smull | Umull => (3, ExecutionPort::IntMul),

        // Integer divide: 10 cycles
        SDiv | UDiv => (10, ExecutionPort::IntDiv),

        // Loads: 4 cycles (L1 hit)
        LdrRI | LdrPreIndex | LdrPostIndex | LdrbRI | LdrhRI | LdrsbRI | LdrshRI | LdrRO
        | LdrbRO | LdrhRO | LdrswRO | LdrLiteral | LdpRI | LdpPostIndex | LdrGot | LdrTlvp
        | LdrGottprel => (4, ExecutionPort::LoadStore),
        // Volatile loads/stores: same port/latency as plain (the barrier effect
        // that keeps them from being reordered lives in the effects model).
        VolatileLdrRI | VolatileLdrbRI | VolatileLdrhRI => (4, ExecutionPort::LoadStore),
        VolatileStrRI | VolatileStrbRI | VolatileStrhRI => (1, ExecutionPort::LoadStore),

        // Stores: 1 cycle (non-blocking dispatch)
        StrRI | StrPreIndex | StrPostIndex | StrbRI | StrhRI | StrRO | StrbRO | StrhRO | StpRI
        | StpPreIndex | STRWui | STRXui | STRSui | STRDui => (1, ExecutionPort::LoadStore),

        // Stack allocation pseudo
        StackAlloc => (1, ExecutionPort::IntAlu),

        // Branches
        B | BCond | Bcc | Cbz | Cbnz | Tbz | Tbnz | Br => (1, ExecutionPort::Branch),

        // Calls / return
        Bl | Blr | BL | BLR | TailCall | Ret => (1, ExecutionPort::Branch),

        // Floating-point arithmetic: 3 cycles
        FaddRR | FsubRR | FmulRR | FdivRR | FnegRR | FabsRR | Fcmp => (3, ExecutionPort::FpAlu),
        // FMADD fused multiply-add: 4-cycle FP mul/FMA unit.
        FmaddRR => (4, ExecutionPort::FpAlu),
        FminnmRR | FmaxnmRR => (3, ExecutionPort::FpAlu),
        FrintmRR | FrintpRR | FrintzRR => (3, ExecutionPort::FpAlu),
        FsqrtRR => (12, ExecutionPort::FpAlu),
        FcvtzsRR | FcvtzuRR | ScvtfRR | UcvtfRR => (3, ExecutionPort::FpAlu),
        FcvtSD | FcvtDS | FcvtHS | FcvtHD | FcvtSH | FcvtDH => (3, ExecutionPort::FpAlu),
        FmovGprFpr | FmovFprGpr | FmovFprFpr | FmovImm => (1, ExecutionPort::FpAlu),
        // FCSEL: FPR-domain conditional select. Issues on the FP/NEON pipe (2cy),
        // NOT the integer ALU — the whole point of this opcode is that the select
        // stays in the FP bank. Reads NZCV (see `effects::reads_flags`), so the
        // scheduler keeps it after its flag-setting CMP.
        FcselRR => (2, ExecutionPort::FpAlu),

        // NEON SIMD: uses FP/NEON ALU units
        NeonAddV | NeonSubV => (2, ExecutionPort::FpAlu),
        NeonMulV => (3, ExecutionPort::FpAlu),
        NeonFaddV | NeonFsubV => (3, ExecutionPort::FpAlu),
        NeonFmulV => (4, ExecutionPort::FpAlu),
        // FP vector fused multiply-accumulate: 4-cycle FP mul/FMA unit (the
        // vector sibling of FmaddRR). Tied operand 0 (see has_tied_def_use)
        // gives the RAW edge to the accumulator's setter.
        NeonFmlaV | NeonFmlsV | NeonFmlaLaneV => (4, ExecutionPort::FpAlu),
        // Vector int->FP conversion: 3-cycle FP convert (like scalar UCVTF/SCVTF).
        NeonUcvtfV | NeonScvtfV => (3, ExecutionPort::FpAlu),
        // Vector f32->f64 widening convert (FCVTL/FCVTL2): 3-cycle FP convert.
        NeonFcvtlV | NeonFcvtl2V => (3, ExecutionPort::FpAlu),
        // FP lane extract to a scalar D register (MOV Dd, Vn.D[lane]): SIMD
        // copy/permute latency.
        NeonDupScalarD => (3, ExecutionPort::FpAlu),
        NeonFdivV => (10, ExecutionPort::FpAlu),
        NeonAndV | NeonOrrV | NeonEorV | NeonBicV | NeonNotV | NeonRbitV | NeonRev32V
        | NeonRev64V => (1, ExecutionPort::FpAlu),
        NeonCmeqV | NeonCmgtV | NeonCmgeV | NeonCmhiV | NeonCmhsV | NeonFcmgtV => {
            (2, ExecutionPort::FpAlu)
        }
        NeonSmaxV | NeonSminV | NeonUmaxV | NeonUminV => (2, ExecutionPort::FpAlu),
        NeonUmaxv | NeonAddpScalar => (3, ExecutionPort::FpAlu),
        NeonDupElem | NeonDupGen | NeonMovi => (2, ExecutionPort::FpAlu),
        NeonInsGen | NeonUmovGen => (3, ExecutionPort::FpAlu),
        NeonShlVImm | NeonUshrVImm | NeonSshrVImm => (2, ExecutionPort::FpAlu),
        NeonCntV => (2, ExecutionPort::FpAlu),
        NeonUaddlpV => (3, ExecutionPort::FpAlu),
        NeonSaddlpV => (3, ExecutionPort::FpAlu),
        NeonAbsV => (2, ExecutionPort::FpAlu),
        // Unsigned dot-product accumulate (FEAT_DotProd): multiply-class SIMD
        // latency. The RAW edge on the tied operand 0 (see has_tied_def_use)
        // keeps it ordered after the accumulator's setter.
        NeonUdotV => (3, ExecutionPort::FpAlu),
        NeonBitV => (2, ExecutionPort::FpAlu),
        // Byte-wise extract/concatenate (EXT sliding window): permute-class
        // SIMD latency, plain 2-source def (no tied operand).
        NeonExtV => (2, ExecutionPort::FpAlu),
        // Widening multiply-accumulate-long (SMLAL/SMLAL2/UMLAL/UMLAL2):
        // multiply-class SIMD latency. The RAW edge on the tied operand 0 (see
        // has_tied_def_use) keeps it ordered after the accumulator's setter.
        NeonSmlalV | NeonSmlal2V | NeonUmlalV | NeonUmlal2V => (3, ExecutionPort::FpAlu),
        // Widening add-wide (UADDW/UADDW2): add-class SIMD latency (three-operand
        // form; the i64 addend Vn is a plain source, operand 1 — no tied operand).
        // (SADDW/SADDW2 are the signed siblings — same add-class latency.)
        NeonUaddwV | NeonUaddw2V | NeonSaddwV | NeonSaddw2V => (2, ExecutionPort::FpAlu),
        // Vector multiply-accumulate (MLA.4S) + pairwise widening accumulate
        // (UADALP .4S -> .2D): multiply/accumulate-class SIMD latency (~3cy
        // measured on M4). Both accumulate into a TIED operand 0 (see
        // has_tied_def_use); the RAW edge keeps them after the acc's setter.
        NeonMlaV | NeonUadalpV => (3, ExecutionPort::FpAlu),
        NeonLd1Post => (4, ExecutionPort::LoadStore),
        NeonLdpQPost => (4, ExecutionPort::LoadStore),
        NeonSt1Post => (1, ExecutionPort::LoadStore),
        // STP Q-pair post-index: one store-unit op writing 32 bytes.
        NeonStpQPost => (1, ExecutionPort::LoadStore),

        // Trap pseudo-instructions: treated as branches
        Brk | TrapOverflow | TrapBoundsCheck | TrapBoundsCheckExact | TrapNull | TrapNullIfZero
        | TrapDivZero | TrapDivZeroIfZero | TrapShiftRange | TrapShiftRangeIfOOB
        | TrapOverflowExact => (1, ExecutionPort::Branch),

        // Reference counting: memory-like
        Retain | Release => (1, ExecutionPort::LoadStore),

        // Atomic loads: 4 cycles (like regular load + ordering)
        Ldar | Ldarb | Ldarh | Ldaxr => (4, ExecutionPort::LoadStore),

        // Atomic stores: 2 cycles (like regular store + ordering)
        Stlr | Stlrb | Stlrh | Stlxr => (2, ExecutionPort::LoadStore),

        // Atomic RMW (LSE): 6 cycles
        Ldadd | Ldadda | Ldaddal | Ldaddl | Ldclr | Ldclra | Ldclral | Ldclrl | Ldeor | Ldeora
        | Ldeoral | Ldeorl | Ldset | Ldseta | Ldsetal | Ldsetl | Ldsmax | Ldsmaxa | Ldsmaxal
        | Ldsmaxl | Ldsmin | Ldsmina | Ldsminal | Ldsminl | Ldumax | Ldumaxa | Ldumaxal
        | Ldumaxl | Ldumin | Ldumina | Lduminal | Lduminl | Swp | Swpa | Swpal | Swpl => {
            (6, ExecutionPort::LoadStore)
        }

        // Compare-and-swap: 8 cycles
        Cas | Casa | Casal | Casl => (8, ExecutionPort::LoadStore),

        // Barriers: 4-12 cycles
        Dmb => (4, ExecutionPort::LoadStore),
        Dsb => (8, ExecutionPort::LoadStore),
        Isb => (12, ExecutionPort::LoadStore),

        // System register read: modeled as 4-cycle ALU op. TPIDR_EL0 on
        // Apple Silicon (Firestorm/Icestorm) is effectively ~3-4 cycles; the
        // broader MRS family varies, but 4 is a safe, scheduler-friendly
        // default.
        Mrs => (4, ExecutionPort::IntAlu),

        // Pseudo-instructions
        Phi | Copy | Nop => (1, ExecutionPort::IntAlu),

        // Emission-time alignment padding (never present when the scheduler
        // runs; entry exists for totality).
        AlignNop => (1, ExecutionPort::IntAlu),
    }
}

// ---------------------------------------------------------------------------
// Schedule node and DAG
// ---------------------------------------------------------------------------

/// A node in the scheduling dependency graph.
#[derive(Debug, Clone)]
pub struct ScheduleNode {
    /// The instruction this node represents.
    pub inst_id: InstId,
    /// Execution latency in cycles.
    pub latency: u32,
    /// Which execution port this instruction uses.
    pub port: ExecutionPort,
    /// Indices of nodes this node depends on (predecessors).
    pub deps: Vec<usize>,
    /// Indices of nodes that depend on this node (successors).
    pub rev_deps: Vec<usize>,
    /// Earliest cycle this node can start (computed during scheduling).
    pub earliest_start: u32,
    /// Priority: longest path from this node to any exit (critical path).
    pub priority: u32,
    /// Whether this node has been scheduled.
    pub scheduled: bool,
}

/// Dependency graph for instruction scheduling within a basic block.
#[derive(Debug, Clone)]
pub struct ScheduleDAG {
    /// Nodes indexed by position in the original block instruction list.
    pub nodes: Vec<ScheduleNode>,
}

impl ScheduleDAG {
    /// Compute critical-path priorities (longest path to exit) for all nodes.
    ///
    /// Uses a topological traversal instead of unbounded relaxation. The
    /// scheduler has original-order fallbacks for cyclic DAGs, but priority
    /// computation runs before those fallbacks; keeping this bounded is what
    /// lets the fallback execute.
    fn compute_priorities(&mut self) {
        let n = self.nodes.len();
        if n == 0 {
            return;
        }

        for node in &mut self.nodes {
            node.priority = 0;
        }

        let mut indegree: Vec<usize> = self.nodes.iter().map(|node| node.deps.len()).collect();
        let mut ready: VecDeque<usize> = indegree
            .iter()
            .enumerate()
            .filter_map(|(idx, &degree)| (degree == 0).then_some(idx))
            .collect();
        let mut topo = Vec::with_capacity(n);

        while let Some(idx) = ready.pop_front() {
            topo.push(idx);
            for &succ in &self.nodes[idx].rev_deps {
                if indegree[succ] > 0 {
                    indegree[succ] -= 1;
                    if indegree[succ] == 0 {
                        ready.push_back(succ);
                    }
                }
            }
        }

        if topo.len() != n {
            for node in &mut self.nodes {
                node.priority = node.latency;
            }
            return;
        }

        for &idx in topo.iter().rev() {
            let latency = self.nodes[idx].latency;
            let mut priority = latency;
            for &succ in &self.nodes[idx].rev_deps {
                priority = priority.max(latency.saturating_add(self.nodes[succ].priority));
            }
            self.nodes[idx].priority = priority;
        }
    }
}

// ---------------------------------------------------------------------------
// DAG construction
// ---------------------------------------------------------------------------

/// Build a scheduling dependency graph for one basic block.
///
/// Dependency types:
/// - **Data (RAW)**: instruction B uses a VReg defined by instruction A.
/// - **Memory ordering**: conservative ordering between memory operations,
///   except proof-reorderable ordinary AArch64 loads may omit load-load edges,
///   and statically disjoint proof-reorderable `StrRI` -> `LdrRI` pairs may
///   omit store-load edges.
/// - **Control**: terminators depend on all prior non-terminator instructions.
/// - **Side-effect ordering**: instructions with `HAS_SIDE_EFFECTS` are ordered
///   relative to each other.
pub fn build_dag(func: &MachFunction, block_id: BlockId) -> ScheduleDAG {
    build_dag_for_insts(func, &func.block(block_id).insts)
}

fn is_proof_reorderable_ordinary_load(opcode: AArch64Opcode, flags: InstFlags) -> bool {
    use AArch64Opcode::*;

    if !trust_cg_lower::guard_evidence::validator_guard_replay_authority_available() && !cfg!(test)
    {
        return false;
    }

    let disqualifying_flags =
        InstFlags::WRITES_MEMORY | InstFlags::HAS_SIDE_EFFECTS | InstFlags::IS_CALL;

    flags.contains(InstFlags::PROOF_REORDERABLE)
        && flags.intersection(disqualifying_flags).is_empty()
        && matches!(
            opcode,
            LdrRI | LdrbRI | LdrhRI | LdrsbRI | LdrshRI | LdrRO | LdrswRO | LdrLiteral | LdpRI
        )
}

fn is_proof_reorderable_ordinary_ldr_ri(opcode: AArch64Opcode, flags: InstFlags) -> bool {
    if !trust_cg_lower::guard_evidence::validator_guard_replay_authority_available() && !cfg!(test)
    {
        return false;
    }

    let disqualifying_flags =
        InstFlags::WRITES_MEMORY | InstFlags::HAS_SIDE_EFFECTS | InstFlags::IS_CALL;

    flags.contains(InstFlags::PROOF_REORDERABLE)
        && flags.intersection(disqualifying_flags).is_empty()
        && opcode == AArch64Opcode::LdrRI
}

fn is_proof_reorderable_ordinary_str_ri(opcode: AArch64Opcode, flags: InstFlags) -> bool {
    if !trust_cg_lower::guard_evidence::validator_guard_replay_authority_available() && !cfg!(test)
    {
        return false;
    }

    let disqualifying_flags = InstFlags::READS_MEMORY | InstFlags::IS_CALL | InstFlags::IS_PSEUDO;

    flags.contains(InstFlags::PROOF_REORDERABLE)
        && flags.contains(InstFlags::WRITES_MEMORY)
        && flags.intersection(disqualifying_flags).is_empty()
        && opcode == AArch64Opcode::StrRI
}

/// Visit each explicit def-operand VReg of `inst` without allocating. Same
/// enumeration order and set as [`explicit_vreg_defs`].
#[inline]
fn for_each_explicit_vreg_def(inst: &MachInst, mut f: impl FnMut(VReg)) {
    aarch64_for_each_def_position(inst.opcode, inst.operands.len(), |pos| {
        if let Some(vreg) = inst.operands.get(pos).and_then(MachOperand::as_vreg) {
            f(vreg);
        }
    });
}

/// Visit each explicit use-operand VReg of `inst` without allocating. Same
/// enumeration order and set as [`explicit_vreg_uses`].
#[inline]
fn for_each_explicit_vreg_use(inst: &MachInst, mut f: impl FnMut(VReg)) {
    aarch64_for_each_use_position(inst.opcode, inst.operands.len(), |pos| {
        if let Some(vreg) = inst.operands.get(pos).and_then(MachOperand::as_vreg) {
            f(vreg);
        }
    });
}

#[cfg(test)]
fn explicit_vreg_defs(inst: &MachInst) -> Vec<VReg> {
    let mut out = Vec::new();
    for_each_explicit_vreg_def(inst, |vreg| out.push(vreg));
    out
}

#[cfg(test)]
fn explicit_vreg_uses(inst: &MachInst) -> Vec<VReg> {
    let mut out = Vec::new();
    for_each_explicit_vreg_use(inst, |vreg| out.push(vreg));
    out
}

#[derive(Debug, Clone, Copy)]
struct StaticMemoryByteRange<'a> {
    base: &'a MachOperand,
    offset: i64,
    size: i64,
}

fn proven_str_ri_byte_range(inst: &MachInst) -> Option<StaticMemoryByteRange<'_>> {
    if !is_proof_reorderable_ordinary_str_ri(inst.opcode, inst.flags) {
        return None;
    }

    let base = inst.operands.get(1)?;
    let offset = inst.operands.get(2)?.as_imm()?;
    let size = transfer_operand_size(inst.operands.first()?)?;
    (size > 0).then_some(StaticMemoryByteRange { base, offset, size })
}

fn proven_ldr_ri_byte_range(inst: &MachInst) -> Option<StaticMemoryByteRange<'_>> {
    if !is_proof_reorderable_ordinary_ldr_ri(inst.opcode, inst.flags) {
        return None;
    }

    let base = inst.operands.get(1)?;
    let offset = inst.operands.get(2)?.as_imm()?;
    let size = transfer_operand_size(inst.operands.first()?)?;
    (size > 0).then_some(StaticMemoryByteRange { base, offset, size })
}

fn transfer_operand_size(op: &MachOperand) -> Option<i64> {
    match op {
        MachOperand::VReg(vreg) => Some(i64::from(vreg.class.size_bytes())),
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

fn statically_disjoint_byte_ranges(
    left: StaticMemoryByteRange<'_>,
    right: StaticMemoryByteRange<'_>,
) -> bool {
    left.base == right.base
        && !byte_ranges_overlap(left.offset, left.size, right.offset, right.size)
}

fn proven_disjoint_store_load(prior: &MachInst, current: &MachInst) -> bool {
    let Some(store_range) = proven_str_ri_byte_range(prior) else {
        return false;
    };
    let Some(load_range) = proven_ldr_ri_byte_range(current) else {
        return false;
    };

    statically_disjoint_byte_ranges(store_range, load_range)
}

fn memory_accesses_must_stay_ordered(prior: &MachInst, current: &MachInst) -> bool {
    if is_proof_reorderable_ordinary_load(prior.opcode, prior.flags)
        && is_proof_reorderable_ordinary_load(current.opcode, current.flags)
    {
        return false;
    }

    if proven_disjoint_store_load(prior, current) {
        return false;
    }

    true
}

fn build_dag_for_insts(func: &MachFunction, inst_ids: &[InstId]) -> ScheduleDAG {
    let n = inst_ids.len();

    // Create nodes.
    let mut nodes: Vec<ScheduleNode> = Vec::with_capacity(n);
    for &inst_id in inst_ids {
        let inst = func.inst(inst_id);
        let (latency, port) = opcode_latency(inst.opcode);
        nodes.push(ScheduleNode {
            inst_id,
            latency,
            port,
            deps: Vec::new(),
            rev_deps: Vec::new(),
            earliest_start: 0,
            priority: 0,
            scheduled: false,
        });
    }

    // Helper: add edge from `from` to `to` (from must execute before to).
    let mut edges: HashSet<(usize, usize)> = HashSet::default();
    let add_edge = |from: usize, to: usize, edges: &mut HashSet<(usize, usize)>| {
        if from != to && edges.insert((from, to)) {
            // edges set prevents duplicates; actual deps/rev_deps updated below
        }
    };

    // Build VReg def list: vreg -> sorted list of node indices where the
    // vreg is defined. Most value-producing instructions define operand 0;
    // pair loads define operands 0 and 1.
    //
    // A VReg may be defined multiple times in the same block when:
    //  - Copy-based phi resolution redefines block parameter VRegs at the end
    //    of the block. For example, after lowering trust_ir block arguments:
    //
    //        v7 = add v3, v4      ← uses v3/v4 from block params (previous iter)
    //        v3 = mov v7          ← redefines v3 for the next iteration
    //        v4 = mov v9          ← redefines v4 for the next iteration
    //        b loop_header
    //
    //  - The instruction is a tied def-use (MOVK): the destination is both
    //    the def AND an implicit source. A MOVZ+MOVK chain looks like:
    //
    //        v38 = movz imm_lo
    //        v38 = movk imm_mid, 16    ← implicit read of v38 (tied)
    //        v38 = movk imm_hi, 32     ← implicit read of v38 (tied)
    //        v38 = movk imm_vhi, 48    ← implicit read of v38 (tied)
    //
    //    A subsequent use of v38 must read the FULL 64-bit value, i.e., it
    //    must be ordered AFTER the last MOVK, not just after the initial MOVZ.
    //    See issue #382: xxh3 O2 miscompile caused by the scheduler reordering
    //    readers of v38 between MOVZ and MOVK.
    //
    // We store all defs in program order, then use `latest_def_before` below
    // to pick the most recent prior def for each use. This correctly handles
    // both multi-def patterns without breaking the phi-resolution case (uses
    // that appear BEFORE any in-block def have no latest_def and read from
    // outside the block).
    let mut vreg_def_list: HashMap<VReg, Vec<usize>> = HashMap::default();
    for (idx, &inst_id) in inst_ids.iter().enumerate() {
        let inst = func.inst(inst_id);
        for_each_explicit_vreg_def(inst, |vreg| {
            vreg_def_list.entry(vreg).or_default().push(idx);
        });
    }

    // Legacy def_map: FIRST definition per vreg. Retained for the WAR step
    // below which uses it to decide whether a use reads from outside the
    // block.
    let def_map: HashMap<VReg, usize> = vreg_def_list
        .iter()
        .filter_map(|(vid, defs)| defs.first().map(|d| (*vid, *d)))
        .collect();

    // Return the latest def index of `vreg` that is strictly less than `idx`,
    // or None if there is no in-block def prior to `idx` (i.e., the vreg is
    // read from outside the block — a block parameter / phi input).
    let latest_def_before = |vreg: VReg, idx: usize| -> Option<usize> {
        let defs = vreg_def_list.get(&vreg)?;
        // defs is sorted by construction; find the last def strictly < idx.
        defs.iter().rev().find(|&&d| d < idx).copied()
    };

    // 1. Data dependencies (RAW): for each use operand, add edge from the
    // latest prior def in the same block.
    //
    // A use whose vreg has NO in-block def before it reads from outside the
    // block (block parameter); no within-block RAW edge needed. Similarly,
    // skip adding self-loops (add_edge already does from != to).
    //
    // For tied def-use opcodes (MOVK), operand[0] is ALSO a use: the
    // destination register's prior value is an implicit input. Without this
    // edge, the scheduler can reorder a MOVK before the MOVZ (or an earlier
    // MOVK in the chain) that established the prior value, producing wrong
    // results. See issue #382.
    for (idx, &inst_id) in inst_ids.iter().enumerate() {
        let inst = func.inst(inst_id);
        for_each_explicit_vreg_use(inst, |vreg| {
            if let Some(def_idx) = latest_def_before(vreg, idx) {
                add_edge(def_idx, idx, &mut edges);
            }
        });
    }

    // 1b. VReg WAW (write-after-write) dependencies: when the same VReg is
    //     defined multiple times in one block (phi-resolution copies),
    //     the second definition must be ordered after the first.
    //
    // 1c. VReg WAR (write-after-read / anti-dependencies): when an instruction
    //     reads a VReg and a later instruction defines (or redefines) that same
    //     VReg within the block, the read must complete before the write.
    //     Without this, the scheduler can move the definition before the read,
    //     causing the read to see the new value instead of the old one.
    //
    //     This is critical for phi-resolution copies at loop back-edges:
    //       v_tmp = sdiv v10, v11   ← reads v10 and v11
    //       v_res = msub v_tmp, v11, v10
    //       v10 = mov v11           ← redefines v10 (copy b to a)
    //       v11 = mov v_res         ← redefines v11 (copy result to b)
    //       b loop_header
    //
    //     Without WAR edges, the scheduler may reorder `v11 = mov v_res`
    //     before the sdiv/msub/mov that read v11, breaking the loop.
    //
    //     This was the root cause of issue #308 (O1 breaks SRem-based loops).
    {
        let mut vreg_defs: HashMap<VReg, Vec<usize>> = HashMap::default();
        let mut vreg_uses: HashMap<VReg, Vec<usize>> = HashMap::default();

        for (idx, &inst_id) in inst_ids.iter().enumerate() {
            let inst = func.inst(inst_id);
            // Collect defs.
            for_each_explicit_vreg_def(inst, |vreg| {
                vreg_defs.entry(vreg).or_default().push(idx);
            });
            // Collect uses (source operands).
            for_each_explicit_vreg_use(inst, |vreg| {
                vreg_uses.entry(vreg).or_default().push(idx);
            });
        }

        // WAW: chain multiple definitions of the same vreg in program order.
        for defs in vreg_defs.values() {
            for window in defs.windows(2) {
                add_edge(window[0], window[1], &mut edges);
            }
        }

        // WAR: for each instruction that defines a VReg, add edges from ALL
        // prior uses of that VReg in the same block. This ensures reads of
        // the old value complete before the new definition overwrites it.
        //
        // This handles both cases:
        // - VReg defined once in the block (e.g., phi-resolution copy redefining
        //   a block parameter VReg that is also used as a source earlier)
        // - VReg defined multiple times in the block
        for (vreg, defs) in &vreg_defs {
            if let Some(uses) = vreg_uses.get(vreg) {
                for &def_idx in defs {
                    for &use_idx in uses {
                        // Use must precede the definition in program order.
                        if use_idx < def_idx {
                            add_edge(use_idx, def_idx, &mut edges);
                        }
                    }
                }
            }
        }
    }

    // 1c. VReg WAR (write-after-read / anti-) dependencies: when an instruction
    //     at index `j` defines a VReg `v` that is used by an earlier instruction
    //     at index `i < j`, the write at `j` must not be reordered before the
    //     read at `i`. This is critical for phi-resolution copy blocks where
    //     parallel assignments are lowered to sequential copies:
    //
    //       [0] v20 = mov v21      ← reads old v21 (from predecessor)
    //       [1] v21 = mov v23      ← redefines v21
    //
    //     Without the WAR edge 0→1, the scheduler could place [1] before [0],
    //     causing [0] to read the new v21 instead of the old one.
    //
    //     We only add WAR edges when the use reads a value from OUTSIDE the
    //     block (i.e., the vreg is not defined in the block before the use,
    //     or is defined by the same instruction that is being written later).
    //     If the use reads a within-block definition, the RAW edge from step 1
    //     already provides the necessary ordering.
    {
        // Collect all uses: vreg -> list of user node indices.
        let mut vreg_uses: HashMap<VReg, Vec<usize>> = HashMap::default();
        for (idx, &inst_id) in inst_ids.iter().enumerate() {
            let inst = func.inst(inst_id);
            for_each_explicit_vreg_use(inst, |vreg| {
                vreg_uses.entry(vreg).or_default().push(idx);
            });
        }

        // For each vreg defined in the block, check if any earlier instruction
        // uses the same vreg with a value from outside the block.
        for (idx, &inst_id) in inst_ids.iter().enumerate() {
            let inst = func.inst(inst_id);
            for_each_explicit_vreg_def(inst, |def_vreg| {
                let Some(users) = vreg_uses.get(&def_vreg) else {
                    return;
                };
                for &user_idx in users {
                    if user_idx < idx {
                        // user_idx reads def_vreg BEFORE idx defines it.
                        // Check if the read comes from outside the block
                        // (no prior in-block definition covers this use).
                        let prior_def = def_map.get(&def_vreg).copied();
                        let read_is_external = match prior_def {
                            // The first in-block def IS this instruction (idx),
                            // so the use at user_idx reads from outside.
                            Some(first_def) if first_def >= user_idx => true,
                            // The first in-block def is before user_idx,
                            // so the RAW edge from step 1 already orders them.
                            Some(_) => false,
                            // No in-block def at all (shouldn't happen since
                            // we're iterating over defs, but be safe).
                            None => true,
                        };
                        if read_is_external {
                            // WAR: the use at user_idx must execute before
                            // the def at idx.
                            add_edge(user_idx, idx, &mut edges);
                        }
                    }
                }
            });
        }
    }

    // 1d. PReg RAW/WAR/WAW dependencies.
    //
    // Pre-regalloc machine IR can already contain fixed physical registers for
    // ABI formals, calls, returns, and stack/frame helpers. The VReg dependency
    // logic above cannot see those architectural registers. Model them directly
    // so scheduling cannot move a physical-register writer before an earlier
    // physical-register read, including implicit live-in reads attached by ISel.
    let preg_accesses: Vec<PRegAccesses> = inst_ids
        .iter()
        .map(|&inst_id| collect_preg_accesses(func.inst(inst_id)))
        .collect();
    // Only instructions that actually touch a physical register can take part
    // in a physical-register dependency, so pairing every instruction with every
    // earlier one wastes the overwhelming majority of the comparisons: in
    // ordinary straight-line code almost all instructions are pure-vreg and
    // their access lists are empty. Restricting the all-pairs walk to the
    // instructions with a non-empty access list yields exactly the same edge set
    // -- an empty list cannot overlap anything -- while making the cost O(k^2)
    // in the number of physical-register touchers rather than O(n^2) in the
    // region size.
    let preg_touchers: Vec<usize> = (0..n)
        .filter(|&i| !preg_accesses[i].reads.is_empty() || !preg_accesses[i].writes.is_empty())
        .collect();
    for (pos, &idx) in preg_touchers.iter().enumerate() {
        let current = &preg_accesses[idx];
        for &prior_idx in &preg_touchers[..pos] {
            let prior = &preg_accesses[prior_idx];
            if overlaps_any(&prior.writes, &current.reads)
                || overlaps_any(&prior.reads, &current.writes)
                || overlaps_any(&prior.writes, &current.writes)
            {
                add_edge(prior_idx, idx, &mut edges);
            }
        }
    }

    // 1e. Pre-regalloc fixed-PReg anti-dependencies against virtual registers.
    //
    // A fixed physical-register read, such as an entry live-in copy
    // `v0 = copy x0`, is not safe to delay past later virtual-register
    // definitions. Register allocation may assign one of those virtual defs to
    // x0, clobbering the live-in before the delayed copy reads it. Conversely,
    // a fixed physical-register write must not move before earlier virtual
    // uses, because those uses may later be allocated to the same physical
    // register. Model those pre-RA hazards conservatively for fixed PRegs that
    // can alias an allocatable register. Non-allocatable fixed registers such
    // as SP/X16/X30 are handled by explicit PReg dependencies and barriers.
    {
        let mut vreg_defs: Vec<usize> = Vec::new();
        let mut vreg_uses: Vec<usize> = Vec::new();

        for (idx, &inst_id) in inst_ids.iter().enumerate() {
            let inst = func.inst(inst_id);

            let mut has_def = false;
            for_each_explicit_vreg_def(inst, |_| has_def = true);
            if has_def {
                vreg_defs.push(idx);
            }

            let mut has_use = false;
            for_each_explicit_vreg_use(inst, |_| has_use = true);
            if has_use {
                vreg_uses.push(idx);
            }
        }

        for (idx, access) in preg_accesses.iter().enumerate() {
            if access
                .reads
                .iter()
                .any(|&preg| preg_can_alias_allocatable(preg))
            {
                for &def_idx in &vreg_defs {
                    if idx < def_idx {
                        add_edge(idx, def_idx, &mut edges);
                    }
                }
            }

            if access
                .writes
                .iter()
                .any(|&preg| preg_can_alias_allocatable(preg))
            {
                for &use_idx in &vreg_uses {
                    if use_idx < idx {
                        add_edge(use_idx, idx, &mut edges);
                    }
                }

                // ...and the case that was MISSING: an earlier VIRTUAL DEF
                // must not be DELAYED past a fixed physical-register write.
                // Register allocation may assign that virtual def to the same
                // physical register, clobbering the value the write produced —
                // and for the ABI return register that value is live all the
                // way out of the function, so nothing in the region redefines
                // it and no other rule catches the hazard.
                //
                // P0 this fixes (found by benchmarks/bridge-fuzz):
                //     fn f(p0: u64, .., p7: u16, p8: u64, p9: u64) -> u32 { p0 as u32 }
                // With >8 integer parameters the unused ones are stack-passed
                // and ISel emits dead `LdrRI vN, [x29, IncomingArg(..)]` loads.
                // Pre-regalloc the region is
                //     LdrRI [v9, x29, IncomingArg(8)]   ; dead
                //     Uxtw  [PReg(x0), v10]             ; the return value
                //     Ret   [PReg(x30)]                 ; does NOT list x0
                // Without this edge the dead load may be scheduled after the
                // `Uxtw`, and regalloc — seeing no later reader of x0, because
                // `Ret` does not name it — hands the dead load x0. Emitted:
                // `mov w0,w1 ; ldr x0,[x29,#24] ; ret`, i.e. the function
                // returns its LAST parameter. LLVM 1000, trust-cg 1009 at
                // O1/O2/O3, and the proofs-on lane did NOT fail closed on it.
                //
                // The deeper defect is that `Ret` does not declare the return
                // register as a use; fixing that is the general repair and
                // would also cover any future consumer that reasons about
                // live-out. This edge closes the scheduling half conservatively
                // in the meantime.
                for &def_idx in &vreg_defs {
                    if def_idx < idx {
                        add_edge(def_idx, idx, &mut edges);
                    }
                }
            }
        }
    }

    // 2. Memory dependencies: order memory-affecting instructions
    //    conservatively in original program order.
    //
    // Load-load reordering is legal only with a precise alias/effect model.
    // The JIT uses generated pointer-rich code where loads can observe
    // callout-owned buffers, stack slots, and aggregate-layout scratch areas.
    // PROOF_REORDERABLE is that precise proof for ordinary non-writeback
    // AArch64 loads only. ValidBorrow also proves independence for ordinary
    // StrRI -> LdrRI when the byte ranges are statically disjoint. Keep
    // overlapping ranges, unknown ranges, stores, calls, barriers, atomics,
    // writeback forms, and unproven memory operations ordered as before.
    let mut memory_accesses: Vec<usize> = Vec::new();

    for (idx, &inst_id) in inst_ids.iter().enumerate() {
        let inst = func.inst(inst_id);
        let flags = inst.flags;
        let effect = opcode_effect(inst.opcode);

        let is_load = effect.reads_memory() || flags.contains(InstFlags::READS_MEMORY);
        let is_store = effect.writes_memory() || flags.contains(InstFlags::WRITES_MEMORY);
        let is_barrier = effect.is_barrier() || flags.contains(InstFlags::IS_CALL);

        if !(is_load || is_store || is_barrier) {
            continue;
        }

        for &prior_idx in &memory_accesses {
            let prior = func.inst(inst_ids[prior_idx]);
            if memory_accesses_must_stay_ordered(prior, inst) {
                add_edge(prior_idx, idx, &mut edges);
            }
        }
        memory_accesses.push(idx);
    }

    // 2b. NZCV flag dependencies: flag-writing instructions (CMP, TST, ADDS,
    //     SUBS, etc.) and flag-reading instructions (CSet, Csel, ADC, BCond,
    //     etc.) communicate through an implicit single architectural flag
    //     register.
    //
    //     These dependencies are not captured by explicit operands. A later
    //     flag writer must not move between an earlier writer and its reader,
    //     so serialize all NZCV accesses in program order while allowing
    //     unrelated non-flag instructions to schedule around them.
    {
        let mut last_flag_access: Option<usize> = None;
        for (idx, &inst_id) in inst_ids.iter().enumerate() {
            let inst = func.inst(inst_id);
            let touches_flags = writes_flags(inst.opcode)
                || reads_flags(inst.opcode)
                || matches!(inst.opcode, AArch64Opcode::BCond | AArch64Opcode::Bcc);
            if touches_flags {
                if let Some(prev) = last_flag_access {
                    add_edge(prev, idx, &mut edges);
                }
                last_flag_access = Some(idx);
            }
        }
    }

    // 3. Side-effect ordering: instructions with HAS_SIDE_EFFECTS that are not
    //    already covered by memory deps are ordered relative to each other.
    let mut last_side_effect: Option<usize> = None;
    for (idx, &inst_id) in inst_ids.iter().enumerate() {
        let inst = func.inst(inst_id);
        if inst.flags.contains(InstFlags::HAS_SIDE_EFFECTS) {
            if let Some(prev) = last_side_effect {
                add_edge(prev, idx, &mut edges);
            }
            last_side_effect = Some(idx);
        }
    }

    // 3a. Calls and opcode-modeled barriers are full scheduling barriers.
    //
    // Pre-regalloc call lowering uses physical ABI registers for arguments
    // and return values. Those PReg dependencies are intentionally not part
    // of the VReg RAW/WAR tracking above, so a pure copy from X0 after a call
    // can otherwise be hoisted before the call and read the pre-call argument.
    // Keep all instructions on their original side of a call/barrier until
    // the scheduler grows complete PReg dependency modeling.
    for (idx, &inst_id) in inst_ids.iter().enumerate() {
        let inst = func.inst(inst_id);
        let effect = opcode_effect(inst.opcode);
        if inst.flags.contains(InstFlags::IS_CALL) || effect.is_barrier() {
            for prior in 0..idx {
                add_edge(prior, idx, &mut edges);
            }
            for later in (idx + 1)..n {
                add_edge(idx, later, &mut edges);
            }
        }
    }

    // 4. Control dependencies: terminators fence the whole region.
    //
    // Instructions after an internal terminator are control-dependent on not
    // taking that terminator. They may be unreachable after `ret`, or they may
    // be fallthrough-only work after a conditional branch. Keep those later
    // instructions after the terminator so scheduling cannot turn unreachable
    // or guarded memory operations into unconditional execution.
    for (idx, &inst_id) in inst_ids.iter().enumerate() {
        let inst = func.inst(inst_id);
        if inst.flags.contains(InstFlags::IS_TERMINATOR) {
            for prior in 0..idx {
                add_edge(prior, idx, &mut edges);
            }
            for later in (idx + 1)..n {
                add_edge(idx, later, &mut edges);
            }
        }
    }

    // Populate deps/rev_deps from the edge set.
    for &(from, to) in &edges {
        nodes[to].deps.push(from);
        nodes[from].rev_deps.push(to);
    }

    let mut dag = ScheduleDAG { nodes };
    dag.compute_priorities();
    dag
}

#[derive(Debug, Default)]
struct PRegAccesses {
    reads: Vec<PReg>,
    writes: Vec<PReg>,
}

fn push_unique_preg(regs: &mut Vec<PReg>, preg: PReg) {
    if !regs.contains(&preg) {
        regs.push(preg);
    }
}

fn collect_preg_read_from_operand(reads: &mut Vec<PReg>, operand: &MachOperand) {
    match operand {
        MachOperand::PReg(preg) => push_unique_preg(reads, *preg),
        MachOperand::MemOp { base, .. } => push_unique_preg(reads, *base),
        _ => {}
    }
}

fn collect_preg_accesses(inst: &trust_cg_ir::MachInst) -> PRegAccesses {
    let mut accesses = PRegAccesses::default();

    aarch64_for_each_def_position(inst.opcode, inst.operands.len(), |pos| {
        if let Some(preg) = inst.operands.get(pos).and_then(MachOperand::as_preg) {
            push_unique_preg(&mut accesses.writes, preg);
        }
    });

    aarch64_for_each_use_position(inst.opcode, inst.operands.len(), |pos| {
        if let Some(operand) = inst.operands.get(pos) {
            collect_preg_read_from_operand(&mut accesses.reads, operand);
        }
    });

    for &preg in inst.implicit_uses {
        push_unique_preg(&mut accesses.reads, preg);
    }
    for &preg in inst.implicit_defs {
        push_unique_preg(&mut accesses.writes, preg);
    }

    if call_opcode_clobbers_registers(inst.opcode) || inst.flags.contains(InstFlags::IS_CALL) {
        for preg in CALL_CLOBBER_GPRS {
            push_unique_preg(&mut accesses.writes, preg);
        }
        for preg in CALLER_SAVED_FPRS {
            push_unique_preg(&mut accesses.writes, preg);
        }
    }

    accesses
}

fn call_opcode_clobbers_registers(opcode: AArch64Opcode) -> bool {
    matches!(
        opcode,
        AArch64Opcode::Bl | AArch64Opcode::Blr | AArch64Opcode::BL | AArch64Opcode::BLR
    )
}

fn overlaps_any(left: &[PReg], right: &[PReg]) -> bool {
    left.iter()
        .any(|&l| right.iter().any(|&r| regs_overlap(l, r)))
}

fn preg_can_alias_allocatable(preg: PReg) -> bool {
    ALLOCATABLE_GPRS
        .iter()
        .chain(ALLOCATABLE_FPRS.iter())
        .any(|&allocatable| regs_overlap(preg, allocatable))
}

// ---------------------------------------------------------------------------
// Register pressure tracking during scheduling
// ---------------------------------------------------------------------------

/// Tracks approximate register pressure during list scheduling.
///
/// Monitors the number of live virtual registers at each scheduling step.
/// When pressure exceeds thresholds, the scheduler prefers instructions that
/// reduce pressure (consumers that kill operands) over instructions that
/// increase it (producers that define new values).
///
/// This prevents the scheduler from creating unnecessarily long live ranges
/// that force the register allocator to spill. The heuristic balances ILP
/// (critical-path scheduling) against register pressure (spill avoidance).
///
/// Reference: LLVM's `ScheduleDAGRRList::BURegReductionPriorityQueue` and
/// GCC's `sched-pressure.cc`.
#[derive(Debug, Clone)]
pub struct PressureTracker {
    /// Set of GPR VRegs currently live (defined but not yet last-used).
    live_gprs: HashSet<VReg>,
    /// Set of FPR VRegs currently live.
    live_fprs: HashSet<VReg>,
    /// Peak GPR pressure observed so far.
    pub peak_gpr: u32,
    /// Peak FPR pressure observed so far.
    pub peak_fpr: u32,
    /// GPR pressure threshold: above this, prefer consumers.
    pub gpr_threshold: u32,
    /// FPR pressure threshold: above this, prefer consumers.
    pub fpr_threshold: u32,
}

impl PressureTracker {
    /// Create a new pressure tracker with default AArch64 thresholds.
    ///
    /// Thresholds are set below the allocatable register count to provide
    /// headroom: 20 GPRs (of 28 allocatable) and 24 FPRs (of 32 allocatable).
    pub fn new() -> Self {
        Self {
            live_gprs: HashSet::default(),
            live_fprs: HashSet::default(),
            peak_gpr: 0,
            peak_fpr: 0,
            gpr_threshold: 20,
            fpr_threshold: 24,
        }
    }

    /// Create a tracker with custom thresholds.
    pub fn with_thresholds(gpr_threshold: u32, fpr_threshold: u32) -> Self {
        Self {
            live_gprs: HashSet::default(),
            live_fprs: HashSet::default(),
            peak_gpr: 0,
            peak_fpr: 0,
            gpr_threshold,
            fpr_threshold,
        }
    }

    /// Current GPR pressure (number of live GPR VRegs).
    pub fn gpr_pressure(&self) -> u32 {
        self.live_gprs.len() as u32
    }

    /// Current FPR pressure (number of live FPR VRegs).
    pub fn fpr_pressure(&self) -> u32 {
        self.live_fprs.len() as u32
    }

    /// Returns true if GPR or FPR pressure exceeds the threshold.
    pub fn is_high_pressure(&self) -> bool {
        self.gpr_pressure() > self.gpr_threshold || self.fpr_pressure() > self.fpr_threshold
    }

    /// Record that a VReg has been defined (becomes live).
    pub fn define_vreg(&mut self, vreg: VReg) {
        let is_fpr = matches!(
            vreg.class,
            RegClass::Fpr128 | RegClass::Fpr64 | RegClass::Fpr32 | RegClass::Fpr16 | RegClass::Fpr8
        );
        if is_fpr {
            self.live_fprs.insert(vreg);
            self.peak_fpr = self.peak_fpr.max(self.live_fprs.len() as u32);
        } else {
            self.live_gprs.insert(vreg);
            self.peak_gpr = self.peak_gpr.max(self.live_gprs.len() as u32);
        }
    }

    /// Record that a VReg has been killed (last use — no longer live).
    pub fn kill_vreg(&mut self, vreg: VReg) {
        self.live_gprs.remove(&vreg);
        self.live_fprs.remove(&vreg);
    }
}

impl Default for PressureTracker {
    fn default() -> Self {
        Self::new()
    }
}

/// Per-node pressure metadata computed before scheduling.
///
/// For each node in the DAG, we precompute:
/// - How many VRegs this instruction uses for the last time (kills).
/// - How many VRegs this instruction defines (new live ranges).
/// - The register class of defined VRegs.
#[derive(Debug, Clone)]
struct NodePressureInfo {
    /// VRegs defined by this instruction.
    defs: Vec<VReg>,
    /// VRegs used by this instruction.
    uses: Vec<VReg>,
    /// Number of VRegs whose last use is this instruction (kills).
    /// Computed from the full block context.
    kills: u32,
    /// Net pressure change: defs - kills. Negative means pressure-reducing.
    net_pressure: i32,
}

/// Precompute pressure metadata for all nodes in the DAG.
///
/// For each instruction, we determine which VRegs it defines and uses,
/// and which uses are the last use in the block (kills). This is computed
/// from the function's instruction data and the DAG node mapping.
fn compute_pressure_info(func: &MachFunction, dag: &ScheduleDAG) -> Vec<NodePressureInfo> {
    let n = dag.nodes.len();

    // Collect defs and uses per node.
    let mut infos: Vec<NodePressureInfo> = Vec::with_capacity(n);
    for node in &dag.nodes {
        let inst = func.inst(node.inst_id);
        let mut defs = Vec::new();
        let mut uses = Vec::new();

        for_each_explicit_vreg_def(inst, |vreg| defs.push(vreg));
        for_each_explicit_vreg_use(inst, |vreg| uses.push(vreg));

        infos.push(NodePressureInfo {
            defs,
            uses,
            kills: 0,
            net_pressure: 0,
        });
    }

    // Build last-use map: for each VReg used in this block, find the last
    // node index that uses it. Uses that are last are "kills".
    let mut last_use_node: HashMap<VReg, usize> = HashMap::default();
    for (idx, info) in infos.iter().enumerate() {
        for &vreg in &info.uses {
            last_use_node.insert(vreg, idx);
        }
    }

    // Count kills per node and compute net pressure.
    for (idx, info) in infos.iter_mut().enumerate() {
        let mut kills = 0u32;
        for &vreg in &info.uses {
            if last_use_node.get(&vreg) == Some(&idx) {
                kills += 1;
            }
        }
        info.kills = kills;
        info.net_pressure = info.defs.len() as i32 - kills as i32;
    }

    infos
}

// ---------------------------------------------------------------------------
// List scheduling
// ---------------------------------------------------------------------------

/// Where a node currently lives in [`ReadySet`].
#[derive(Clone, Copy, PartialEq, Eq)]
enum ReadySlot {
    /// Dependencies not yet satisfied — not tracked by the set.
    Blocked,
    /// Dependencies satisfied, but `earliest_start` is still in the future.
    /// Carries the key it was filed under so it can be re-keyed exactly.
    Pending(u32),
    /// Dependencies satisfied and `earliest_start <= cycle`: selectable now.
    Ready,
    /// Already emitted.
    Done,
}

/// Incremental ready-set for the list schedulers.
///
/// # Why this exists
///
/// Both schedulers used to rebuild the ready set from scratch on every
/// scheduled instruction:
///
/// ```text
/// while scheduled_order.len() < n {
///     for (i, deps) in remaining_deps.iter().enumerate() { ... }   // scans ALL n
///     ready.sort_by(...);
///     let best = ready[0];
/// ```
///
/// One instruction is emitted per outer iteration, so that is O(n^2) scanning
/// (plus an O(k log k) sort per step). On a 1600-statement function in a single
/// scheduling region it was ~2.56M scans and **113ms per invocation**, which
/// made `pressure-aware-scheduler` 60% of the entire optimization budget and the
/// whole backend quadratic. Measured: trust-cg was 22.85x slower than LLVM at
/// 3200 statements and still diverging.
///
/// This maintains the same set incrementally: a node is admitted exactly once,
/// when its last dependency is satisfied, and selection is a single ordered-map
/// lookup. That is O(n log n) overall.
///
/// # Why the emitted schedule is unchanged
///
/// The old code selected `ready[0]` after sorting by a comparator whose final
/// tie-break is the node index, so the comparator is a TOTAL order and
/// `ready[0]` is its unique minimum. Each `BTreeSet` here is keyed by exactly
/// that order, so `first()` returns the same node. Both orders are kept
/// simultaneously because `high_pressure` — which selects between them — is
/// recomputed per step and may flip either way; the two sets always hold the
/// same membership.
///
/// `earliest_start` may in principle be bumped after a node is already admitted
/// (duplicate edges can drive `remaining_deps` to zero early), so [`Self::bump`]
/// re-files such a node, including demoting it out of the ready set when its
/// start moves past the current cycle. That keeps this exactly as robust as the
/// full rescan it replaces.
struct ReadySet {
    /// Priority order: `priority` DESC, then index ASC.
    normal: BTreeSet<(core::cmp::Reverse<u32>, usize)>,
    /// Pressure order: `net_pressure` ASC, `priority` DESC, index ASC.
    /// `None` for schedulers that never consult pressure.
    pressure: Option<BTreeSet<(i32, core::cmp::Reverse<u32>, usize)>>,
    /// Dependency-satisfied nodes not yet at their `earliest_start`.
    pending: BTreeSet<(u32, usize)>,
    slot: Vec<ReadySlot>,
    prio: Vec<u32>,
    netp: Vec<i32>,
}

impl ReadySet {
    fn new(prio: Vec<u32>, netp: Option<Vec<i32>>) -> Self {
        let n = prio.len();
        Self {
            normal: BTreeSet::new(),
            pressure: netp.as_ref().map(|_| BTreeSet::new()),
            pending: BTreeSet::new(),
            slot: vec![ReadySlot::Blocked; n],
            prio,
            netp: netp.unwrap_or_else(|| vec![0; n]),
        }
    }

    fn normal_key(&self, i: usize) -> (core::cmp::Reverse<u32>, usize) {
        (core::cmp::Reverse(self.prio[i]), i)
    }

    fn pressure_key(&self, i: usize) -> (i32, core::cmp::Reverse<u32>, usize) {
        (self.netp[i], core::cmp::Reverse(self.prio[i]), i)
    }

    fn insert_ready(&mut self, i: usize) {
        let nk = self.normal_key(i);
        self.normal.insert(nk);
        if self.pressure.is_some() {
            let pk = self.pressure_key(i);
            self.pressure.as_mut().expect("checked").insert(pk);
        }
        self.slot[i] = ReadySlot::Ready;
    }

    fn remove_ready(&mut self, i: usize) {
        let nk = self.normal_key(i);
        self.normal.remove(&nk);
        if self.pressure.is_some() {
            let pk = self.pressure_key(i);
            self.pressure.as_mut().expect("checked").remove(&pk);
        }
    }

    /// Admit a node whose dependencies are now all satisfied.
    fn admit(&mut self, i: usize, earliest_start: u32, cycle: u32) {
        if self.slot[i] != ReadySlot::Blocked {
            return;
        }
        if earliest_start <= cycle {
            self.insert_ready(i);
        } else {
            self.pending.insert((earliest_start, i));
            self.slot[i] = ReadySlot::Pending(earliest_start);
        }
    }

    /// Re-file a node whose `earliest_start` moved after it was admitted.
    fn bump(&mut self, i: usize, earliest_start: u32, cycle: u32) {
        match self.slot[i] {
            ReadySlot::Blocked | ReadySlot::Done => {}
            ReadySlot::Pending(old) => {
                if old != earliest_start {
                    self.pending.remove(&(old, i));
                    self.pending.insert((earliest_start, i));
                    self.slot[i] = ReadySlot::Pending(earliest_start);
                }
            }
            ReadySlot::Ready => {
                if earliest_start > cycle {
                    self.remove_ready(i);
                    self.pending.insert((earliest_start, i));
                    self.slot[i] = ReadySlot::Pending(earliest_start);
                }
            }
        }
    }

    /// Promote every pending node whose start has arrived.
    fn advance_to(&mut self, cycle: u32) {
        while let Some(&(start, i)) = self.pending.first() {
            if start > cycle {
                break;
            }
            self.pending.pop_first();
            self.insert_ready(i);
        }
    }

    fn is_ready_empty(&self) -> bool {
        self.normal.is_empty()
    }

    /// Earliest start among dependency-satisfied nodes not yet selectable.
    fn next_pending_start(&self) -> Option<u32> {
        self.pending.first().map(|&(start, _)| start)
    }

    /// The unique minimum of the requested order, removed from the set.
    fn take_best(&mut self, high_pressure: bool) -> Option<usize> {
        let best = if high_pressure {
            self.pressure.as_ref().and_then(|p| p.first()).map(|k| k.2)
        } else {
            self.normal.first().map(|k| k.1)
        }
        .or_else(|| self.normal.first().map(|k| k.1))?;
        self.remove_ready(best);
        self.slot[best] = ReadySlot::Done;
        Some(best)
    }
}

/// List scheduling: produce a new instruction order that minimizes stalls.
///
/// Uses a priority queue (sorted ready set) with critical-path heuristic.
/// At each step, picks the ready node with the highest priority (longest
/// remaining critical path).
pub fn schedule_list(dag: &mut ScheduleDAG) -> Vec<InstId> {
    let n = dag.nodes.len();
    if n == 0 {
        return Vec::new();
    }

    let mut scheduled_order: Vec<InstId> = Vec::with_capacity(n);
    let mut remaining_deps: Vec<usize> = dag.nodes.iter().map(|node| node.deps.len()).collect();
    let mut cycle: u32 = 0;

    // Incremental ready-set: same selection as the previous full rescan, without
    // the O(n^2). See `ReadySet` for why the emitted order is unchanged.
    let mut ready = ReadySet::new(dag.nodes.iter().map(|node| node.priority).collect(), None);
    for (i, deps) in remaining_deps.iter().enumerate() {
        if *deps == 0 {
            ready.admit(i, dag.nodes[i].earliest_start, cycle);
        }
    }

    while scheduled_order.len() < n {
        ready.advance_to(cycle);

        if ready.is_ready_empty() {
            // No node ready at this cycle — advance to the earliest available.
            let Some(min_start) = ready.next_pending_start() else {
                // Cyclic dependencies mean the scheduler cannot prove any
                // non-original order is legal. Preserve the original region
                // order instead of breaking a dependency edge.
                return preserve_original_order(dag);
            };
            cycle = min_start;
            continue;
        }

        // Pick the highest-priority ready node.
        let Some(best) = ready.take_best(false) else {
            return preserve_original_order(dag);
        };
        dag.nodes[best].scheduled = true;
        dag.nodes[best].earliest_start = cycle;
        scheduled_order.push(dag.nodes[best].inst_id);

        // Update dependents: their earliest_start is at least (cycle + latency).
        // Use saturating_sub because force-scheduled nodes may have had their
        // remaining_deps zeroed, causing a successor's count to underflow if
        // decremented again by a different predecessor in a cycle.
        let finish = cycle + dag.nodes[best].latency;
        let rev_deps = dag.nodes[best].rev_deps.clone();
        for &succ in &rev_deps {
            remaining_deps[succ] = remaining_deps[succ].saturating_sub(1);
            if dag.nodes[succ].earliest_start < finish {
                dag.nodes[succ].earliest_start = finish;
                ready.bump(succ, finish, cycle);
            }
            if remaining_deps[succ] == 0 {
                ready.admit(succ, dag.nodes[succ].earliest_start, cycle);
            }
        }

        cycle += 1;
    }

    scheduled_order
}

fn preserve_original_order(dag: &mut ScheduleDAG) -> Vec<InstId> {
    for (idx, node) in dag.nodes.iter_mut().enumerate() {
        node.scheduled = true;
        node.earliest_start = u32::try_from(idx).unwrap_or(u32::MAX);
    }
    dag.nodes.iter().map(|node| node.inst_id).collect()
}

/// Register pressure-aware list scheduling.
///
/// Extends the basic list scheduler with register pressure heuristics:
///
/// 1. **Pressure tracking**: Maintains a set of live VRegs. When an instruction
///    is scheduled, its defs become live and its killed operands die.
///
/// 2. **Consumer preference under high pressure**: When pressure exceeds the
///    threshold, the scheduler prefers instructions that kill (last-use) more
///    VRegs. This reduces the number of simultaneously live values.
///
/// 3. **Short live-range preference**: Among producers, prefer those whose
///    consumers are ready soon (fewer remaining deps on successors). This
///    keeps newly defined values short-lived.
///
/// 4. **Net pressure tie-breaking**: When critical-path priorities are equal,
///    prefer nodes with lower net pressure (kills - defs), i.e., nodes that
///    release more registers than they define.
///
/// The combined heuristic ordering when pressure is high:
///   1. Nodes with negative net_pressure (more kills than defs) first
///   2. Among those, highest critical-path priority
///   3. Among equal, prefer original order for stability
///
/// When pressure is below threshold, falls back to pure critical-path priority
/// (same as `schedule_list`), preserving ILP optimization.
pub fn schedule_list_pressure_aware(
    func: &MachFunction,
    dag: &mut ScheduleDAG,
) -> (Vec<InstId>, PressureTracker) {
    let n = dag.nodes.len();
    if n == 0 {
        return (Vec::new(), PressureTracker::new());
    }

    let pressure_info = compute_pressure_info(func, dag);
    let mut tracker = PressureTracker::new();

    // Recompute last-use accounting relative to the scheduling order.
    // We track remaining use counts for each VReg: when a VReg's remaining
    // uses reach 0, it is killed.
    let mut vreg_remaining_uses: HashMap<VReg, u32> = HashMap::default();
    for info in &pressure_info {
        for &vreg in &info.uses {
            *vreg_remaining_uses.entry(vreg).or_insert(0) += 1;
        }
    }

    let mut scheduled_order: Vec<InstId> = Vec::with_capacity(n);
    let mut remaining_deps: Vec<usize> = dag.nodes.iter().map(|node| node.deps.len()).collect();
    let mut cycle: u32 = 0;

    // Incremental ready-set holding BOTH selection orders at once, because
    // `high_pressure` is recomputed every step and may flip either way. The keys
    // reproduce the two comparators the previous `sort_by` used, so the selected
    // node — and therefore the emitted schedule — is unchanged. See `ReadySet`.
    let mut ready = ReadySet::new(
        dag.nodes.iter().map(|node| node.priority).collect(),
        Some(pressure_info.iter().map(|i| i.net_pressure).collect()),
    );
    for (i, deps) in remaining_deps.iter().enumerate() {
        if *deps == 0 {
            ready.admit(i, dag.nodes[i].earliest_start, cycle);
        }
    }

    while scheduled_order.len() < n {
        ready.advance_to(cycle);

        if ready.is_ready_empty() {
            let Some(min_start) = ready.next_pending_start() else {
                // Cyclic dependencies mean the scheduler cannot prove any
                // non-original order is legal. Preserve the original region
                // order instead of breaking a dependency edge.
                return (preserve_original_order(dag), tracker);
            };
            cycle = min_start;
            continue;
        }

        let high_pressure = tracker.is_high_pressure();

        let Some(best) = ready.take_best(high_pressure) else {
            return (preserve_original_order(dag), tracker);
        };
        dag.nodes[best].scheduled = true;
        dag.nodes[best].earliest_start = cycle;
        scheduled_order.push(dag.nodes[best].inst_id);

        // Update pressure: process uses (potential kills) before defs.
        // When we schedule an instruction, its used VRegs have their remaining
        // use count decremented. If it reaches 0, the VReg is killed.
        for &vreg in &pressure_info[best].uses {
            if let Some(count) = vreg_remaining_uses.get_mut(&vreg) {
                *count = count.saturating_sub(1);
                if *count == 0 {
                    tracker.kill_vreg(vreg);
                }
            }
        }

        // Process defs: newly defined VRegs become live.
        for &vreg in &pressure_info[best].defs {
            tracker.define_vreg(vreg);
        }

        // Update dependents.
        // Use saturating_sub because force-scheduled nodes may have had their
        // remaining_deps zeroed, causing a successor's count to underflow if
        // decremented again by a different predecessor in a cycle.
        let finish = cycle + dag.nodes[best].latency;
        let rev_deps = dag.nodes[best].rev_deps.clone();
        for &succ in &rev_deps {
            remaining_deps[succ] = remaining_deps[succ].saturating_sub(1);
            if dag.nodes[succ].earliest_start < finish {
                dag.nodes[succ].earliest_start = finish;
                ready.bump(succ, finish, cycle);
            }
            if remaining_deps[succ] == 0 {
                ready.admit(succ, dag.nodes[succ].earliest_start, cycle);
            }
        }

        cycle += 1;
    }

    (scheduled_order, tracker)
}

// ---------------------------------------------------------------------------
// Block and function scheduling
// ---------------------------------------------------------------------------

/// Find scheduling regions within a block by splitting at internal terminators.
///
/// A scheduling region is a maximal contiguous range of instructions that can
/// be reordered relative to each other. Conditional branches (BCond, Bcc, Cbz,
/// etc.) end a region because instructions after them should only execute if
/// the branch is not taken. The branch itself is part of the region it ends.
///
/// Returns a list of (start_index, end_index) pairs (inclusive).
///
/// For a normal block with one terminator at the end, this returns a single
/// region spanning the entire block. For blocks created by CfgSimplify that
/// merge a conditional-branch block with its fallthrough block, this returns
/// multiple regions.
fn find_scheduling_regions(func: &MachFunction, block_id: BlockId) -> Vec<(usize, usize)> {
    let block = func.block(block_id);
    let insts = &block.insts;

    if insts.is_empty() {
        return vec![];
    }

    let mut regions = Vec::new();
    let mut region_start = 0;

    for (i, &inst_id) in insts.iter().enumerate() {
        let inst = func.inst(inst_id);
        // Any internal terminator ends a region (and is part of it). A `ret`
        // can appear before leftover unreachable instructions after earlier
        // CFG cleanup, and conditional branches can guard the fallthrough tail.
        if i < insts.len() - 1 && inst.flags.contains(InstFlags::IS_TERMINATOR) {
            regions.push((region_start, i));
            region_start = i + 1;
        }
    }

    // Final region: from the last split point to the end.
    regions.push((region_start, insts.len() - 1));

    regions
}

fn cross_block_redefined_vregs(func: &MachFunction) -> HashSet<VReg> {
    let mut first_def_block: HashMap<VReg, BlockId> = HashMap::default();
    let mut redefined = HashSet::default();

    for &block_id in &func.block_order {
        let mut block_defs = HashSet::default();
        for &inst_id in &func.block(block_id).insts {
            let inst = func.inst(inst_id);
            for_each_explicit_vreg_def(inst, |vreg| {
                block_defs.insert(vreg);
            });
        }

        for vreg in block_defs {
            if let Some(first_block) = first_def_block.insert(vreg, block_id)
                && first_block != block_id
            {
                redefined.insert(vreg);
            }
        }
    }

    redefined
}

fn block_touches_cross_block_redefined_vreg(
    func: &MachFunction,
    block_id: BlockId,
    redefined: &HashSet<VReg>,
) -> bool {
    if redefined.is_empty() {
        return false;
    }

    func.block(block_id).insts.iter().any(|&inst_id| {
        let inst = func.inst(inst_id);
        let mut touches = false;
        for_each_explicit_vreg_def(inst, |vreg| {
            touches = touches || redefined.contains(&vreg);
        });
        if !touches {
            for_each_explicit_vreg_use(inst, |vreg| {
                touches = touches || redefined.contains(&vreg);
            });
        }
        touches
    })
}

/// Schedule one basic block: build DAG, run list scheduling, reorder instructions.
///
/// Returns true if the instruction order changed.
pub fn schedule_block(func: &mut MachFunction, block_id: BlockId) -> bool {
    let redefined = cross_block_redefined_vregs(func);
    schedule_block_with_redefined_vregs(func, block_id, &redefined)
}

fn schedule_block_with_redefined_vregs(
    func: &mut MachFunction,
    block_id: BlockId,
    redefined: &HashSet<VReg>,
) -> bool {
    let block = func.block(block_id);
    if block.insts.len() <= 1 {
        return false;
    }

    // Lowered block parameters are represented as edge-local copies into the
    // same VReg from multiple predecessor blocks. That non-SSA web is correct
    // in original order, but pre-RA scheduling can widen the web enough to
    // expose allocator/parallel-copy hazards. Preserve those blocks until the
    // allocator models cross-block phi copies directly.
    if block_touches_cross_block_redefined_vreg(func, block_id, redefined) {
        return false;
    }

    // Split the block into scheduling regions at internal terminators.
    // CfgSimplify can merge blocks, creating blocks where a BCond appears
    // in the middle followed by the fallthrough path. The scheduler must
    // NOT reorder instructions across such internal terminators, because
    // instructions after a conditional branch only execute if the branch
    // is not taken.
    let regions = find_scheduling_regions(func, block_id);

    if regions.len() <= 1 {
        // Single region: schedule the whole block as before.
        let original_order: Vec<InstId> = block.insts.clone();
        let mut dag = build_dag(func, block_id);
        let new_order = schedule_list(&mut dag);

        if new_order == original_order {
            return false;
        }

        let block_mut = func.block_mut(block_id);
        block_mut.insts = new_order;
        return true;
    }

    // Multiple regions: schedule each independently and concatenate.
    let original_order: Vec<InstId> = block.insts.clone();
    let mut new_full_order: Vec<InstId> = Vec::with_capacity(original_order.len());

    for (start, end) in &regions {
        let region_insts: Vec<InstId> = original_order[*start..=*end].to_vec();
        if region_insts.len() <= 1 {
            new_full_order.extend(&region_insts);
            continue;
        }

        let mut dag = build_dag_for_insts(func, &region_insts);
        let scheduled = schedule_list(&mut dag);

        new_full_order.extend(scheduled);
    }

    if new_full_order == original_order {
        return false;
    }

    let block_mut = func.block_mut(block_id);
    block_mut.insts = new_full_order;
    true
}

/// Schedule one basic block with register pressure awareness.
///
/// Uses pressure-aware heuristics to balance ILP against register pressure.
/// Returns true if the instruction order changed, along with the pressure tracker.
pub fn schedule_block_pressure_aware(
    func: &mut MachFunction,
    block_id: BlockId,
) -> (bool, PressureTracker) {
    let redefined = cross_block_redefined_vregs(func);
    schedule_block_pressure_aware_with_redefined_vregs(func, block_id, &redefined)
}

fn schedule_block_pressure_aware_with_redefined_vregs(
    func: &mut MachFunction,
    block_id: BlockId,
    redefined: &HashSet<VReg>,
) -> (bool, PressureTracker) {
    let block = func.block(block_id);
    if block.insts.len() <= 1 {
        return (false, PressureTracker::new());
    }

    if block_touches_cross_block_redefined_vreg(func, block_id, redefined) {
        return (false, PressureTracker::new());
    }

    // Split the block into scheduling regions at internal terminators,
    // same as schedule_block. See find_scheduling_regions for rationale.
    let regions = find_scheduling_regions(func, block_id);

    if regions.len() <= 1 {
        // Single region: schedule the whole block as before.
        let original_order: Vec<InstId> = block.insts.clone();
        let mut dag = build_dag(func, block_id);
        let (new_order, tracker) = schedule_list_pressure_aware(func, &mut dag);

        if new_order == original_order {
            return (false, tracker);
        }

        let block_mut = func.block_mut(block_id);
        block_mut.insts = new_order;
        return (true, tracker);
    }

    // Multiple regions: schedule each independently.
    let original_order: Vec<InstId> = block.insts.clone();
    let mut new_full_order: Vec<InstId> = Vec::with_capacity(original_order.len());
    let mut combined_tracker = PressureTracker::new();

    for (start, end) in &regions {
        let region_insts: Vec<InstId> = original_order[*start..=*end].to_vec();
        if region_insts.len() <= 1 {
            new_full_order.extend(&region_insts);
            continue;
        }

        let mut dag = build_dag_for_insts(func, &region_insts);
        let (scheduled, tracker) = schedule_list_pressure_aware(func, &mut dag);

        // Accumulate pressure from the last region (approximation).
        combined_tracker = tracker;
        new_full_order.extend(scheduled);
    }

    if new_full_order == original_order {
        return (false, combined_tracker);
    }

    let block_mut = func.block_mut(block_id);
    block_mut.insts = new_full_order;
    (true, combined_tracker)
}

/// Schedule all basic blocks in a function.
///
/// Returns true if any block was reordered.
pub fn schedule_function(func: &mut MachFunction) -> bool {
    let mut changed = false;
    let redefined = cross_block_redefined_vregs(func);
    let block_ids: Vec<BlockId> = func.block_order.clone();
    for block_id in block_ids {
        if schedule_block_with_redefined_vregs(func, block_id, &redefined) {
            changed = true;
        }
    }
    changed
}

/// Schedule all basic blocks in a function with register pressure awareness.
///
/// Returns true if any block was reordered, along with peak GPR and FPR
/// pressure across all blocks.
pub fn schedule_function_pressure_aware(func: &mut MachFunction) -> (bool, u32, u32) {
    let mut changed = false;
    let mut peak_gpr: u32 = 0;
    let mut peak_fpr: u32 = 0;
    let redefined = cross_block_redefined_vregs(func);
    let block_ids: Vec<BlockId> = func.block_order.clone();
    for block_id in block_ids {
        let (block_changed, tracker) =
            schedule_block_pressure_aware_with_redefined_vregs(func, block_id, &redefined);
        if block_changed {
            changed = true;
        }
        peak_gpr = peak_gpr.max(tracker.peak_gpr);
        peak_fpr = peak_fpr.max(tracker.peak_fpr);
    }
    (changed, peak_gpr, peak_fpr)
}

// ---------------------------------------------------------------------------
// MachinePass implementation
// ---------------------------------------------------------------------------

/// Instruction scheduling pass for AArch64.
///
/// Reorders instructions within each basic block to maximize ILP and
/// minimize pipeline stalls. Runs as a pre-register-allocation pass.
pub struct InstructionScheduler;

impl MachinePass for InstructionScheduler {
    fn name(&self) -> &str {
        "instruction-scheduler"
    }

    fn run(&mut self, func: &mut MachFunction) -> bool {
        schedule_function(func)
    }

    fn run_with_provenance(
        &mut self,
        func: &mut MachFunction,
        _provenance: &mut ProvenanceMap,
    ) -> bool {
        // Reordering only permutes existing InstIds within block instruction
        // lists. Source mappings stay attached to those InstIds, so recording a
        // provenance transform would imply an instruction rewrite that did not
        // happen.
        self.run(func)
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

/// Pressure-aware instruction scheduling pass for AArch64.
///
/// Like `InstructionScheduler` but trades some ILP for lower register pressure.
/// When the number of live virtual registers exceeds a threshold (20 GPR, 24 FPR),
/// the scheduler prefers consuming instructions (that kill operands) over producing
/// instructions (that define new values). This reduces peak register pressure and
/// avoids unnecessary spills during register allocation.
///
/// Should be used instead of `InstructionScheduler` when register pressure is a
/// concern (large basic blocks, many live values).
pub struct PressureAwareScheduler;

impl MachinePass for PressureAwareScheduler {
    fn name(&self) -> &str {
        "pressure-aware-scheduler"
    }

    fn run(&mut self, func: &mut MachFunction) -> bool {
        let (changed, _, _) = schedule_function_pressure_aware(func);
        changed
    }

    fn run_with_provenance(
        &mut self,
        func: &mut MachFunction,
        _provenance: &mut ProvenanceMap,
    ) -> bool {
        // The pressure-aware variant shares the same mutation contract as the
        // basic scheduler: it only permutes existing InstIds and leaves
        // instruction/source provenance untouched.
        self.run(func)
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

// ---------------------------------------------------------------------------
// Phase 2: Resource hazard tracking and pipeline analysis
// ---------------------------------------------------------------------------

/// Returns the number of execution units available for a given port
/// on Apple M1 Firestorm.
///
/// Reference: Dougall Johnson, "Apple M1 Firestorm Microarchitecture"
pub fn port_capacity(port: ExecutionPort) -> u32 {
    match port {
        ExecutionPort::IntAlu => 6,
        ExecutionPort::IntMul => 2,
        ExecutionPort::IntDiv => 1,
        ExecutionPort::LoadStore => 2,
        ExecutionPort::Branch => 1,
        ExecutionPort::FpAlu => 4,
    }
}

// ---------------------------------------------------------------------------
// Resource state tracking
// ---------------------------------------------------------------------------

/// Tracks execution unit availability per cycle for structural hazard detection.
///
/// Models the Apple M1 Firestorm port availability: at each cycle, each port
/// has a fixed number of units. Scheduling an instruction on a port at a cycle
/// consumes one unit. A structural hazard occurs when all units of a port are
/// occupied at a given cycle.
#[derive(Debug, Clone)]
pub struct ResourceState {
    /// Per-cycle usage: (port, cycle) -> units currently in use.
    usage: HashMap<(ExecutionPort, u32), u32>,
}

impl ResourceState {
    /// Create a new resource state with no reservations.
    pub fn new() -> Self {
        Self {
            usage: HashMap::default(),
        }
    }

    /// Returns the number of units still available for `port` at `cycle`.
    pub fn units_available(&self, port: ExecutionPort, cycle: u32) -> u32 {
        let cap = port_capacity(port);
        let used = self.usage.get(&(port, cycle)).copied().unwrap_or(0);
        cap.saturating_sub(used)
    }

    /// Returns true if at least one unit is available for `port` at `cycle`.
    pub fn is_available(&self, port: ExecutionPort, cycle: u32) -> bool {
        self.units_available(port, cycle) > 0
    }

    /// Reserve one unit of `port` at `cycle`. Returns true if successful,
    /// false if all units are already occupied (structural hazard).
    pub fn reserve(&mut self, port: ExecutionPort, cycle: u32) -> bool {
        if !self.is_available(port, cycle) {
            return false;
        }
        *self.usage.entry((port, cycle)).or_insert(0) += 1;
        true
    }
}

impl Default for ResourceState {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// Hazard detection
// ---------------------------------------------------------------------------

/// Classification of pipeline hazards detected in a schedule.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum HazardKind {
    /// Data hazard: a consumer had to wait for a producer's result.
    /// `wait_cycles` is the number of stall cycles (earliest_start difference
    /// minus 1 for the dispatch slot).
    DataHazard {
        producer: usize,
        consumer: usize,
        wait_cycles: u32,
    },
    /// Structural hazard: all execution units for a port were busy at a cycle.
    StructuralHazard { port: ExecutionPort, cycle: u32 },
    /// Load-use hazard: a load result is consumed in the very next instruction
    /// in program order, causing a pipeline bubble. This is a special case of
    /// data hazard common on in-order cores and still costly on OoO cores
    /// when the load misses cache.
    LoadUseHazard { load_node: usize, use_node: usize },
}

/// Detect pipeline hazards in a scheduled DAG.
///
/// Precondition: the DAG must have been through `schedule_list` so that
/// `earliest_start` and `scheduled` are populated for all nodes.
pub fn detect_hazards(dag: &ScheduleDAG) -> Vec<HazardKind> {
    let mut hazards = Vec::new();
    let n = dag.nodes.len();

    // Build a resource state from the schedule.
    let mut resources = ResourceState::new();
    for node in &dag.nodes {
        if !resources.reserve(node.port, node.earliest_start) {
            hazards.push(HazardKind::StructuralHazard {
                port: node.port,
                cycle: node.earliest_start,
            });
        }
    }

    // Check data hazards: for each edge, if the consumer's earliest_start
    // is later than (producer earliest_start + 1), the consumer stalled
    // waiting for data.
    for consumer_idx in 0..n {
        let consumer_start = dag.nodes[consumer_idx].earliest_start;
        for &producer_idx in &dag.nodes[consumer_idx].deps {
            let producer_start = dag.nodes[producer_idx].earliest_start;
            let producer_latency = dag.nodes[producer_idx].latency;
            let ready_cycle = producer_start + producer_latency;
            if consumer_start >= ready_cycle && consumer_start > producer_start + 1 {
                let wait_cycles = consumer_start.saturating_sub(producer_start + 1);
                if wait_cycles > 0 {
                    hazards.push(HazardKind::DataHazard {
                        producer: producer_idx,
                        consumer: consumer_idx,
                        wait_cycles,
                    });
                }
            }
        }
    }

    // Check load-use hazards: load followed by consumer at (earliest_start + 1).
    // This is a pipeline forwarding stall on many microarchitectures.
    for consumer_idx in 0..n {
        for &producer_idx in &dag.nodes[consumer_idx].deps {
            if dag.nodes[producer_idx].port == ExecutionPort::LoadStore
                && dag.nodes[producer_idx].latency >= 4
            {
                // This producer is a load (latency >= 4 distinguishes loads from stores).
                let load_start = dag.nodes[producer_idx].earliest_start;
                let consumer_start = dag.nodes[consumer_idx].earliest_start;
                // If consumer is scheduled before load result is ready, that means
                // the scheduler had to wait. If consumer is at load_start + 1,
                // it's a tight load-use pair.
                if consumer_start == load_start + 1 {
                    hazards.push(HazardKind::LoadUseHazard {
                        load_node: producer_idx,
                        use_node: consumer_idx,
                    });
                }
            }
        }
    }

    hazards
}

// ---------------------------------------------------------------------------
// Dual-issue hints
// ---------------------------------------------------------------------------

/// A hint that two instructions can potentially dual-issue on Apple M-series.
///
/// Apple M1 Firestorm can dispatch up to 8 micro-ops per cycle across its
/// execution ports. Two instructions can dual-issue if they use different
/// port types and both are ready at the same cycle.
#[derive(Debug, Clone)]
pub struct DualIssueHint {
    /// First node index.
    pub first: usize,
    /// Second node index.
    pub second: usize,
    /// Human-readable reason for the dual-issue opportunity.
    pub reason: &'static str,
}

/// Returns true if two ports can potentially dual-issue.
///
/// Dual-issue pairs on Apple M-series:
/// - ALU + Load/Store
/// - ALU + ALU (6 ALU units)
/// - ALU + Branch
/// - ALU + FpAlu
/// - Load/Store + FpAlu
fn can_dual_issue(a: ExecutionPort, b: ExecutionPort) -> Option<&'static str> {
    use ExecutionPort::*;
    match (a, b) {
        (IntAlu, LoadStore) | (LoadStore, IntAlu) => Some("ALU + Load/Store"),
        (IntAlu, IntAlu) => Some("ALU + ALU"),
        (IntAlu, Branch) | (Branch, IntAlu) => Some("ALU + Branch"),
        (IntAlu, FpAlu) | (FpAlu, IntAlu) => Some("ALU + FP"),
        (LoadStore, FpAlu) | (FpAlu, LoadStore) => Some("Load/Store + FP"),
        (FpAlu, FpAlu) => Some("FP + FP"),
        _ => None,
    }
}

/// Find dual-issue opportunities in a scheduled DAG.
///
/// The list scheduler issues one instruction per cycle, but Apple M1 Firestorm
/// can dispatch up to 8 micro-ops per cycle. This analysis identifies
/// consecutive instruction pairs in the schedule where:
/// 1. Both were ready within the same cycle window (within 1 cycle).
/// 2. They use compatible execution ports.
/// 3. They are NOT directly dependent on each other (no edge between them).
///
/// These pairs *could* have been dual-issued on real hardware even though
/// our simple list scheduler serializes them.
pub fn find_dual_issue_hints(dag: &ScheduleDAG) -> Vec<DualIssueHint> {
    let mut hints = Vec::new();
    let n = dag.nodes.len();
    if n < 2 {
        return hints;
    }

    // Build a set of direct dependency edges for O(1) lookup.
    let mut dep_edges: HashSet<(usize, usize)> = HashSet::default();
    for (idx, node) in dag.nodes.iter().enumerate() {
        for &pred in &node.deps {
            dep_edges.insert((pred, idx));
        }
    }

    // Build schedule order sorted by (earliest_start, node_index).
    let mut schedule_order: Vec<(u32, usize)> =
        (0..n).map(|i| (dag.nodes[i].earliest_start, i)).collect();
    schedule_order.sort_by_key(|&(cycle, idx)| (cycle, idx));

    // Check consecutive pairs: if both were ready within 1 cycle and are
    // independent, they could dual-issue.
    for window in schedule_order.windows(2) {
        let (cycle_a, idx_a) = window[0];
        let (cycle_b, idx_b) = window[1];

        // Must be within 1 cycle of each other (list scheduler serialization).
        if cycle_b > cycle_a + 1 {
            continue;
        }

        // Must not be directly dependent.
        if dep_edges.contains(&(idx_a, idx_b)) || dep_edges.contains(&(idx_b, idx_a)) {
            continue;
        }

        let port_a = dag.nodes[idx_a].port;
        let port_b = dag.nodes[idx_b].port;
        if let Some(reason) = can_dual_issue(port_a, port_b) {
            hints.push(DualIssueHint {
                first: idx_a,
                second: idx_b,
                reason,
            });
        }
    }

    hints
}

// ---------------------------------------------------------------------------
// Register pressure tracking
// ---------------------------------------------------------------------------

/// Register pressure snapshot during scheduling.
///
/// Tracks the maximum number of simultaneously live GPR and FPR virtual
/// registers. If pressure exceeds the allocatable register count, the
/// register allocator will need to spill, which is expensive.
#[derive(Debug, Clone)]
pub struct RegisterPressure {
    /// Current GPR live count.
    pub gpr_pressure: u32,
    /// Current FPR live count.
    pub fpr_pressure: u32,
    /// Maximum GPR pressure seen during the schedule.
    pub max_gpr_pressure: u32,
    /// Maximum FPR pressure seen during the schedule.
    pub max_fpr_pressure: u32,
    /// GPR limit before spilling is expected (allocatable GPRs on AArch64).
    pub gpr_limit: u32,
    /// FPR limit before spilling is expected (allocatable FPRs on AArch64).
    pub fpr_limit: u32,
}

impl RegisterPressure {
    /// Returns true if register pressure exceeded the allocatable limit
    /// at any point during scheduling.
    pub fn pressure_exceeded(&self) -> bool {
        self.max_gpr_pressure > self.gpr_limit || self.max_fpr_pressure > self.fpr_limit
    }
}

/// Compute register pressure for a scheduled instruction order.
///
/// Walks the schedule in order, tracking which vregs are live. A vreg
/// becomes live when defined and dies after its last use in the schedule.
///
/// Uses: AArch64 has 28 allocatable GPRs (X0-X28 minus FP/LR) and
/// 32 allocatable FPRs (V0-V31).
pub fn compute_register_pressure(
    func: &MachFunction,
    _block_id: BlockId,
    schedule: &[InstId],
) -> RegisterPressure {
    // GPR limit: X0-X28 = 29, minus X29(FP), X30(LR) => 28 allocatable.
    // FPR limit: V0-V31, callee-saved V8-V15 still allocatable => 32.
    let gpr_limit: u32 = 28;
    let fpr_limit: u32 = 32;

    // Build last-use map keyed by full virtual-register identity. Numeric ids
    // are only unique within a register class.
    let mut last_use_pos: HashMap<VReg, usize> = HashMap::default();

    for (pos, &inst_id) in schedule.iter().enumerate() {
        let inst = func.inst(inst_id);

        for_each_explicit_vreg_use(inst, |vreg| {
            last_use_pos.insert(vreg, pos);
        });
    }

    // Walk schedule positions, maintaining live set.
    let mut live_gprs: HashSet<VReg> = HashSet::default();
    let mut live_fprs: HashSet<VReg> = HashSet::default();
    let mut max_gpr: u32 = 0;
    let mut max_fpr: u32 = 0;

    for (pos, &inst_id) in schedule.iter().enumerate() {
        let inst = func.inst(inst_id);

        for_each_explicit_vreg_def(inst, |vreg| {
            let is_fpr = matches!(
                vreg.class,
                RegClass::Fpr128
                    | RegClass::Fpr64
                    | RegClass::Fpr32
                    | RegClass::Fpr16
                    | RegClass::Fpr8
            );
            if is_fpr {
                live_fprs.insert(vreg);
            } else {
                live_gprs.insert(vreg);
            }
        });

        // Update max pressure.
        max_gpr = max_gpr.max(live_gprs.len() as u32);
        max_fpr = max_fpr.max(live_fprs.len() as u32);

        // Remove dead vregs (last use at this position).
        // Collect into a Vec first to avoid borrowing conflicts.
        let dead_gprs: Vec<VReg> = live_gprs
            .iter()
            .filter(|&&vreg| last_use_pos.get(&vreg).copied() == Some(pos))
            .copied()
            .collect();
        for vreg in dead_gprs {
            live_gprs.remove(&vreg);
        }

        let dead_fprs: Vec<VReg> = live_fprs
            .iter()
            .filter(|&&vreg| last_use_pos.get(&vreg).copied() == Some(pos))
            .copied()
            .collect();
        for vreg in dead_fprs {
            live_fprs.remove(&vreg);
        }
    }

    RegisterPressure {
        gpr_pressure: live_gprs.len() as u32,
        fpr_pressure: live_fprs.len() as u32,
        max_gpr_pressure: max_gpr,
        max_fpr_pressure: max_fpr,
        gpr_limit,
        fpr_limit,
    }
}

// ---------------------------------------------------------------------------
// Schedule quality metrics
// ---------------------------------------------------------------------------

/// Quality metrics for a computed schedule.
///
/// Provides a quantitative assessment of how well the scheduler has
/// utilized execution resources and avoided pipeline hazards.
#[derive(Debug, Clone)]
pub struct ScheduleMetrics {
    /// Total number of instructions scheduled.
    pub total_instructions: usize,
    /// Total execution cycles (span from first to last instruction completion).
    pub total_cycles: u32,
    /// Estimated instructions per cycle (IPC).
    pub ipc_estimate: f64,
    /// Number of cycles where the pipeline stalled (no instruction issued
    /// despite pending work).
    pub stall_count: u32,
    /// Number of data hazards detected.
    pub data_hazards: u32,
    /// Number of structural hazards detected.
    pub structural_hazards: u32,
    /// Length of the critical path in cycles.
    pub critical_path_length: u32,
    /// Number of dual-issue opportunities found.
    pub dual_issue_opportunities: u32,
    /// Maximum GPR register pressure.
    pub max_gpr_pressure: u32,
    /// Maximum FPR register pressure.
    pub max_fpr_pressure: u32,
    /// Whether register pressure exceeded allocatable limits.
    pub pressure_exceeded: bool,
}

/// Compute comprehensive schedule quality metrics.
///
/// Requires a DAG that has been through `schedule_list` (earliest_start populated)
/// and the resulting instruction order.
pub fn compute_schedule_metrics(
    func: &MachFunction,
    block_id: BlockId,
    dag: &ScheduleDAG,
    schedule: &[InstId],
) -> ScheduleMetrics {
    let n = dag.nodes.len();
    if n == 0 {
        return ScheduleMetrics {
            total_instructions: 0,
            total_cycles: 0,
            ipc_estimate: 0.0,
            stall_count: 0,
            data_hazards: 0,
            structural_hazards: 0,
            critical_path_length: 0,
            dual_issue_opportunities: 0,
            max_gpr_pressure: 0,
            max_fpr_pressure: 0,
            pressure_exceeded: false,
        };
    }

    // Total cycles: max(earliest_start + latency) across all nodes.
    let total_cycles = dag
        .nodes
        .iter()
        .map(|node| node.earliest_start + node.latency)
        .max()
        .unwrap_or(0);

    // IPC estimate.
    let ipc = if total_cycles > 0 {
        n as f64 / total_cycles as f64
    } else {
        n as f64
    };

    // Stall count: cycles where no instruction was issued.
    // Build a set of cycles where at least one instruction was scheduled.
    let mut issue_cycles: HashSet<u32> = HashSet::default();
    for node in &dag.nodes {
        issue_cycles.insert(node.earliest_start);
    }
    let max_issue_cycle = dag
        .nodes
        .iter()
        .map(|node| node.earliest_start)
        .max()
        .unwrap_or(0);
    let stall_count = (0..=max_issue_cycle)
        .filter(|c| !issue_cycles.contains(c))
        .count() as u32;

    // Critical path length: the maximum priority in the DAG
    // (which is the longest path from any node to any exit).
    let critical_path_length = dag
        .nodes
        .iter()
        .map(|node| node.priority)
        .max()
        .unwrap_or(0);

    // Hazard detection.
    let hazards = detect_hazards(dag);
    let data_hazards = hazards
        .iter()
        .filter(|h| matches!(h, HazardKind::DataHazard { .. }))
        .count() as u32;
    let structural_hazards = hazards
        .iter()
        .filter(|h| matches!(h, HazardKind::StructuralHazard { .. }))
        .count() as u32;

    // Dual-issue opportunities.
    let dual_hints = find_dual_issue_hints(dag);
    let dual_issue_opportunities = dual_hints.len() as u32;

    // Register pressure.
    let pressure = compute_register_pressure(func, block_id, schedule);

    ScheduleMetrics {
        total_instructions: n,
        total_cycles,
        ipc_estimate: ipc,
        stall_count,
        data_hazards,
        structural_hazards,
        critical_path_length,
        dual_issue_opportunities,
        max_gpr_pressure: pressure.max_gpr_pressure,
        max_fpr_pressure: pressure.max_fpr_pressure,
        pressure_exceeded: pressure.pressure_exceeded(),
    }
}

// ---------------------------------------------------------------------------
// Schedule block with metrics
// ---------------------------------------------------------------------------

fn trivial_schedule_metrics(inst_count: usize) -> ScheduleMetrics {
    ScheduleMetrics {
        total_instructions: inst_count,
        total_cycles: if inst_count == 0 { 0 } else { 1 },
        ipc_estimate: if inst_count == 0 { 0.0 } else { 1.0 },
        stall_count: 0,
        data_hazards: 0,
        structural_hazards: 0,
        critical_path_length: if inst_count == 0 { 0 } else { 1 },
        dual_issue_opportunities: 0,
        max_gpr_pressure: 0,
        max_fpr_pressure: 0,
        pressure_exceeded: false,
    }
}

fn compute_existing_order_metrics(func: &MachFunction, block_id: BlockId) -> ScheduleMetrics {
    let block = func.block(block_id);
    if block.insts.len() <= 1 {
        return trivial_schedule_metrics(block.insts.len());
    }

    let original_order = block.insts.clone();
    let mut dag = build_dag(func, block_id);
    preserve_original_order(&mut dag);
    compute_schedule_metrics(func, block_id, &dag, &original_order)
}

fn combine_schedule_metrics(metrics: &[ScheduleMetrics]) -> ScheduleMetrics {
    let total_instructions = metrics.iter().map(|m| m.total_instructions).sum();
    let total_cycles = metrics.iter().map(|m| m.total_cycles).sum();
    let ipc_estimate = if total_cycles > 0 {
        total_instructions as f64 / total_cycles as f64
    } else {
        0.0
    };

    ScheduleMetrics {
        total_instructions,
        total_cycles,
        ipc_estimate,
        stall_count: metrics.iter().map(|m| m.stall_count).sum(),
        data_hazards: metrics.iter().map(|m| m.data_hazards).sum(),
        structural_hazards: metrics.iter().map(|m| m.structural_hazards).sum(),
        critical_path_length: metrics.iter().map(|m| m.critical_path_length).sum(),
        dual_issue_opportunities: metrics.iter().map(|m| m.dual_issue_opportunities).sum(),
        max_gpr_pressure: metrics
            .iter()
            .map(|m| m.max_gpr_pressure)
            .max()
            .unwrap_or(0),
        max_fpr_pressure: metrics
            .iter()
            .map(|m| m.max_fpr_pressure)
            .max()
            .unwrap_or(0),
        pressure_exceeded: metrics.iter().any(|m| m.pressure_exceeded),
    }
}

/// Schedule one basic block and return both the reordering result and
/// quality metrics for the schedule.
pub fn schedule_block_with_metrics(
    func: &mut MachFunction,
    block_id: BlockId,
) -> (bool, ScheduleMetrics) {
    let block = func.block(block_id);
    if block.insts.len() <= 1 {
        return (false, trivial_schedule_metrics(block.insts.len()));
    }

    let redefined = cross_block_redefined_vregs(func);
    if block_touches_cross_block_redefined_vreg(func, block_id, &redefined) {
        return (false, compute_existing_order_metrics(func, block_id));
    }

    let original_order: Vec<InstId> = block.insts.clone();
    let regions = find_scheduling_regions(func, block_id);

    if regions.len() <= 1 {
        let mut dag = build_dag(func, block_id);
        let new_order = schedule_list(&mut dag);

        let metrics = compute_schedule_metrics(func, block_id, &dag, &new_order);

        let changed = new_order != original_order;
        if changed {
            let block_mut = func.block_mut(block_id);
            block_mut.insts = new_order;
        }

        return (changed, metrics);
    }

    let mut new_full_order: Vec<InstId> = Vec::with_capacity(original_order.len());
    let mut region_metrics = Vec::with_capacity(regions.len());

    for (start, end) in &regions {
        let region_insts: Vec<InstId> = original_order[*start..=*end].to_vec();
        if region_insts.len() <= 1 {
            new_full_order.extend(&region_insts);
            region_metrics.push(trivial_schedule_metrics(region_insts.len()));
            continue;
        }

        let mut dag = build_dag_for_insts(func, &region_insts);
        let scheduled = schedule_list(&mut dag);
        let metrics = compute_schedule_metrics(func, block_id, &dag, &scheduled);

        new_full_order.extend(scheduled);
        region_metrics.push(metrics);
    }

    let metrics = combine_schedule_metrics(&region_metrics);
    let changed = new_full_order != original_order;
    if changed {
        let block_mut = func.block_mut(block_id);
        block_mut.insts = new_full_order;
    }

    (changed, metrics)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pass_manager::{AnalysisCache, MachinePass};
    use std::time::Instant;
    use trust_cg_ir::regs::{W0, X0, X1, X2, X16};
    use trust_cg_ir::{
        AArch64Opcode, MachFunction, MachInst, MachOperand, PassId, ProvenanceMap, RegClass,
        Signature, TransformKind, TrustIrInstId, VReg,
    };

    fn vreg(id: u32) -> MachOperand {
        MachOperand::VReg(VReg::new(id, RegClass::Gpr64))
    }

    fn typed_vreg(id: u32, class: RegClass) -> MachOperand {
        MachOperand::VReg(VReg::new(id, class))
    }

    fn imm(val: i64) -> MachOperand {
        MachOperand::Imm(val)
    }

    fn record_identity_provenance(
        func: &MachFunction,
        first_trust_ir: u32,
    ) -> (ProvenanceMap, Vec<(TrustIrInstId, InstId)>) {
        let mut provenance = ProvenanceMap::new();
        let mut mappings = Vec::new();

        for &block_id in &func.block_order {
            for &inst_id in &func.block(block_id).insts {
                let trust_ir = TrustIrInstId(first_trust_ir + mappings.len() as u32);
                provenance.record_lowering(trust_ir, &[inst_id], PassId::new("isel"));
                mappings.push((trust_ir, inst_id));
            }
        }

        (provenance, mappings)
    }

    fn assert_identity_provenance_survived(
        provenance: &ProvenanceMap,
        mappings: &[(TrustIrInstId, InstId)],
    ) {
        for &(trust_ir, inst_id) in mappings {
            assert_eq!(
                provenance
                    .get_mach_insts(trust_ir)
                    .expect("source mapping should remain present"),
                std::slice::from_ref(&inst_id)
            );

            let entry = provenance
                .get_entry(inst_id)
                .expect("instruction should keep provenance entry");
            assert!(entry.is_active());
            assert_eq!(entry.trust_ir_origins, vec![trust_ir]);
            assert_eq!(entry.transforms.len(), 1);
            assert_eq!(&entry.transforms[0].pass, &PassId::new("isel"));
            assert_eq!(&entry.transforms[0].kind, &TransformKind::Lowered);
        }
    }

    fn proof_reorderable_inst(opcode: AArch64Opcode, operands: Vec<MachOperand>) -> MachInst {
        MachInst::with_flags(
            opcode,
            operands,
            opcode.default_flags() | InstFlags::PROOF_REORDERABLE,
        )
    }

    fn proof_reorderable_load(dst: u32, base: u32, offset: i64) -> MachInst {
        proof_reorderable_inst(
            AArch64Opcode::LdrRI,
            vec![vreg(dst), vreg(base), imm(offset)],
        )
    }

    fn proof_reorderable_store(src: u32, base: u32, offset: i64) -> MachInst {
        proof_reorderable_inst(
            AArch64Opcode::StrRI,
            vec![vreg(src), vreg(base), imm(offset)],
        )
    }

    fn make_func_with_insts(insts: Vec<MachInst>) -> MachFunction {
        let mut func = MachFunction::new("test_sched".to_string(), Signature::new(vec![], vec![]));
        let block = func.entry;
        for inst in insts {
            let id = func.push_inst(inst);
            func.append_inst(block, id);
        }
        func
    }

    fn schedule_node(inst_id: InstId, deps: &[usize], rev_deps: &[usize]) -> ScheduleNode {
        ScheduleNode {
            inst_id,
            latency: 1,
            port: ExecutionPort::IntAlu,
            deps: deps.to_vec(),
            rev_deps: rev_deps.to_vec(),
            earliest_start: 0,
            priority: 0,
            scheduled: false,
        }
    }

    fn pos(inst: InstId, order: &[InstId]) -> usize {
        order.iter().position(|&id| id == inst).unwrap()
    }

    fn assert_dag_edge(dag: &ScheduleDAG, from: usize, to: usize, context: &str) {
        assert!(
            dag.nodes[to].deps.contains(&from),
            "{}: missing dependency edge {} -> {}",
            context,
            from,
            to
        );
        assert!(
            dag.nodes[from].rev_deps.contains(&to),
            "{}: missing reverse dependency edge {} -> {}",
            context,
            from,
            to
        );
    }

    fn assert_no_dag_edge(dag: &ScheduleDAG, from: usize, to: usize, context: &str) {
        assert!(
            !dag.nodes[to].deps.contains(&from),
            "{}: unexpected dependency edge {} -> {}",
            context,
            from,
            to
        );
        assert!(
            !dag.nodes[from].rev_deps.contains(&to),
            "{}: unexpected reverse dependency edge {} -> {}",
            context,
            from,
            to
        );
    }

    // ---- Latency model tests ----

    #[test]
    fn test_latency_alu() {
        let (lat, port) = opcode_latency(AArch64Opcode::AddRR);
        assert_eq!(lat, 1);
        assert_eq!(port, ExecutionPort::IntAlu);

        let (lat, port) = opcode_latency(AArch64Opcode::Rbit);
        assert_eq!(lat, 1);
        assert_eq!(port, ExecutionPort::IntAlu);
    }

    #[test]
    fn test_latency_mul() {
        let (lat, port) = opcode_latency(AArch64Opcode::MulRR);
        assert_eq!(lat, 3);
        assert_eq!(port, ExecutionPort::IntMul);
    }

    #[test]
    fn test_latency_div() {
        let (lat, port) = opcode_latency(AArch64Opcode::SDiv);
        assert_eq!(lat, 10);
        assert_eq!(port, ExecutionPort::IntDiv);
    }

    #[test]
    fn test_latency_load() {
        let (lat, port) = opcode_latency(AArch64Opcode::LdrRI);
        assert_eq!(lat, 4);
        assert_eq!(port, ExecutionPort::LoadStore);
    }

    #[test]
    fn test_latency_store() {
        let (lat, port) = opcode_latency(AArch64Opcode::StrRI);
        assert_eq!(lat, 1);
        assert_eq!(port, ExecutionPort::LoadStore);
    }

    #[test]
    fn test_latency_branch() {
        let (lat, port) = opcode_latency(AArch64Opcode::B);
        assert_eq!(lat, 1);
        assert_eq!(port, ExecutionPort::Branch);
    }

    #[test]
    fn test_latency_fp() {
        let (lat, port) = opcode_latency(AArch64Opcode::FaddRR);
        assert_eq!(lat, 3);
        assert_eq!(port, ExecutionPort::FpAlu);
    }

    // ---- Empty and trivial block tests ----

    #[test]
    fn test_empty_block() {
        let mut func = MachFunction::new("empty".to_string(), Signature::new(vec![], vec![]));
        let mut sched = InstructionScheduler;
        assert!(!sched.run(&mut func));
    }

    #[test]
    fn test_single_instruction() {
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![ret]);

        let mut sched = InstructionScheduler;
        assert!(!sched.run(&mut func));
    }

    #[test]
    fn test_compute_priorities_cycle_terminates() {
        let start = Instant::now();
        let mut dag = ScheduleDAG {
            nodes: vec![
                schedule_node(InstId(0), &[1], &[1]),
                schedule_node(InstId(1), &[0], &[0]),
            ],
        };

        dag.compute_priorities();

        assert!(
            start.elapsed().as_secs() < 5,
            "cyclic priority computation must be bounded"
        );
        assert_eq!(dag.nodes[0].priority, 1);
        assert_eq!(dag.nodes[1].priority, 1);
    }

    // ---- Data dependency tests ----

    #[test]
    fn test_data_dependency_respected() {
        // v1 = add v0, #1    (inst0)
        // v2 = add v1, #2    (inst1, depends on inst0)
        // ret                 (inst2)
        let add1 = MachInst::new(AArch64Opcode::AddRI, vec![vreg(1), vreg(0), imm(1)]);
        let add2 = MachInst::new(AArch64Opcode::AddRI, vec![vreg(2), vreg(1), imm(2)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![add1, add2, ret]);

        let mut sched = InstructionScheduler;
        sched.run(&mut func);

        let block = func.block(func.entry);
        let order: Vec<InstId> = block.insts.clone();

        // add1 must come before add2 (data dependency v1).
        let pos_add1 = order.iter().position(|&id| id == InstId(0)).unwrap();
        let pos_add2 = order.iter().position(|&id| id == InstId(1)).unwrap();
        assert!(
            pos_add1 < pos_add2,
            "add1 (def v1) must precede add2 (use v1)"
        );

        // ret must be last.
        assert_eq!(*order.last().unwrap(), InstId(2), "ret must be last");
    }

    // ---- Independent instructions reordering test ----

    #[test]
    fn test_independent_instructions_reordered() {
        // Original order:
        //   v1 = add v0, #1      (1 cycle, low priority)
        //   v2 = mul v3, v4      (3 cycles, high priority — longer critical path)
        //   v5 = add v2, #1      (uses v2)
        //   ret
        //
        // The scheduler should prefer to schedule mul first because it has
        // higher latency and its dependent (add v2, #1) is on the critical path.
        let add1 = MachInst::new(AArch64Opcode::AddRI, vec![vreg(1), vreg(0), imm(1)]);
        let mul = MachInst::new(AArch64Opcode::MulRR, vec![vreg(2), vreg(3), vreg(4)]);
        let add2 = MachInst::new(AArch64Opcode::AddRI, vec![vreg(5), vreg(2), imm(1)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![add1, mul, add2, ret]);

        let mut sched = InstructionScheduler;
        sched.run(&mut func);

        let block = func.block(func.entry);
        let order: Vec<InstId> = block.insts.clone();

        // mul (InstId(1)) should be scheduled before or at same position as
        // add1 (InstId(0)) because it has higher priority (3+1 > 1).
        let pos_mul = order.iter().position(|&id| id == InstId(1)).unwrap();
        let pos_add1 = order.iter().position(|&id| id == InstId(0)).unwrap();
        assert!(
            pos_mul <= pos_add1,
            "mul should be scheduled before add1 (critical path), got mul@{} add1@{}",
            pos_mul,
            pos_add1,
        );

        // add2 must come after mul (data dep on v2).
        let pos_add2 = order.iter().position(|&id| id == InstId(2)).unwrap();
        assert!(pos_mul < pos_add2, "add2 depends on mul");

        // ret must be last.
        assert_eq!(*order.last().unwrap(), InstId(3));
    }

    #[test]
    fn test_instruction_scheduler_provenance_survives_reorder() {
        let add1 = MachInst::new(AArch64Opcode::AddRI, vec![vreg(1), vreg(0), imm(1)]);
        let mul = MachInst::new(AArch64Opcode::MulRR, vec![vreg(2), vreg(3), vreg(4)]);
        let add2 = MachInst::new(AArch64Opcode::AddRI, vec![vreg(5), vreg(2), imm(1)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![add1, mul, add2, ret]);
        let original_order = func.block(func.entry).insts.clone();
        let (mut provenance, mappings) = record_identity_provenance(&func, 200);

        let mut sched = InstructionScheduler;
        let mut analyses = AnalysisCache::new();
        let changed =
            sched.run_with_analyses_and_provenance(&mut func, &mut analyses, &mut provenance);
        assert!(changed);

        let order = func.block(func.entry).insts.clone();
        assert_ne!(order, original_order);
        assert!(pos(InstId(1), &order) <= pos(InstId(0), &order));
        assert!(pos(InstId(1), &order) < pos(InstId(2), &order));
        assert_eq!(*order.last().unwrap(), InstId(3));
        assert_identity_provenance_survived(&provenance, &mappings);
    }

    #[test]
    fn test_scheduler_preserves_cross_block_phi_copy_webs() {
        let mut func = MachFunction::new(
            "test_phi_copy_web".to_string(),
            Signature::new(vec![], vec![]),
        );
        let entry = func.entry;
        let left = func.create_block();
        let right = func.create_block();
        let join = func.create_block();

        let branch_left = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(left)],
        ));
        func.append_inst(entry, branch_left);

        let left_add = func.push_inst(MachInst::new(
            AArch64Opcode::AddRI,
            vec![vreg(30), vreg(31), imm(1)],
        ));
        let left_mul = func.push_inst(MachInst::new(
            AArch64Opcode::MulRR,
            vec![vreg(32), vreg(33), vreg(34)],
        ));
        let left_copy = func.push_inst(MachInst::new(AArch64Opcode::MovR, vec![vreg(10), vreg(4)]));
        let left_branch = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(join)],
        ));
        func.append_inst(left, left_add);
        func.append_inst(left, left_mul);
        func.append_inst(left, left_copy);
        func.append_inst(left, left_branch);

        let right_copy =
            func.push_inst(MachInst::new(AArch64Opcode::MovR, vec![vreg(10), vreg(5)]));
        let right_branch = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(join)],
        ));
        func.append_inst(right, right_copy);
        func.append_inst(right, right_branch);

        let join_use = func.push_inst(MachInst::new(
            AArch64Opcode::AddRI,
            vec![vreg(11), vreg(10), imm(1)],
        ));
        let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(join, join_use);
        func.append_inst(join, ret);

        let left_original = func.block(left).insts.clone();
        let right_original = func.block(right).insts.clone();
        let join_original = func.block(join).insts.clone();

        let redefined = cross_block_redefined_vregs(&func);
        assert!(redefined.contains(&VReg::new(10, RegClass::Gpr64)));
        assert!(block_touches_cross_block_redefined_vreg(
            &func, left, &redefined
        ));
        assert!(block_touches_cross_block_redefined_vreg(
            &func, right, &redefined
        ));
        assert!(block_touches_cross_block_redefined_vreg(
            &func, join, &redefined
        ));

        let mut sched = InstructionScheduler;
        sched.run(&mut func);

        assert_eq!(func.block(left).insts, left_original);
        assert_eq!(func.block(right).insts, right_original);
        assert_eq!(func.block(join).insts, join_original);
    }

    // ---- Memory dependency tests ----

    #[test]
    fn test_memory_dependency_prevents_reorder() {
        // str v0, [sp, #0]    (store, inst0)
        // v1 = ldr [v2, #0]   (load, inst1 — must come after store)
        // ret                  (inst2)
        let store = MachInst::new(AArch64Opcode::StrRI, vec![vreg(0), vreg(10), imm(0)]);
        let load = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(1), vreg(2), imm(0)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![store, load, ret]);

        let mut sched = InstructionScheduler;
        sched.run(&mut func);

        let block = func.block(func.entry);
        let order: Vec<InstId> = block.insts.clone();

        // Store must come before load (conservative memory ordering).
        let pos_store = order.iter().position(|&id| id == InstId(0)).unwrap();
        let pos_load = order.iter().position(|&id| id == InstId(1)).unwrap();
        assert!(
            pos_store < pos_load,
            "store must precede load (memory dependency)"
        );
    }

    #[test]
    fn test_call_barrier_preserves_abi_arg_and_return_copies() {
        // Pre-regalloc call lowering uses physical ABI registers:
        //   x0  <- arg
        //   x16 <- callee
        //   blr x16
        //   ret_vreg <- x0
        //
        // The scheduler does not model PReg dataflow, so the call must act as
        // a barrier to keep argument setup before it and return-register reads
        // after it.
        let arg_copy = MachInst::new(AArch64Opcode::Copy, vec![MachOperand::PReg(X0), vreg(0)]);
        let target_copy = MachInst::new(AArch64Opcode::MovR, vec![MachOperand::PReg(X16), vreg(1)]);
        let call = MachInst::new(AArch64Opcode::Blr, vec![MachOperand::PReg(X16)]);
        let ret_copy = MachInst::new(AArch64Opcode::Copy, vec![vreg(2), MachOperand::PReg(X0)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![arg_copy, target_copy, call, ret_copy, ret]);

        let mut sched = InstructionScheduler;
        sched.run(&mut func);

        let order = &func.block(func.entry).insts;
        let pos_arg = order.iter().position(|&id| id == InstId(0)).unwrap();
        let pos_target = order.iter().position(|&id| id == InstId(1)).unwrap();
        let pos_call = order.iter().position(|&id| id == InstId(2)).unwrap();
        let pos_ret_copy = order.iter().position(|&id| id == InstId(3)).unwrap();

        assert!(pos_arg < pos_call, "argument copy must stay before BLR");
        assert!(pos_target < pos_call, "target copy must stay before BLR");
        assert!(pos_call < pos_ret_copy, "return copy must stay after BLR");
    }

    #[test]
    fn test_call_opcode_clobber_keeps_return_read_before_next_arg_write() {
        static CALL_USES: &[PReg] = &[X0, X16];

        let arg_copy = MachInst::new(AArch64Opcode::Copy, vec![MachOperand::PReg(X0), vreg(0)]);
        let target_copy = MachInst::new(AArch64Opcode::MovR, vec![MachOperand::PReg(X16), vreg(1)]);
        let call = MachInst::new(AArch64Opcode::Blr, vec![MachOperand::PReg(X16)])
            .with_implicit_uses(CALL_USES);
        let ret_copy = MachInst::new(AArch64Opcode::Copy, vec![vreg(2), MachOperand::PReg(X0)]);
        let next_arg_copy =
            MachInst::new(AArch64Opcode::Copy, vec![MachOperand::PReg(X0), vreg(3)]);
        let next_target_copy =
            MachInst::new(AArch64Opcode::MovR, vec![MachOperand::PReg(X16), vreg(4)]);
        let next_call = MachInst::new(AArch64Opcode::Blr, vec![MachOperand::PReg(X16)])
            .with_implicit_uses(CALL_USES);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let func = make_func_with_insts(vec![
            arg_copy,
            target_copy,
            call,
            ret_copy,
            next_arg_copy,
            next_target_copy,
            next_call,
            ret,
        ]);

        let mut dag = build_dag(&func, func.entry);
        assert!(
            dag.nodes[3].deps.contains(&2),
            "post-call X0 read must depend on the call's implicit X0 clobber"
        );
        assert!(
            dag.nodes[4].deps.contains(&3),
            "next X0 argument write must stay after the prior return X0 read"
        );

        let order = schedule_list(&mut dag);
        assert!(pos(InstId(2), &order) < pos(InstId(3), &order));
        assert!(pos(InstId(3), &order) < pos(InstId(4), &order));
    }

    #[test]
    fn test_pressure_aware_call_opcode_clobber_keeps_return_before_next_arg() {
        static CALL_USES: &[PReg] = &[X0, X16];

        let arg_copy = MachInst::new(AArch64Opcode::Copy, vec![MachOperand::PReg(X0), vreg(0)]);
        let target_copy = MachInst::new(AArch64Opcode::MovR, vec![MachOperand::PReg(X16), vreg(1)]);
        let call = MachInst::new(AArch64Opcode::Blr, vec![MachOperand::PReg(X16)])
            .with_implicit_uses(CALL_USES);
        let ret_copy = MachInst::new(AArch64Opcode::Copy, vec![vreg(2), MachOperand::PReg(X0)]);
        let next_arg_copy =
            MachInst::new(AArch64Opcode::Copy, vec![MachOperand::PReg(X0), vreg(3)]);
        let next_call = MachInst::new(AArch64Opcode::Blr, vec![MachOperand::PReg(X16)])
            .with_implicit_uses(CALL_USES);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![
            arg_copy,
            target_copy,
            call,
            ret_copy,
            next_arg_copy,
            next_call,
            ret,
        ]);

        let mut sched = PressureAwareScheduler;
        sched.run(&mut func);

        let order = &func.block(func.entry).insts;
        assert!(pos(InstId(2), order) < pos(InstId(3), order));
        assert!(pos(InstId(3), order) < pos(InstId(4), order));
    }

    #[test]
    fn test_opcode_effect_barrier_preserves_original_sides_without_call_flag() {
        let before = MachInst::new(AArch64Opcode::MovI, vec![vreg(20), imm(1)]);
        let barrier = MachInst::with_flags(
            AArch64Opcode::Blr,
            vec![MachOperand::PReg(X16)],
            InstFlags::EMPTY,
        );
        let after1 = MachInst::new(AArch64Opcode::AddRR, vec![vreg(21), vreg(10), vreg(11)]);
        let after2 = MachInst::new(AArch64Opcode::AddRR, vec![vreg(22), vreg(21), vreg(12)]);
        let after3 = MachInst::new(AArch64Opcode::AddRR, vec![vreg(23), vreg(22), vreg(13)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);

        let mut func = make_func_with_insts(vec![before, barrier, after1, after2, after3, ret]);
        let mut sched = InstructionScheduler;
        sched.run(&mut func);

        let order = &func.block(func.entry).insts;
        assert!(pos(InstId(0), order) < pos(InstId(1), order));
        assert!(pos(InstId(1), order) < pos(InstId(2), order));
    }

    #[test]
    fn test_opcode_effect_barrier_preserves_original_sides_pressure_aware() {
        let before = MachInst::new(AArch64Opcode::MovI, vec![vreg(20), imm(1)]);
        let barrier = MachInst::with_flags(
            AArch64Opcode::Blr,
            vec![MachOperand::PReg(X16)],
            InstFlags::EMPTY,
        );
        let after1 = MachInst::new(AArch64Opcode::AddRR, vec![vreg(21), vreg(10), vreg(11)]);
        let after2 = MachInst::new(AArch64Opcode::AddRR, vec![vreg(22), vreg(21), vreg(12)]);
        let after3 = MachInst::new(AArch64Opcode::AddRR, vec![vreg(23), vreg(22), vreg(13)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);

        let mut func = make_func_with_insts(vec![before, barrier, after1, after2, after3, ret]);
        let mut sched = PressureAwareScheduler;
        sched.run(&mut func);

        let order = &func.block(func.entry).insts;
        assert!(pos(InstId(0), order) < pos(InstId(1), order));
        assert!(pos(InstId(1), order) < pos(InstId(2), order));
    }

    #[test]
    fn test_internal_return_fences_later_load() {
        let mov = MachInst::new(AArch64Opcode::MovI, vec![vreg(0), imm(1)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let load = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(1), vreg(2), imm(0)]);
        let mut func = make_func_with_insts(vec![mov, ret, load]);

        let mut sched = InstructionScheduler;
        sched.run(&mut func);

        let order = &func.block(func.entry).insts;
        assert!(
            pos(InstId(1), order) < pos(InstId(2), order),
            "internal return must fence later potentially-faulting load"
        );
    }

    #[test]
    fn test_internal_return_fences_later_load_pressure_aware() {
        let mov = MachInst::new(AArch64Opcode::MovI, vec![vreg(0), imm(1)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let load = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(1), vreg(2), imm(0)]);
        let mut func = make_func_with_insts(vec![mov, ret, load]);

        let mut sched = PressureAwareScheduler;
        sched.run(&mut func);

        let order = &func.block(func.entry).insts;
        assert!(
            pos(InstId(1), order) < pos(InstId(2), order),
            "pressure-aware scheduler must keep unreachable load after return"
        );
    }

    #[test]
    fn test_trap_null_if_zero_fences_later_load() {
        let guard = MachInst::new(AArch64Opcode::TrapNullIfZero, vec![vreg(2)]);
        let load = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(1), vreg(2), imm(0)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![guard, load, ret]);

        let mut sched = InstructionScheduler;
        sched.run(&mut func);

        let order = &func.block(func.entry).insts;
        assert!(
            pos(InstId(0), order) < pos(InstId(1), order),
            "not-null guard must fence the protected load"
        );
    }

    #[test]
    fn test_trap_null_if_zero_fences_later_load_pressure_aware() {
        let guard = MachInst::new(AArch64Opcode::TrapNullIfZero, vec![vreg(2)]);
        let load = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(1), vreg(2), imm(0)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![guard, load, ret]);

        let mut sched = PressureAwareScheduler;
        sched.run(&mut func);

        let order = &func.block(func.entry).insts;
        assert!(
            pos(InstId(0), order) < pos(InstId(1), order),
            "pressure-aware scheduler must keep protected load after not-null guard"
        );
    }

    #[test]
    fn test_internal_branch_fences_fallthrough_side_effects_pressure_aware() {
        let cond = MachInst::new(
            AArch64Opcode::Cbz,
            vec![vreg(0), MachOperand::Block(BlockId(1))],
        );
        let store = MachInst::new(AArch64Opcode::StrRI, vec![vreg(1), vreg(2), imm(0)]);
        let call = MachInst::new(AArch64Opcode::Blr, vec![MachOperand::PReg(X16)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![cond, store, call, ret]);
        let target = func.create_block();
        assert_eq!(target, BlockId(1));
        let target_ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(target, target_ret);
        let block_count = func.num_blocks();
        let block_order = func.block_order.clone();

        let mut sched = PressureAwareScheduler;
        sched.run(&mut func);

        assert_eq!(func.num_blocks(), block_count);
        assert_eq!(func.block_order, block_order);
        let order = &func.block(func.entry).insts;
        assert!(
            pos(InstId(0), order) < pos(InstId(1), order),
            "guarding branch must stay before fallthrough store"
        );
        assert!(
            pos(InstId(0), order) < pos(InstId(2), order),
            "guarding branch must stay before fallthrough call"
        );
    }

    #[test]
    fn test_internal_branch_fences_fallthrough_side_effects() {
        let cond = MachInst::new(
            AArch64Opcode::Cbz,
            vec![vreg(0), MachOperand::Block(BlockId(1))],
        );
        let store = MachInst::new(AArch64Opcode::StrRI, vec![vreg(1), vreg(2), imm(0)]);
        let call = MachInst::new(AArch64Opcode::Blr, vec![MachOperand::PReg(X16)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![cond, store, call, ret]);
        let target = func.create_block();
        assert_eq!(target, BlockId(1));
        let target_ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(target, target_ret);
        let block_count = func.num_blocks();
        let block_order = func.block_order.clone();

        let mut sched = InstructionScheduler;
        sched.run(&mut func);

        assert_eq!(func.num_blocks(), block_count);
        assert_eq!(func.block_order, block_order);
        let order = &func.block(func.entry).insts;
        assert!(
            pos(InstId(0), order) < pos(InstId(1), order),
            "guarding branch must stay before fallthrough store"
        );
        assert!(
            pos(InstId(0), order) < pos(InstId(2), order),
            "guarding branch must stay before fallthrough call"
        );
    }

    #[test]
    fn test_build_dag_preg_implicit_use_war_xw_alias() {
        static READS_W0: &[PReg] = &[W0];

        let read_w0 = MachInst::new(AArch64Opcode::Copy, vec![vreg(10), MachOperand::PReg(X1)])
            .with_implicit_uses(READS_W0);
        let write_x0 = MachInst::new(AArch64Opcode::Copy, vec![MachOperand::PReg(X0), vreg(2)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let func = make_func_with_insts(vec![read_w0, write_x0, ret]);

        let mut dag = build_dag(&func, func.entry);
        assert!(
            dag.nodes[1].deps.contains(&0),
            "explicit X0 def must stay after prior implicit W0 use"
        );

        let order = schedule_list(&mut dag);
        assert!(
            pos(InstId(0), &order) < pos(InstId(1), &order),
            "scheduler must preserve implicit-use WAR across X/W aliases"
        );
    }

    #[test]
    fn test_build_dag_preg_raw_waw_for_call_like_copies() {
        static CALL_USES: &[PReg] = &[X0, X16];
        static CALL_DEFS: &[PReg] = &[X0];

        let arg_copy = MachInst::new(AArch64Opcode::Copy, vec![MachOperand::PReg(X0), vreg(0)]);
        let target_copy = MachInst::new(AArch64Opcode::Copy, vec![MachOperand::PReg(X16), vreg(1)]);
        let call_like =
            MachInst::with_flags(AArch64Opcode::Nop, vec![], InstFlags::HAS_SIDE_EFFECTS)
                .with_implicit_uses(CALL_USES)
                .with_implicit_defs(CALL_DEFS);
        let ret_copy = MachInst::new(AArch64Opcode::Copy, vec![vreg(2), MachOperand::PReg(X0)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let func = make_func_with_insts(vec![arg_copy, target_copy, call_like, ret_copy, ret]);

        let mut dag = build_dag(&func, func.entry);
        assert!(
            dag.nodes[2].deps.contains(&0),
            "call-like implicit X0 use/def must depend on explicit argument X0 def"
        );
        assert!(
            dag.nodes[2].deps.contains(&1),
            "call-like implicit X16 use must depend on explicit target X16 def"
        );
        assert!(
            dag.nodes[3].deps.contains(&2),
            "post-call explicit X0 read must depend on call-like implicit X0 def"
        );

        let order = schedule_list(&mut dag);
        assert!(pos(InstId(0), &order) < pos(InstId(2), &order));
        assert!(pos(InstId(1), &order) < pos(InstId(2), &order));
        assert!(pos(InstId(2), &order) < pos(InstId(3), &order));
    }

    #[test]
    fn test_pressure_aware_scheduler_preserves_implicit_use_war_xw_alias() {
        static READS_W0: &[PReg] = &[W0];

        let read_w0 = MachInst::new(AArch64Opcode::Copy, vec![vreg(10), MachOperand::PReg(X1)])
            .with_implicit_uses(READS_W0);
        let write_x0 = MachInst::new(AArch64Opcode::Copy, vec![MachOperand::PReg(X0), vreg(2)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![read_w0, write_x0, ret]);

        let _ = schedule_function_pressure_aware(&mut func);
        let order = &func.block(func.entry).insts;
        assert!(
            pos(InstId(0), order) < pos(InstId(1), order),
            "pressure-aware scheduler must preserve implicit-use WAR across X/W aliases"
        );
    }

    #[test]
    fn test_build_dag_preg_livein_read_orders_later_vreg_defs() {
        let read_x0 = MachInst::new(AArch64Opcode::Copy, vec![vreg(10), MachOperand::PReg(X0)]);
        let mul = MachInst::new(AArch64Opcode::MulRR, vec![vreg(11), vreg(1), vreg(2)]);
        let use_mul = MachInst::new(AArch64Opcode::AddRI, vec![vreg(12), vreg(11), imm(1)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let func = make_func_with_insts(vec![read_x0, mul, use_mul, ret]);

        let mut dag = build_dag(&func, func.entry);
        assert!(
            dag.nodes[1].deps.contains(&0),
            "entry X0 read must stay before later VReg defs that may allocate to X0"
        );

        let order = schedule_list(&mut dag);
        assert!(
            pos(InstId(0), &order) < pos(InstId(1), &order),
            "scheduler must not delay fixed live-in reads past virtual defs"
        );
    }

    #[test]
    fn test_build_dag_preg_write_orders_after_prior_vreg_uses() {
        let prior_use = MachInst::new(AArch64Opcode::AddRR, vec![vreg(10), vreg(1), vreg(2)]);
        let write_x0 = MachInst::new(AArch64Opcode::Copy, vec![MachOperand::PReg(X0), vreg(3)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let func = make_func_with_insts(vec![prior_use, write_x0, ret]);

        let mut dag = build_dag(&func, func.entry);
        assert!(
            dag.nodes[1].deps.contains(&0),
            "fixed X0 writes must stay after earlier VReg uses that may allocate to X0"
        );

        let order = schedule_list(&mut dag);
        assert!(
            pos(InstId(0), &order) < pos(InstId(1), &order),
            "scheduler must not move fixed PReg writes before prior virtual uses"
        );
    }

    #[test]
    fn test_build_dag_preg_write_orders_after_prior_vreg_defs() {
        let prior_def = MachInst::new(AArch64Opcode::MovI, vec![vreg(10), imm(7)]);
        let write_x0 = MachInst::new(AArch64Opcode::Copy, vec![MachOperand::PReg(X0), vreg(3)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let func = make_func_with_insts(vec![prior_def, write_x0, ret]);

        let mut dag = build_dag(&func, func.entry);
        assert!(
            dag.nodes[1].deps.contains(&0),
            "fixed X0 writes must stay after earlier VReg defs that may allocate to X0"
        );

        let order = schedule_list(&mut dag);
        assert!(
            pos(InstId(0), &order) < pos(InstId(1), &order),
            "scheduler must not delay virtual defs past fixed PReg writes"
        );
    }

    #[test]
    fn test_store_store_ordering_preserved() {
        // str v0, [v1, #0]    (inst0)
        // str v2, [v3, #8]    (inst1, must come after inst0)
        // ret                  (inst2)
        let store1 = MachInst::new(AArch64Opcode::StrRI, vec![vreg(0), vreg(1), imm(0)]);
        let store2 = MachInst::new(AArch64Opcode::StrRI, vec![vreg(2), vreg(3), imm(8)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![store1, store2, ret]);

        let mut sched = InstructionScheduler;
        sched.run(&mut func);

        let block = func.block(func.entry);
        let order: Vec<InstId> = block.insts.clone();

        let pos_s1 = order.iter().position(|&id| id == InstId(0)).unwrap();
        let pos_s2 = order.iter().position(|&id| id == InstId(1)).unwrap();
        assert!(pos_s1 < pos_s2, "store-store ordering must be preserved");
    }

    #[test]
    fn test_load_load_ordering_preserved() {
        // Two independent loads are kept in original order until the scheduler
        // has a precise alias/effect model for generated JIT code.
        // v1 = ldr [v0, #0]    (inst0, 4 cycles)
        // v3 = ldr [v2, #8]    (inst1, 4 cycles)
        // v4 = add v1, v3      (inst2, uses both)
        // ret                   (inst3)
        let load1 = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(1), vreg(0), imm(0)]);
        let load2 = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(3), vreg(2), imm(8)]);
        let add = MachInst::new(AArch64Opcode::AddRR, vec![vreg(4), vreg(1), vreg(3)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let func = make_func_with_insts(vec![load1, load2, add, ret]);

        // Build DAG and verify memory ordering adds a dependency between loads.
        let dag = build_dag(&func, func.entry);

        assert!(
            dag.nodes[0].rev_deps.contains(&1) && dag.nodes[1].deps.contains(&0),
            "load2 should depend on load1 through conservative memory ordering"
        );
    }

    #[test]
    fn test_ldpri_second_def_orders_later_user() {
        let ldp = MachInst::with_flags(
            AArch64Opcode::LdpRI,
            vec![vreg(1), vreg(2), vreg(0), imm(0)],
            InstFlags::READS_MEMORY | InstFlags::PROOF_REORDERABLE,
        );
        let use_second = MachInst::new(AArch64Opcode::AddRI, vec![vreg(3), vreg(2), imm(1)]);
        let use_first = MachInst::new(AArch64Opcode::AddRI, vec![vreg(4), vreg(1), imm(1)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let func = make_func_with_insts(vec![ldp, use_second, use_first, ret]);

        let mut dag = build_dag(&func, func.entry);
        assert!(
            dag.nodes[1].deps.contains(&0),
            "user of LdpRI operand 1 must depend on the pair load"
        );
        assert!(
            dag.nodes[2].deps.contains(&0),
            "user of LdpRI operand 0 must depend on the pair load"
        );

        let order = schedule_list(&mut dag);
        assert!(pos(InstId(0), &order) < pos(InstId(1), &order));
        assert!(pos(InstId(0), &order) < pos(InstId(2), &order));
    }

    #[test]
    fn test_ldpri_counts_two_gpr_defs_for_pressure() {
        let ldp = MachInst::with_flags(
            AArch64Opcode::LdpRI,
            vec![vreg(1), vreg(2), vreg(0), imm(0)],
            InstFlags::READS_MEMORY | InstFlags::PROOF_REORDERABLE,
        );
        let use_both = MachInst::new(AArch64Opcode::AddRR, vec![vreg(3), vreg(1), vreg(2)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let func = make_func_with_insts(vec![ldp, use_both, ret]);

        let dag = build_dag(&func, func.entry);
        let infos = compute_pressure_info(&func, &dag);

        assert_eq!(
            infos[0].defs,
            vec![VReg::new(1, RegClass::Gpr64), VReg::new(2, RegClass::Gpr64)]
        );
        assert_eq!(infos[0].kills, 1);
        assert_eq!(infos[0].net_pressure, 1);

        let pressure =
            compute_register_pressure(&func, func.entry, func.block(func.entry).insts.as_slice());
        assert!(pressure.max_gpr_pressure >= 2);
    }

    #[test]
    fn atomic_lse_def_use_ldpri_preg_second_def_raw_edge() {
        let ldp = MachInst::new(
            AArch64Opcode::LdpRI,
            vec![
                MachOperand::PReg(X0),
                MachOperand::PReg(X1),
                MachOperand::PReg(X2),
                imm(0),
            ],
        );
        let read_x1 = MachInst::new(AArch64Opcode::Copy, vec![vreg(1), MachOperand::PReg(X1)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let func = make_func_with_insts(vec![ldp, read_x1, ret]);

        let accesses = collect_preg_accesses(func.inst(InstId(0)));
        assert_eq!(accesses.writes, vec![X0, X1]);
        assert_eq!(accesses.reads, vec![X2]);

        let dag = build_dag(&func, func.entry);
        assert_dag_edge(
            &dag,
            0,
            1,
            "fixed PReg reader of LdpRI operand 1 must depend on the pair load",
        );
    }

    #[test]
    fn atomic_lse_def_use_ldpri_preg_second_def_war_edge() {
        let read_x1 = MachInst::new(AArch64Opcode::Copy, vec![vreg(1), MachOperand::PReg(X1)]);
        let ldp = MachInst::new(
            AArch64Opcode::LdpRI,
            vec![
                MachOperand::PReg(X0),
                MachOperand::PReg(X1),
                MachOperand::PReg(X2),
                imm(0),
            ],
        );
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let func = make_func_with_insts(vec![read_x1, ldp, ret]);

        let dag = build_dag(&func, func.entry);
        assert_dag_edge(
            &dag,
            0,
            1,
            "fixed PReg read of X1 must stay before a later LdpRI write to X1",
        );
    }

    #[test]
    fn atomic_lse_def_use_scheduler_roles_and_memory_edges() {
        let src = MachInst::new(AArch64Opcode::MovI, vec![vreg(10), imm(7)]);
        let addr = MachInst::new(AArch64Opcode::MovI, vec![vreg(12), imm(0x1000)]);
        let rmw = MachInst::with_flags(
            AArch64Opcode::Ldadd,
            vec![vreg(10), vreg(11), vreg(12)],
            AArch64Opcode::Ldadd.default_flags() | InstFlags::PROOF_REORDERABLE,
        );
        let use_rmw_result = MachInst::new(AArch64Opcode::AddRI, vec![vreg(13), vreg(11), imm(1)]);
        let expected = MachInst::new(AArch64Opcode::MovI, vec![vreg(20), imm(1)]);
        let desired = MachInst::new(AArch64Opcode::MovI, vec![vreg(21), imm(2)]);
        let cas_addr = MachInst::new(AArch64Opcode::MovI, vec![vreg(22), imm(0x2000)]);
        let cas = MachInst::new(AArch64Opcode::Cas, vec![vreg(20), vreg(21), vreg(22)]);
        let use_cas_result = MachInst::new(AArch64Opcode::AddRI, vec![vreg(23), vreg(20), imm(1)]);
        let load = proof_reorderable_load(30, 31, 0);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let func = make_func_with_insts(vec![
            src,
            addr,
            rmw,
            use_rmw_result,
            expected,
            desired,
            cas_addr,
            cas,
            use_cas_result,
            load,
            ret,
        ]);

        let rmw_inst = func.inst(InstId(2));
        assert_eq!(
            explicit_vreg_defs(rmw_inst),
            vec![VReg::new(11, RegClass::Gpr64)]
        );
        assert_eq!(
            explicit_vreg_uses(rmw_inst),
            vec![
                VReg::new(10, RegClass::Gpr64),
                VReg::new(12, RegClass::Gpr64)
            ]
        );

        let cas_inst = func.inst(InstId(7));
        assert_eq!(
            explicit_vreg_defs(cas_inst),
            vec![VReg::new(20, RegClass::Gpr64)]
        );
        assert_eq!(
            explicit_vreg_uses(cas_inst),
            vec![
                VReg::new(20, RegClass::Gpr64),
                VReg::new(21, RegClass::Gpr64),
                VReg::new(22, RegClass::Gpr64),
            ]
        );

        let rmw_preg = MachInst::new(
            AArch64Opcode::Ldadd,
            vec![
                MachOperand::PReg(X0),
                MachOperand::PReg(X1),
                MachOperand::PReg(X2),
            ],
        );
        let rmw_accesses = collect_preg_accesses(&rmw_preg);
        assert_eq!(rmw_accesses.writes, vec![X1]);
        assert_eq!(rmw_accesses.reads, vec![X0, X2]);

        let cas_preg = MachInst::new(
            AArch64Opcode::Cas,
            vec![
                MachOperand::PReg(X0),
                MachOperand::PReg(X1),
                MachOperand::PReg(X2),
            ],
        );
        let cas_accesses = collect_preg_accesses(&cas_preg);
        assert_eq!(cas_accesses.writes, vec![X0]);
        assert_eq!(cas_accesses.reads, vec![X0, X1, X2]);

        let dag = build_dag(&func, func.entry);
        assert_dag_edge(&dag, 0, 2, "Ldadd must read operand 0");
        assert_dag_edge(&dag, 1, 2, "Ldadd must read operand 2");
        assert_dag_edge(&dag, 2, 3, "Ldadd must define operand 1");
        assert_dag_edge(&dag, 4, 7, "Cas must read tied operand 0");
        assert_dag_edge(&dag, 5, 7, "Cas must read operand 1");
        assert_dag_edge(&dag, 6, 7, "Cas must read operand 2");
        assert_dag_edge(&dag, 7, 8, "Cas must define tied operand 0");
        assert_dag_edge(
            &dag,
            2,
            9,
            "PROOF_REORDERABLE LSE atomics must remain memory-conservative",
        );

        let infos = compute_pressure_info(&func, &dag);
        assert_eq!(infos[2].defs, vec![VReg::new(11, RegClass::Gpr64)]);
        assert_eq!(
            infos[2].uses,
            vec![
                VReg::new(10, RegClass::Gpr64),
                VReg::new(12, RegClass::Gpr64)
            ]
        );
        assert_eq!(infos[7].defs, vec![VReg::new(20, RegClass::Gpr64)]);
        assert_eq!(
            infos[7].uses,
            vec![
                VReg::new(20, RegClass::Gpr64),
                VReg::new(21, RegClass::Gpr64),
                VReg::new(22, RegClass::Gpr64)
            ]
        );
    }

    #[test]
    fn test_proven_reorderable_load_load_skips_memory_spine_edge() {
        // Two independent proven loads can omit the conservative load-load
        // memory spine edge. Data, control, store, call, and barrier edges are
        // still modeled elsewhere.
        let load1 = proof_reorderable_load(1, 0, 0);
        let load2 = proof_reorderable_load(3, 2, 8);
        let add = MachInst::new(AArch64Opcode::AddRR, vec![vreg(4), vreg(1), vreg(3)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let func = make_func_with_insts(vec![load1, load2, add, ret]);

        let dag = build_dag(&func, func.entry);

        assert!(
            !dag.nodes[0].rev_deps.contains(&1) && !dag.nodes[1].deps.contains(&0),
            "proven load2 should not depend on proven load1 through memory ordering"
        );
    }

    #[test]
    fn test_proven_reorderable_disjoint_store_load_skips_memory_edge() {
        // ValidBorrow lets the scheduler use the existing non-aliased
        // store-load proof model only when the ordinary StrRI/LdrRI byte
        // ranges are statically known and disjoint.
        let store = proof_reorderable_store(10, 0, 0);
        let load = proof_reorderable_load(1, 0, 8);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let func = make_func_with_insts(vec![store, load, ret]);

        let dag = build_dag(&func, func.entry);

        assert_no_dag_edge(
            &dag,
            0,
            1,
            "disjoint proven StrRI/LdrRI should not have a memory edge",
        );
    }

    #[test]
    fn test_proven_reorderable_disjoint_store_load_can_schedule_load_first() {
        let store = proof_reorderable_store(10, 0, 0);
        let load = proof_reorderable_load(1, 0, 8);
        let use_load = MachInst::new(AArch64Opcode::AddRI, vec![vreg(2), vreg(1), imm(1)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![store, load, use_load, ret]);

        let mut sched = InstructionScheduler;
        sched.run(&mut func);

        let order = &func.block(func.entry).insts;
        assert!(
            pos(InstId(1), order) < pos(InstId(0), order),
            "disjoint proven load should be able to move before the prior store"
        );
    }

    #[test]
    fn test_proven_reorderable_store_load_keeps_edge_for_conservative_cases() {
        let cases: Vec<(&str, MachInst, MachInst)> = vec![
            (
                "overlapping byte ranges",
                proof_reorderable_store(10, 0, 0),
                proof_reorderable_load(1, 0, 4),
            ),
            (
                "different static bases are not a disjoint-range proof",
                proof_reorderable_store(10, 0, 0),
                proof_reorderable_load(1, 2, 8),
            ),
            (
                "unknown store offset",
                proof_reorderable_inst(AArch64Opcode::StrRI, vec![vreg(10), vreg(0), vreg(12)]),
                proof_reorderable_load(1, 0, 8),
            ),
            (
                "unknown store size",
                proof_reorderable_inst(AArch64Opcode::StrRI, vec![imm(7), vreg(0), imm(0)]),
                proof_reorderable_load(1, 0, 8),
            ),
            (
                "unproved store",
                MachInst::new(AArch64Opcode::StrRI, vec![vreg(10), vreg(0), imm(0)]),
                proof_reorderable_load(1, 0, 8),
            ),
            (
                "unproved load",
                proof_reorderable_store(10, 0, 0),
                MachInst::new(AArch64Opcode::LdrRI, vec![vreg(1), vreg(0), imm(8)]),
            ),
            (
                "atomic store",
                proof_reorderable_inst(AArch64Opcode::Stlr, vec![vreg(10), vreg(0)]),
                proof_reorderable_load(1, 0, 8),
            ),
            (
                "writeback store",
                proof_reorderable_inst(
                    AArch64Opcode::StpPreIndex,
                    vec![vreg(10), vreg(11), vreg(0), imm(0)],
                ),
                proof_reorderable_load(1, 0, 16),
            ),
        ];

        for (context, store, load) in cases {
            let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
            let func = make_func_with_insts(vec![store, load, ret]);
            let dag = build_dag(&func, func.entry);

            assert_dag_edge(&dag, 0, 1, context);
        }
    }

    #[test]
    fn test_proven_reorderable_store_load_keeps_call_barrier() {
        let store = proof_reorderable_store(10, 0, 0);
        let call = MachInst::new(AArch64Opcode::Bl, vec![MachOperand::Imm(0)]);
        let load = proof_reorderable_load(1, 0, 8);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let func = make_func_with_insts(vec![store, call, load, ret]);

        let dag = build_dag(&func, func.entry);

        assert_dag_edge(&dag, 0, 1, "store must stay before following call");
        assert_dag_edge(&dag, 1, 2, "load must stay after preceding call");
    }

    #[test]
    fn test_proven_reorderable_load_fenced_by_following_ordered_memory_ops() {
        for (context, follower) in [
            (
                "following store",
                MachInst::new(AArch64Opcode::StrRI, vec![vreg(3), vreg(2), imm(0)]),
            ),
            (
                "following call",
                MachInst::new(AArch64Opcode::Bl, vec![MachOperand::Imm(0)]),
            ),
            (
                "following barrier",
                MachInst::with_flags(AArch64Opcode::Dmb, vec![imm(0)], InstFlags::EMPTY),
            ),
            (
                "following unproven load",
                MachInst::new(AArch64Opcode::LdrRI, vec![vreg(3), vreg(2), imm(0)]),
            ),
        ] {
            let load = proof_reorderable_load(1, 0, 0);
            let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
            let func = make_func_with_insts(vec![load, follower, ret]);
            let dag = build_dag(&func, func.entry);

            assert_dag_edge(&dag, 0, 1, context);
        }
    }

    #[test]
    fn test_proven_reorderable_loads_overlap_latency() {
        // Without a load-load memory edge, the second proven load can issue
        // while the first load's 4-cycle result latency is still outstanding.
        let load1 = proof_reorderable_load(1, 0, 0);
        let load2 = proof_reorderable_load(3, 2, 8);
        let add1 = MachInst::new(AArch64Opcode::AddRI, vec![vreg(4), vreg(1), imm(1)]);
        let add2 = MachInst::new(AArch64Opcode::AddRI, vec![vreg(5), vreg(3), imm(1)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let func = make_func_with_insts(vec![load1, load2, add1, add2, ret]);

        let mut dag = build_dag(&func, func.entry);
        let _order = schedule_list(&mut dag);

        assert_eq!(dag.nodes[0].earliest_start, 0);
        assert!(
            dag.nodes[1].earliest_start < dag.nodes[0].latency,
            "second proven load should overlap first load latency: start={} latency={}",
            dag.nodes[1].earliest_start,
            dag.nodes[0].latency
        );
    }

    // ---- Terminator tests ----

    #[test]
    fn test_terminator_stays_last() {
        // v0 = mov #42         (inst0)
        // v1 = mul v2, v3      (inst1, 3 cycles)
        // b.cond <target>      (inst2, terminator — must be last)
        let mov = MachInst::new(AArch64Opcode::MovI, vec![vreg(0), imm(42)]);
        let mul = MachInst::new(AArch64Opcode::MulRR, vec![vreg(1), vreg(2), vreg(3)]);
        let branch = MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(trust_cg_ir::BlockId(1))],
        );
        let mut func = make_func_with_insts(vec![mov, mul, branch]);
        // Need a second block for the branch target.
        let _bb1 = func.create_block();

        let mut sched = InstructionScheduler;
        sched.run(&mut func);

        let block = func.block(func.entry);
        let order: Vec<InstId> = block.insts.clone();

        // Branch must be last.
        assert_eq!(
            *order.last().unwrap(),
            InstId(2),
            "branch terminator must remain last"
        );
    }

    // ---- Latency hiding test ----

    #[test]
    fn test_latency_model_produces_better_schedule() {
        // Input order (suboptimal):
        //   v1 = ldr [v0, #0]     (inst0, 4 cycles)
        //   v2 = add v1, #1       (inst1, depends on inst0)
        //   v3 = mov #99          (inst2, independent)
        //   ret                    (inst3)
        //
        // Optimal schedule: ldr, mov, add, ret
        // The mov can execute during the load's latency.
        let load = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(1), vreg(0), imm(0)]);
        let add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(2), vreg(1), imm(1)]);
        let mov = MachInst::new(AArch64Opcode::MovI, vec![vreg(3), imm(99)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![load, add, mov, ret]);

        let mut sched = InstructionScheduler;
        sched.run(&mut func);

        let block = func.block(func.entry);
        let order: Vec<InstId> = block.insts.clone();

        // Load should be first (highest critical path: 4 + 1 = 5).
        assert_eq!(order[0], InstId(0), "load should be first");

        // Mov (InstId(2)) should be scheduled before add (InstId(1))
        // because add can't start until cycle 4 (waiting on load).
        let pos_mov = order.iter().position(|&id| id == InstId(2)).unwrap();
        let pos_add = order.iter().position(|&id| id == InstId(1)).unwrap();
        assert!(
            pos_mov < pos_add,
            "mov should be scheduled during load latency, before add"
        );

        // Ret must be last.
        assert_eq!(*order.last().unwrap(), InstId(3));
    }

    // ---- DAG construction test ----

    #[test]
    fn test_build_dag_data_deps() {
        // v1 = add v0, #1     (node 0, def v1)
        // v2 = sub v1, #2     (node 1, uses v1 -> dep on node 0)
        // ret                  (node 2)
        let add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(1), vreg(0), imm(1)]);
        let sub = MachInst::new(AArch64Opcode::SubRI, vec![vreg(2), vreg(1), imm(2)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let func = make_func_with_insts(vec![add, sub, ret]);

        let dag = build_dag(&func, func.entry);

        assert_eq!(dag.nodes.len(), 3);
        // Node 1 depends on node 0 (data: v1).
        assert!(dag.nodes[1].deps.contains(&0));
        // Node 0 has node 1 as reverse dep.
        assert!(dag.nodes[0].rev_deps.contains(&1));
    }

    #[test]
    fn test_build_dag_vreg_edges_are_class_exact() {
        // Same numeric id in different register classes must not create false
        // scheduler dependencies. The GPR use of v1 reads from outside the
        // block even though node 0 defines FPR v1.
        let fpr_def = MachInst::new(
            AArch64Opcode::FaddRR,
            vec![
                typed_vreg(1, RegClass::Fpr64),
                typed_vreg(20, RegClass::Fpr64),
                typed_vreg(21, RegClass::Fpr64),
            ],
        );
        let gpr_external_use = MachInst::new(AArch64Opcode::AddRI, vec![vreg(4), vreg(1), imm(1)]);
        let gpr_def = MachInst::new(AArch64Opcode::MovI, vec![vreg(1), imm(7)]);
        let gpr_use = MachInst::new(AArch64Opcode::AddRI, vec![vreg(5), vreg(1), imm(1)]);
        let func = make_func_with_insts(vec![fpr_def, gpr_external_use, gpr_def, gpr_use]);

        let dag = build_dag(&func, func.entry);

        assert_no_dag_edge(&dag, 0, 1, "FPR v1 definition must not feed a GPR v1 use");
        assert_no_dag_edge(
            &dag,
            0,
            2,
            "FPR v1 definition must not WAW-chain with a GPR v1 definition",
        );
        assert_dag_edge(
            &dag,
            1,
            2,
            "external GPR v1 read must stay before a later GPR v1 definition",
        );
        assert_dag_edge(
            &dag,
            2,
            3,
            "same-class GPR v1 definition must feed the later GPR v1 use",
        );
    }

    /// Regression test for #382: the scheduler must treat MOVK's operand[0]
    /// as an implicit read (tied def-use) and emit a RAW edge from the
    /// prior def of that vreg to the MOVK. Without this, a MOVZ+MOVK chain
    /// looks like three independent defs of v1 (so only MOVZ has an outgoing
    /// RAW edge to readers) and the scheduler is free to place readers of
    /// v1 between the MOVZ and the trailing MOVK(s) — reading a partial
    /// constant.
    #[test]
    fn test_build_dag_movk_tied_def_use() {
        // v1 = movz #0x835a                 (node 0, first def of v1)
        // v1 = movk v1, #0xb9ea, lsl 16      (node 1, tied: reads prior v1)
        // v1 = movk v1, #0x82e2, lsl 32      (node 2, tied)
        // v1 = movk v1, #0x717c, lsl 48      (node 3, tied)
        // v3 = eor v2, v1                   (node 4, reads v1)
        // ret                                (node 5)
        //
        // Without the tied def-use edge, node 4 only has a RAW edge to
        // node 0 (the first def), so the scheduler can place node 4 before
        // nodes 1/2/3 and read the partial constant. This caused issue #382.
        let movz = MachInst::new(AArch64Opcode::Movz, vec![vreg(1), imm(0x835a), imm(0)]);
        let movk1 = MachInst::new(AArch64Opcode::Movk, vec![vreg(1), imm(0xb9ea), imm(16)]);
        let movk2 = MachInst::new(AArch64Opcode::Movk, vec![vreg(1), imm(0x82e2), imm(32)]);
        let movk3 = MachInst::new(AArch64Opcode::Movk, vec![vreg(1), imm(0x717c), imm(48)]);
        let eor = MachInst::new(AArch64Opcode::EorRR, vec![vreg(3), vreg(2), vreg(1)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let func = make_func_with_insts(vec![movz, movk1, movk2, movk3, eor, ret]);

        let dag = build_dag(&func, func.entry);
        assert_eq!(dag.nodes.len(), 6);

        // Each MOVK (nodes 1, 2, 3) must depend on its immediate predecessor
        // via the tied-def-use RAW edge (plus WAW chain ordering).
        assert!(
            dag.nodes[1].deps.contains(&0),
            "movk1 must have RAW edge from movz (tied def-use on v1)"
        );
        assert!(
            dag.nodes[2].deps.contains(&1),
            "movk2 must have RAW edge from movk1 (tied def-use on v1)"
        );
        assert!(
            dag.nodes[3].deps.contains(&2),
            "movk3 must have RAW edge from movk2 (tied def-use on v1)"
        );

        // The reader of v1 (eor at node 4) must depend on the LAST MOVK
        // (node 3), not just the initial MOVZ (node 0). This is the
        // essential fix for #382: without this edge, the reader could be
        // scheduled between nodes 0 and 3.
        assert!(
            dag.nodes[4].deps.contains(&3),
            "reader of v1 must depend on the LAST MOVK (node 3), not just MOVZ"
        );
    }

    /// Regression for #408: BFM has a tied def-use (preserves uncovered
    /// bits of Rd). The scheduler must add a RAW edge from the instruction
    /// that produced the prior Rd value to the BFM, otherwise the BFM can
    /// be scheduled past a setter and read the wrong "background" bits.
    #[test]
    fn test_build_dag_bfm_tied_def_use() {
        // v1 = movz #0x1111           (node 0, def of v1)
        // v1 = bfm  v1, v2, #0, #7    (node 1, tied: reads prior v1)
        // v3 = eor v4, v1             (node 2, reads v1)
        // ret                          (node 3)
        let movz = MachInst::new(AArch64Opcode::Movz, vec![vreg(1), imm(0x1111), imm(0)]);
        let bfm = MachInst::new(AArch64Opcode::Bfm, vec![vreg(1), vreg(2), imm(0), imm(7)]);
        let eor = MachInst::new(AArch64Opcode::EorRR, vec![vreg(3), vreg(4), vreg(1)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let func = make_func_with_insts(vec![movz, bfm, eor, ret]);

        let dag = build_dag(&func, func.entry);
        assert_eq!(dag.nodes.len(), 4);
        assert!(
            dag.nodes[1].deps.contains(&0),
            "bfm must have RAW edge from movz (tied def-use on v1) — #408"
        );
        assert!(
            dag.nodes[2].deps.contains(&1),
            "reader of v1 must depend on the BFM, not just the prior MOVZ"
        );
    }

    /// Regression for #409: ADC reads the carry flag implicitly. The
    /// scheduler must add an edge from the most recent flag writer to
    /// each ADC so that reordering ADC past the flag writer is disallowed.
    #[test]
    fn test_build_dag_adc_reads_flags() {
        // v10 = adds v0, v1    (node 0, flag writer)
        // v2  = adc  v4, v5    (node 1, reads carry)
        // v3  = mov  v6        (node 2, no flag dep — could have been
        //                        scheduled before adc if carry were free)
        // ret                   (node 3)
        let adds = MachInst::new(AArch64Opcode::AddsRR, vec![vreg(10), vreg(0), vreg(1)]);
        let adc = MachInst::new(AArch64Opcode::Adc, vec![vreg(2), vreg(4), vreg(5)]);
        let movv = MachInst::new(AArch64Opcode::MovR, vec![vreg(3), vreg(6)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let func = make_func_with_insts(vec![adds, adc, movv, ret]);

        let dag = build_dag(&func, func.entry);
        assert_eq!(dag.nodes.len(), 4);
        assert!(
            dag.nodes[1].deps.contains(&0),
            "adc must depend on prior flag writer (adds) — #409"
        );
    }

    /// Symmetry: SBC reads the borrow flag the same way ADC reads carry.
    #[test]
    fn test_build_dag_sbc_reads_flags() {
        let subs = MachInst::new(AArch64Opcode::SubsRR, vec![vreg(10), vreg(0), vreg(1)]);
        let sbc = MachInst::new(AArch64Opcode::Sbc, vec![vreg(2), vreg(4), vreg(5)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let func = make_func_with_insts(vec![subs, sbc, ret]);

        let dag = build_dag(&func, func.entry);
        assert!(
            dag.nodes[1].deps.contains(&0),
            "sbc must depend on prior flag writer (subs) — #409"
        );
    }

    #[test]
    fn test_build_dag_serializes_nzcv_reader_before_next_writer() {
        // cmp value, #0       (node 0, writes NZCV)
        // cset value_is_zero  (node 1, reads NZCV from node 0)
        // cmp status, #0      (node 2, writes NZCV)
        // cset status_ok      (node 3, reads NZCV from node 2)
        //
        // Node 2 must not move before node 1, otherwise node 1 reads the
        // status comparison flags instead of the value comparison flags.
        let cmp_value = MachInst::new(AArch64Opcode::CmpRR, vec![vreg(0), vreg(1)]);
        let cset_value = MachInst::new(AArch64Opcode::CSet, vec![vreg(2), imm(0)]);
        let cmp_status = MachInst::new(AArch64Opcode::CmpRR, vec![vreg(3), vreg(4)]);
        let cset_status = MachInst::new(AArch64Opcode::CSet, vec![vreg(5), imm(0)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let func = make_func_with_insts(vec![cmp_value, cset_value, cmp_status, cset_status, ret]);

        let dag = build_dag(&func, func.entry);

        assert!(
            dag.nodes[1].deps.contains(&0),
            "first CSet must depend on first CMP"
        );
        assert!(
            dag.nodes[2].deps.contains(&1),
            "second CMP must stay after the first CSet"
        );
        assert!(
            dag.nodes[3].deps.contains(&2),
            "second CSet must depend on second CMP"
        );
    }

    #[test]
    fn test_call_is_memory_barrier() {
        // v0 = ldr [v1, #0]   (inst0, load)
        // bl <func>            (inst1, call — barrier)
        // v2 = ldr [v3, #0]   (inst2, load after call)
        // ret                  (inst3)
        let load1 = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(0), vreg(1), imm(0)]);
        let call = MachInst::new(AArch64Opcode::Bl, vec![MachOperand::Imm(0)]);
        let load2 = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(2), vreg(3), imm(0)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let func = make_func_with_insts(vec![load1, call, load2, ret]);

        let dag = build_dag(&func, func.entry);

        // load1 (node 0) -> call (node 1): load before call.
        assert!(dag.nodes[1].deps.contains(&0), "call depends on prior load");
        // call (node 1) -> load2 (node 2): load after call.
        assert!(
            dag.nodes[2].deps.contains(&1),
            "post-call load depends on call"
        );
    }

    #[test]
    fn test_opcode_effect_barriers_order_memory_without_call_flag() {
        for opcode in [
            AArch64Opcode::Dmb,
            AArch64Opcode::Dsb,
            AArch64Opcode::Isb,
            AArch64Opcode::Mrs,
        ] {
            let store = MachInst::new(AArch64Opcode::StrRI, vec![vreg(0), vreg(1), imm(0)]);
            let barrier = match opcode {
                AArch64Opcode::Mrs => {
                    MachInst::with_flags(opcode, vec![vreg(10), imm(0xde82)], InstFlags::EMPTY)
                }
                _ => MachInst::with_flags(opcode, vec![imm(0)], InstFlags::EMPTY),
            };
            let load = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(2), vreg(3), imm(0)]);
            let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
            let func = make_func_with_insts(vec![store, barrier, load, ret]);

            let dag = build_dag(&func, func.entry);

            assert!(
                dag.nodes[1].deps.contains(&0),
                "{opcode:?} must depend on the prior store"
            );
            assert!(
                dag.nodes[2].deps.contains(&1),
                "post-{opcode:?} load must depend on the barrier"
            );
        }
    }

    #[test]
    fn test_stack_alloc_orders_memory_from_opcode_effect() {
        let load = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(1), vreg(2), imm(0)]);
        let stack_alloc = MachInst::with_flags(
            AArch64Opcode::StackAlloc,
            vec![vreg(3), imm(4), imm(8), imm(16)],
            InstFlags::EMPTY,
        );
        let store = MachInst::new(AArch64Opcode::StrRI, vec![vreg(4), vreg(5), imm(0)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let func = make_func_with_insts(vec![load, stack_alloc, store, ret]);

        let dag = build_dag(&func, func.entry);

        assert!(
            dag.nodes[1].deps.contains(&0),
            "StackAlloc must stay after the prior load"
        );
        assert!(
            dag.nodes[2].deps.contains(&1),
            "later store must stay after StackAlloc"
        );
    }

    // ---- Priority computation test ----

    #[test]
    fn test_priority_critical_path() {
        // v1 = mul v0, v0      (node 0, lat=3)
        // v2 = add v1, #1      (node 1, lat=1, dep on node 0)
        // ret                   (node 2, lat=1, dep on all)
        //
        // Critical path: mul(3) -> add(1) -> ret(1) = 5
        // Node 0 priority = 3 + 1 + 1 = 5
        // Node 1 priority = 1 + 1 = 2
        // Node 2 priority = 1
        let mul = MachInst::new(AArch64Opcode::MulRR, vec![vreg(1), vreg(0), vreg(0)]);
        let add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(2), vreg(1), imm(1)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let func = make_func_with_insts(vec![mul, add, ret]);

        let dag = build_dag(&func, func.entry);

        assert_eq!(dag.nodes[0].priority, 5, "mul has critical path 3+1+1=5");
        assert_eq!(dag.nodes[1].priority, 2, "add has critical path 1+1=2");
        assert_eq!(dag.nodes[2].priority, 1, "ret has priority 1");
    }

    // ---- Idempotency test ----

    #[test]
    fn test_scheduler_idempotent() {
        let add1 = MachInst::new(AArch64Opcode::AddRI, vec![vreg(1), vreg(0), imm(1)]);
        let add2 = MachInst::new(AArch64Opcode::AddRI, vec![vreg(2), vreg(0), imm(2)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![add1, add2, ret]);

        let mut sched = InstructionScheduler;
        sched.run(&mut func);

        let order1: Vec<InstId> = func.block(func.entry).insts.clone();

        // Second run should produce same order.
        let changed = sched.run(&mut func);
        let order2: Vec<InstId> = func.block(func.entry).insts.clone();

        assert_eq!(order1, order2, "scheduler should be idempotent");
        assert!(!changed, "second run should report no change");
    }

    // ---- Phase 2: Resource state tests ----

    #[test]
    fn test_resource_state_basic() {
        let mut rs = ResourceState::new();
        // IntAlu has 6 units.
        assert_eq!(rs.units_available(ExecutionPort::IntAlu, 0), 6);
        assert!(rs.is_available(ExecutionPort::IntAlu, 0));
        // Reserve one unit.
        assert!(rs.reserve(ExecutionPort::IntAlu, 0));
        assert_eq!(rs.units_available(ExecutionPort::IntAlu, 0), 5);
    }

    #[test]
    fn test_resource_state_exhaustion() {
        let mut rs = ResourceState::new();
        // IntDiv has 1 unit. Reserve it.
        assert!(rs.reserve(ExecutionPort::IntDiv, 0));
        assert_eq!(rs.units_available(ExecutionPort::IntDiv, 0), 0);
        assert!(!rs.is_available(ExecutionPort::IntDiv, 0));
        // Attempting to reserve again should fail.
        assert!(!rs.reserve(ExecutionPort::IntDiv, 0));
        // But a different cycle should be fine.
        assert!(rs.is_available(ExecutionPort::IntDiv, 1));
    }

    #[test]
    fn test_port_capacity_values() {
        assert_eq!(port_capacity(ExecutionPort::IntAlu), 6);
        assert_eq!(port_capacity(ExecutionPort::IntMul), 2);
        assert_eq!(port_capacity(ExecutionPort::IntDiv), 1);
        assert_eq!(port_capacity(ExecutionPort::LoadStore), 2);
        assert_eq!(port_capacity(ExecutionPort::Branch), 1);
        assert_eq!(port_capacity(ExecutionPort::FpAlu), 4);
    }

    // ---- Phase 2: Hazard detection tests ----

    #[test]
    fn test_detect_data_hazard() {
        // v1 = mul v0, v0    (node 0, lat=3, cycle 0)
        // v2 = add v1, #1    (node 1, lat=1, dep on node 0, cycle 3)
        // ret                 (node 2)
        //
        // Node 1 must wait until cycle 3 (producer latency 3). The gap
        // from cycle 0+1=1 to cycle 3 is a 2-cycle stall = data hazard.
        let mul = MachInst::new(AArch64Opcode::MulRR, vec![vreg(1), vreg(0), vreg(0)]);
        let add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(2), vreg(1), imm(1)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let func = make_func_with_insts(vec![mul, add, ret]);

        let mut dag = build_dag(&func, func.entry);
        let _order = schedule_list(&mut dag);
        let hazards = detect_hazards(&dag);

        let has_data_hazard = hazards.iter().any(|h| {
            matches!(
                h,
                HazardKind::DataHazard {
                    producer: 0,
                    consumer: 1,
                    ..
                }
            )
        });
        assert!(
            has_data_hazard,
            "mul->add chain should produce a data hazard"
        );
    }

    #[test]
    fn test_detect_structural_hazard_divides() {
        // Two divides at the same cycle would conflict on the single IntDiv unit.
        // v1 = sdiv v0, v2    (node 0, IntDiv)
        // v3 = sdiv v4, v5    (node 1, IntDiv, independent)
        // ret                  (node 2)
        //
        // Both are independent so the scheduler can schedule them at the same cycle,
        // but there's only 1 IntDiv unit.
        let div1 = MachInst::new(AArch64Opcode::SDiv, vec![vreg(1), vreg(0), vreg(2)]);
        let div2 = MachInst::new(AArch64Opcode::SDiv, vec![vreg(3), vreg(4), vreg(5)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let func = make_func_with_insts(vec![div1, div2, ret]);

        let mut dag = build_dag(&func, func.entry);
        let _order = schedule_list(&mut dag);

        // If both divides end up at the same cycle, there should be a structural hazard.
        // The scheduler issues one per cycle, so they might be at cycles 0 and 1.
        // Either way, verify detect_hazards runs without panic.
        let hazards = detect_hazards(&dag);
        // No panic is the basic assertion; structural hazard depends on scheduling.
        let _ = hazards.len(); // runs without error
    }

    #[test]
    fn test_detect_load_use_hazard() {
        // v1 = ldr [v0, #0]   (node 0, lat=4, LoadStore)
        // v2 = add v1, #1     (node 1, uses v1)
        // ret                  (node 2)
        //
        // After scheduling: load at cycle 0, add at cycle 4 (earliest possible).
        // No load-use hazard because add is not at cycle 1.
        let load = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(1), vreg(0), imm(0)]);
        let add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(2), vreg(1), imm(1)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let func = make_func_with_insts(vec![load, add, ret]);

        let mut dag = build_dag(&func, func.entry);
        let _order = schedule_list(&mut dag);
        let hazards = detect_hazards(&dag);

        // The scheduler correctly places add at cycle 4 (not cycle 1),
        // so there should be no load-use hazard but there IS a data hazard
        // (the 3-cycle wait).
        let has_data = hazards
            .iter()
            .any(|h| matches!(h, HazardKind::DataHazard { .. }));
        assert!(has_data, "load->add should produce a data hazard");
    }

    #[test]
    fn test_no_hazard_independent() {
        // Two independent ALU ops: no hazards expected (6 ALU units available).
        // v1 = add v0, #1    (node 0)
        // v3 = add v2, #2    (node 1, independent)
        // ret                 (node 2)
        let add1 = MachInst::new(AArch64Opcode::AddRI, vec![vreg(1), vreg(0), imm(1)]);
        let add2 = MachInst::new(AArch64Opcode::AddRI, vec![vreg(3), vreg(2), imm(2)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let func = make_func_with_insts(vec![add1, add2, ret]);

        let mut dag = build_dag(&func, func.entry);
        let _order = schedule_list(&mut dag);
        let hazards = detect_hazards(&dag);

        // No structural hazards (6 ALU units), no data hazards (independent).
        let structural = hazards
            .iter()
            .filter(|h| matches!(h, HazardKind::StructuralHazard { .. }))
            .count();
        assert_eq!(
            structural, 0,
            "independent ALU ops should have no structural hazards"
        );
    }

    // ---- Phase 2: Dual-issue hint tests ----

    #[test]
    fn test_dual_issue_alu_load() {
        // v1 = add v0, #1    (IntAlu)
        // v2 = ldr [v3, #0]  (LoadStore, independent)
        // ret
        //
        // Both can be at cycle 0 => ALU + Load dual-issue.
        let add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(1), vreg(0), imm(1)]);
        let load = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(2), vreg(3), imm(0)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let func = make_func_with_insts(vec![add, load, ret]);

        let mut dag = build_dag(&func, func.entry);
        let _order = schedule_list(&mut dag);
        let hints = find_dual_issue_hints(&dag);

        // At least one ALU + Load/Store dual-issue hint should be present.
        let has_alu_load = hints.iter().any(|h| h.reason.contains("Load/Store"));
        assert!(
            has_alu_load,
            "ALU + Load should produce dual-issue hint, got {:?}",
            hints.iter().map(|h| h.reason).collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_dual_issue_alu_alu() {
        // Two independent ALU ops at the same cycle.
        let add1 = MachInst::new(AArch64Opcode::AddRI, vec![vreg(1), vreg(0), imm(1)]);
        let add2 = MachInst::new(AArch64Opcode::AddRI, vec![vreg(3), vreg(2), imm(2)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let func = make_func_with_insts(vec![add1, add2, ret]);

        let mut dag = build_dag(&func, func.entry);
        let _order = schedule_list(&mut dag);
        let hints = find_dual_issue_hints(&dag);

        let has_alu_alu = hints.iter().any(|h| h.reason == "ALU + ALU");
        assert!(
            has_alu_alu,
            "two independent ALU ops should hint ALU + ALU dual-issue"
        );
    }

    #[test]
    fn test_no_dual_issue_dependent_chain() {
        // v1 = add v0, #1
        // v2 = add v1, #2  (depends on v1)
        // ret
        //
        // The second add can't issue at the same cycle as the first.
        let add1 = MachInst::new(AArch64Opcode::AddRI, vec![vreg(1), vreg(0), imm(1)]);
        let add2 = MachInst::new(AArch64Opcode::AddRI, vec![vreg(2), vreg(1), imm(2)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let func = make_func_with_insts(vec![add1, add2, ret]);

        let mut dag = build_dag(&func, func.entry);
        let _order = schedule_list(&mut dag);
        let hints = find_dual_issue_hints(&dag);

        // add1 at cycle 0, add2 at cycle 1 (data dep): no dual-issue possible.
        let alu_alu = hints.iter().filter(|h| h.reason == "ALU + ALU").count();
        assert_eq!(
            alu_alu, 0,
            "dependent chain should not produce dual-issue hint"
        );
    }

    // ---- Phase 2: Register pressure tests ----

    #[test]
    fn test_register_pressure_basic() {
        // v1 = add v0, #1   (def v1)
        // v2 = add v1, #2   (use v1, def v2)
        // ret
        let add1 = MachInst::new(AArch64Opcode::AddRI, vec![vreg(1), vreg(0), imm(1)]);
        let add2 = MachInst::new(AArch64Opcode::AddRI, vec![vreg(2), vreg(1), imm(2)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let func = make_func_with_insts(vec![add1, add2, ret]);

        let schedule: Vec<InstId> = func.block(func.entry).insts.clone();
        let pressure = compute_register_pressure(&func, func.entry, &schedule);

        // v1 is live from pos 0 to pos 1, v2 is live from pos 1. Max GPR = 2.
        assert!(
            pressure.max_gpr_pressure <= 3,
            "basic chain should have low pressure"
        );
        assert!(
            !pressure.pressure_exceeded(),
            "should not exceed pressure limit"
        );
    }

    #[test]
    fn test_register_pressure_high() {
        // Create many independent defs to spike pressure.
        // v1 = mov #1
        // v2 = mov #2
        // ...
        // v30 = mov #30
        // v31 = add v1, v2  (uses v1, v2 to keep them live)
        // ret
        let mut insts: Vec<MachInst> = Vec::new();
        for i in 1..=30 {
            insts.push(MachInst::new(
                AArch64Opcode::MovI,
                vec![vreg(i), imm(i as i64)],
            ));
        }
        // Use v1 and v2 to keep them live through the block.
        insts.push(MachInst::new(
            AArch64Opcode::AddRR,
            vec![vreg(31), vreg(1), vreg(2)],
        ));
        insts.push(MachInst::new(AArch64Opcode::Ret, vec![]));
        let func = make_func_with_insts(insts);

        let schedule: Vec<InstId> = func.block(func.entry).insts.clone();
        let pressure = compute_register_pressure(&func, func.entry, &schedule);

        // 30 defs, at peak all 30 are live. GPR limit is 28.
        assert!(
            pressure.max_gpr_pressure >= 28,
            "30 independent defs should produce high pressure, got {}",
            pressure.max_gpr_pressure
        );
        assert!(
            pressure.pressure_exceeded(),
            "30 live GPRs should exceed 28 limit"
        );
    }

    #[test]
    fn test_register_pressure_fpr() {
        // FPR pressure tracking.
        // v1 = fadd v0, v0   (FPR def)
        // v2 = fadd v1, v1   (FPR def, uses v1)
        // ret
        let fadd1 = MachInst::new(
            AArch64Opcode::FaddRR,
            vec![
                MachOperand::VReg(VReg::new(1, RegClass::Fpr64)),
                MachOperand::VReg(VReg::new(0, RegClass::Fpr64)),
                MachOperand::VReg(VReg::new(0, RegClass::Fpr64)),
            ],
        );
        let fadd2 = MachInst::new(
            AArch64Opcode::FaddRR,
            vec![
                MachOperand::VReg(VReg::new(2, RegClass::Fpr64)),
                MachOperand::VReg(VReg::new(1, RegClass::Fpr64)),
                MachOperand::VReg(VReg::new(1, RegClass::Fpr64)),
            ],
        );
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let func = make_func_with_insts(vec![fadd1, fadd2, ret]);

        let schedule: Vec<InstId> = func.block(func.entry).insts.clone();
        let pressure = compute_register_pressure(&func, func.entry, &schedule);

        assert!(
            pressure.max_fpr_pressure >= 1,
            "FPR ops should register FPR pressure, got {}",
            pressure.max_fpr_pressure
        );
        assert_eq!(
            pressure.max_gpr_pressure, 0,
            "FPR-only code should have no GPR pressure"
        );
    }

    #[test]
    fn test_register_pressure_kills_same_numeric_id_by_class() {
        let fpr_def = MachInst::new(AArch64Opcode::FaddRR, vec![fpreg(1), fpreg(10), fpreg(11)]);
        let gpr_def = MachInst::new(AArch64Opcode::MovI, vec![vreg(1), imm(7)]);
        let gpr_use = MachInst::new(AArch64Opcode::AddRI, vec![vreg(2), vreg(1), imm(1)]);
        let fpr_use = MachInst::new(AArch64Opcode::FaddRR, vec![fpreg(3), fpreg(1), fpreg(12)]);
        let func = make_func_with_insts(vec![fpr_def, gpr_def, gpr_use, fpr_use]);

        let schedule: Vec<InstId> = func.block(func.entry).insts.clone();
        let pressure = compute_register_pressure(&func, func.entry, &schedule);

        assert_eq!(
            pressure.gpr_pressure, 1,
            "GPR v1 should die at its same-class last use, leaving only GPR v2 live"
        );
        assert_eq!(
            pressure.fpr_pressure, 1,
            "FPR v1 should die at its same-class last use, leaving only FPR v3 live"
        );
    }

    // ---- Phase 2: Schedule metrics tests ----

    #[test]
    fn test_schedule_metrics_basic() {
        // Simple block: two independent adds + ret.
        let add1 = MachInst::new(AArch64Opcode::AddRI, vec![vreg(1), vreg(0), imm(1)]);
        let add2 = MachInst::new(AArch64Opcode::AddRI, vec![vreg(3), vreg(2), imm(2)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let func = make_func_with_insts(vec![add1, add2, ret]);

        let mut dag = build_dag(&func, func.entry);
        let order = schedule_list(&mut dag);
        let metrics = compute_schedule_metrics(&func, func.entry, &dag, &order);

        assert_eq!(metrics.total_instructions, 3);
        assert!(metrics.total_cycles > 0, "should have at least 1 cycle");
        assert!(metrics.ipc_estimate > 0.0, "IPC should be positive");
        assert!(
            metrics.critical_path_length >= 2,
            "critical path >= 2 (ALU + ret)"
        );
    }

    #[test]
    fn test_schedule_metrics_stalls() {
        // mul -> add chain: mul takes 3 cycles, add must wait.
        let mul = MachInst::new(AArch64Opcode::MulRR, vec![vreg(1), vreg(0), vreg(0)]);
        let add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(2), vreg(1), imm(1)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let func = make_func_with_insts(vec![mul, add, ret]);

        let mut dag = build_dag(&func, func.entry);
        let order = schedule_list(&mut dag);
        let metrics = compute_schedule_metrics(&func, func.entry, &dag, &order);

        // mul at cycle 0, add at cycle 3, ret at cycle 4.
        // Cycles 1, 2 are stalls (nothing issued).
        assert!(
            metrics.stall_count >= 2,
            "mul->add chain should have at least 2 stall cycles, got {}",
            metrics.stall_count
        );
    }

    #[test]
    fn test_schedule_metrics_ipc() {
        // Two independent adds + ret: all 3 can issue in rapid succession.
        let add1 = MachInst::new(AArch64Opcode::AddRI, vec![vreg(1), vreg(0), imm(1)]);
        let add2 = MachInst::new(AArch64Opcode::AddRI, vec![vreg(3), vreg(2), imm(2)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let func = make_func_with_insts(vec![add1, add2, ret]);

        let mut dag = build_dag(&func, func.entry);
        let order = schedule_list(&mut dag);
        let metrics = compute_schedule_metrics(&func, func.entry, &dag, &order);

        // 3 instructions, 3 cycles (ret at cycle 2, completes at 3) => IPC = 3/3 = 1.0.
        assert!(
            metrics.ipc_estimate >= 0.5,
            "independent ALU ops should have reasonable IPC, got {}",
            metrics.ipc_estimate
        );
    }

    #[test]
    fn test_schedule_metrics_critical_path() {
        // mul (3) -> add (1) -> ret (1) = critical path of 5
        let mul = MachInst::new(AArch64Opcode::MulRR, vec![vreg(1), vreg(0), vreg(0)]);
        let add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(2), vreg(1), imm(1)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let func = make_func_with_insts(vec![mul, add, ret]);

        let mut dag = build_dag(&func, func.entry);
        let _order = schedule_list(&mut dag);
        let metrics = compute_schedule_metrics(&func, func.entry, &dag, &_order);

        assert_eq!(
            metrics.critical_path_length, 5,
            "mul(3)->add(1)->ret(1) = critical path 5"
        );
    }

    // ---- Phase 2: Integration test ----

    #[test]
    fn test_schedule_block_with_metrics() {
        // Integration: schedule a block and get metrics back.
        let load = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(1), vreg(0), imm(0)]);
        let add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(2), vreg(1), imm(1)]);
        let mov = MachInst::new(AArch64Opcode::MovI, vec![vreg(3), imm(99)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![load, add, mov, ret]);

        let entry = func.entry;
        let (changed, metrics) = schedule_block_with_metrics(&mut func, entry);

        // The scheduler should reorder: load, mov, add, ret (mov during load latency).
        assert!(
            changed,
            "scheduler should reorder load-add-mov to load-mov-add"
        );
        assert_eq!(metrics.total_instructions, 4);
        assert!(metrics.total_cycles > 0);
        assert!(metrics.ipc_estimate > 0.0);
        assert!(!metrics.pressure_exceeded);
    }

    #[test]
    fn test_schedule_block_with_metrics_preserves_cross_block_phi_copy_webs() {
        let mut func = MachFunction::new(
            "test_metrics_phi_copy_web".to_string(),
            Signature::new(vec![], vec![]),
        );
        let entry = func.entry;
        let left = func.create_block();
        let right = func.create_block();
        let join = func.create_block();

        let branch_left = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(left)],
        ));
        func.append_inst(entry, branch_left);

        let left_load = func.push_inst(MachInst::new(
            AArch64Opcode::LdrRI,
            vec![vreg(20), vreg(21), imm(0)],
        ));
        let left_add = func.push_inst(MachInst::new(
            AArch64Opcode::AddRI,
            vec![vreg(22), vreg(20), imm(1)],
        ));
        let left_copy = func.push_inst(MachInst::new(AArch64Opcode::MovR, vec![vreg(10), vreg(4)]));
        let left_branch = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(join)],
        ));
        func.append_inst(left, left_load);
        func.append_inst(left, left_add);
        func.append_inst(left, left_copy);
        func.append_inst(left, left_branch);

        let right_copy =
            func.push_inst(MachInst::new(AArch64Opcode::MovR, vec![vreg(10), vreg(5)]));
        let right_branch = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(join)],
        ));
        func.append_inst(right, right_copy);
        func.append_inst(right, right_branch);

        let join_use = func.push_inst(MachInst::new(
            AArch64Opcode::AddRI,
            vec![vreg(11), vreg(10), imm(1)],
        ));
        let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(join, join_use);
        func.append_inst(join, ret);

        let left_original = func.block(left).insts.clone();
        let right_original = func.block(right).insts.clone();
        let join_original = func.block(join).insts.clone();

        let (left_changed, left_metrics) = schedule_block_with_metrics(&mut func, left);
        let (right_changed, right_metrics) = schedule_block_with_metrics(&mut func, right);
        let (join_changed, join_metrics) = schedule_block_with_metrics(&mut func, join);

        assert!(!left_changed);
        assert!(!right_changed);
        assert!(!join_changed);
        assert_eq!(func.block(left).insts, left_original);
        assert_eq!(func.block(right).insts, right_original);
        assert_eq!(func.block(join).insts, join_original);
        assert_eq!(left_metrics.total_instructions, left_original.len());
        assert_eq!(right_metrics.total_instructions, right_original.len());
        assert_eq!(join_metrics.total_instructions, join_original.len());
    }

    #[test]
    fn test_schedule_block_with_metrics_splits_at_internal_terminator() {
        let load = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(1), vreg(0), imm(0)]);
        let add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(2), vreg(1), imm(1)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mov = MachInst::new(AArch64Opcode::MovI, vec![vreg(3), imm(99)]);
        let mut func = make_func_with_insts(vec![load, add, ret, mov]);

        let entry = func.entry;
        let (_changed, metrics) = schedule_block_with_metrics(&mut func, entry);
        let order = &func.block(entry).insts;

        assert!(
            pos(InstId(2), order) < pos(InstId(3), order),
            "metrics scheduling must not move instructions across an internal terminator"
        );
        assert_eq!(metrics.total_instructions, 4);
    }

    #[test]
    fn test_schedule_block_with_metrics_empty() {
        let mut func = MachFunction::new("empty".to_string(), Signature::new(vec![], vec![]));
        let entry = func.entry;
        let (changed, metrics) = schedule_block_with_metrics(&mut func, entry);
        assert!(!changed);
        assert_eq!(metrics.total_instructions, 0);
        assert_eq!(metrics.total_cycles, 0);
    }

    #[test]
    fn test_schedule_block_with_metrics_single() {
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![ret]);
        let entry = func.entry;
        let (changed, metrics) = schedule_block_with_metrics(&mut func, entry);
        assert!(!changed);
        assert_eq!(metrics.total_instructions, 1);
        assert_eq!(metrics.total_cycles, 1);
        assert_eq!(metrics.stall_count, 0);
    }

    #[test]
    fn test_dual_issue_count_in_metrics() {
        // Several independent ops that should produce dual-issue hints.
        let add1 = MachInst::new(AArch64Opcode::AddRI, vec![vreg(1), vreg(0), imm(1)]);
        let load = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(2), vreg(3), imm(0)]);
        let add2 = MachInst::new(AArch64Opcode::AddRI, vec![vreg(4), vreg(5), imm(2)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let func = make_func_with_insts(vec![add1, load, add2, ret]);

        let mut dag = build_dag(&func, func.entry);
        let order = schedule_list(&mut dag);
        let metrics = compute_schedule_metrics(&func, func.entry, &dag, &order);

        // With independent ALU + Load, there should be dual-issue opportunities.
        assert!(
            metrics.dual_issue_opportunities >= 1,
            "independent ALU + Load should have dual-issue opportunities, got {}",
            metrics.dual_issue_opportunities
        );
    }

    // ---- Phase 3: Pressure-aware scheduling tests ----

    fn fpreg(id: u32) -> MachOperand {
        MachOperand::VReg(VReg::new(id, RegClass::Fpr64))
    }

    #[test]
    fn test_pressure_tracker_basic() {
        let mut tracker = PressureTracker::new();
        assert_eq!(tracker.gpr_pressure(), 0);
        assert_eq!(tracker.fpr_pressure(), 0);
        assert!(!tracker.is_high_pressure());

        // Define a GPR.
        tracker.define_vreg(VReg::new(1, RegClass::Gpr64));
        assert_eq!(tracker.gpr_pressure(), 1);
        assert_eq!(tracker.peak_gpr, 1);

        // Define an FPR.
        tracker.define_vreg(VReg::new(100, RegClass::Fpr64));
        assert_eq!(tracker.fpr_pressure(), 1);
        assert_eq!(tracker.peak_fpr, 1);

        // Kill GPR.
        tracker.kill_vreg(VReg::new(1, RegClass::Gpr64));
        assert_eq!(tracker.gpr_pressure(), 0);
        assert_eq!(tracker.peak_gpr, 1); // peak preserved
    }

    #[test]
    fn test_pressure_tracker_kill_is_class_exact() {
        let mut tracker = PressureTracker::new();

        tracker.define_vreg(VReg::new(1, RegClass::Gpr64));
        tracker.define_vreg(VReg::new(1, RegClass::Fpr64));
        assert_eq!(tracker.gpr_pressure(), 1);
        assert_eq!(tracker.fpr_pressure(), 1);

        tracker.kill_vreg(VReg::new(1, RegClass::Gpr64));
        assert_eq!(tracker.gpr_pressure(), 0);
        assert_eq!(
            tracker.fpr_pressure(),
            1,
            "killing GPR v1 must not kill FPR v1"
        );
    }

    #[test]
    fn test_pressure_tracker_high_pressure_threshold() {
        let mut tracker = PressureTracker::with_thresholds(3, 3);
        assert!(!tracker.is_high_pressure());

        // Define 4 GPR VRegs -> exceeds threshold of 3.
        tracker.define_vreg(VReg::new(1, RegClass::Gpr64));
        tracker.define_vreg(VReg::new(2, RegClass::Gpr64));
        tracker.define_vreg(VReg::new(3, RegClass::Gpr64));
        assert!(!tracker.is_high_pressure()); // exactly at threshold
        tracker.define_vreg(VReg::new(4, RegClass::Gpr64));
        assert!(tracker.is_high_pressure()); // above threshold

        // Kill one -> back to threshold.
        tracker.kill_vreg(VReg::new(1, RegClass::Gpr64));
        assert!(!tracker.is_high_pressure());
    }

    #[test]
    fn test_pressure_tracker_fpr_high_pressure() {
        let mut tracker = PressureTracker::with_thresholds(100, 2);
        // Only 2 FPR threshold.
        tracker.define_vreg(VReg::new(1, RegClass::Fpr64));
        tracker.define_vreg(VReg::new(2, RegClass::Fpr64));
        assert!(!tracker.is_high_pressure());
        tracker.define_vreg(VReg::new(3, RegClass::Fpr64));
        assert!(tracker.is_high_pressure());
    }

    #[test]
    fn test_compute_pressure_info_basic() {
        // v1 = add v0, #1   (def v1, use v0)
        // v2 = add v1, #2   (def v2, use v1 — v1 killed here)
        // ret
        let add1 = MachInst::new(AArch64Opcode::AddRI, vec![vreg(1), vreg(0), imm(1)]);
        let add2 = MachInst::new(AArch64Opcode::AddRI, vec![vreg(2), vreg(1), imm(2)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let func = make_func_with_insts(vec![add1, add2, ret]);

        let dag = build_dag(&func, func.entry);
        let infos = compute_pressure_info(&func, &dag);

        // Node 0 (add v0,#1 -> v1): defs={v1}, uses={v0}. v0 is not last-used here (also used nowhere else in
        // the DAG sense, but v0 is only used by node 0 -> it IS last use).
        assert_eq!(infos[0].defs.len(), 1);
        assert_eq!(infos[0].defs[0], VReg::new(1, RegClass::Gpr64)); // defines v1

        // Node 1 (add v1,#2 -> v2): defs={v2}, uses={v1}. v1's last use is node 1.
        assert_eq!(infos[1].defs.len(), 1);
        assert_eq!(infos[1].kills, 1); // v1 killed
        assert_eq!(infos[1].net_pressure, 0); // 1 def - 1 kill = 0

        // Node 2 (ret): no defs, no uses.
        assert_eq!(infos[2].defs.len(), 0);
        assert_eq!(infos[2].kills, 0);
    }

    #[test]
    fn test_compute_pressure_info_vreg_identity_is_class_exact() {
        let fpr_def = MachInst::new(AArch64Opcode::FaddRR, vec![fpreg(1), fpreg(10), fpreg(11)]);
        let gpr_use = MachInst::new(AArch64Opcode::AddRI, vec![vreg(2), vreg(1), imm(1)]);
        let fpr_use = MachInst::new(AArch64Opcode::FaddRR, vec![fpreg(3), fpreg(1), fpreg(12)]);
        let func = make_func_with_insts(vec![fpr_def, gpr_use, fpr_use]);

        let dag = build_dag(&func, func.entry);
        let infos = compute_pressure_info(&func, &dag);

        assert_eq!(infos[1].uses, vec![VReg::new(1, RegClass::Gpr64)]);
        assert_eq!(
            infos[1].kills, 1,
            "GPR v1's last use must not be hidden by a later FPR v1 use"
        );
        assert_eq!(
            infos[2].uses,
            vec![
                VReg::new(1, RegClass::Fpr64),
                VReg::new(12, RegClass::Fpr64)
            ]
        );
        assert_eq!(infos[2].kills, 2);
    }

    #[test]
    fn test_pressure_aware_scheduler_low_pressure() {
        // With low pressure, the pressure-aware scheduler should behave like
        // the basic scheduler (critical-path priority).
        let load = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(1), vreg(0), imm(0)]);
        let add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(2), vreg(1), imm(1)]);
        let mov = MachInst::new(AArch64Opcode::MovI, vec![vreg(3), imm(99)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![load, add, mov, ret]);

        let entry = func.entry;
        let (_changed, tracker) = schedule_block_pressure_aware(&mut func, entry);

        // Should still reorder (load, mov, add, ret) for latency hiding.
        let block = func.block(func.entry);
        let order: Vec<InstId> = block.insts.clone();
        assert_eq!(order[0], InstId(0), "load should be first");
        assert_eq!(*order.last().unwrap(), InstId(3), "ret should be last");
        assert!(tracker.peak_gpr <= 3, "low pressure test");
    }

    #[test]
    fn test_pressure_aware_scheduler_provenance_survives_reorder() {
        let load = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(1), vreg(0), imm(0)]);
        let add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(2), vreg(1), imm(1)]);
        let mov = MachInst::new(AArch64Opcode::MovI, vec![vreg(3), imm(99)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![load, add, mov, ret]);
        let original_order = func.block(func.entry).insts.clone();
        let (mut provenance, mappings) = record_identity_provenance(&func, 300);

        let mut sched = PressureAwareScheduler;
        let mut analyses = AnalysisCache::new();
        let changed =
            sched.run_with_analyses_and_provenance(&mut func, &mut analyses, &mut provenance);
        assert!(changed);

        let order = func.block(func.entry).insts.clone();
        assert_ne!(order, original_order);
        assert_eq!(order[0], InstId(0), "load should remain first");
        assert!(pos(InstId(2), &order) < pos(InstId(1), &order));
        assert_eq!(*order.last().unwrap(), InstId(3));
        assert_identity_provenance_survived(&provenance, &mappings);
    }

    #[test]
    fn test_pressure_aware_reduces_peak_pressure() {
        // Create a block with many independent defs followed by uses.
        // The pressure-naive scheduler (critical-path) would schedule all defs
        // first, spiking pressure. The pressure-aware scheduler should interleave
        // defs and uses when pressure gets high.
        //
        // Pattern:
        //   v1 = mov #1    (producer)
        //   v2 = mov #2    (producer)
        //   ...
        //   v25 = mov #25  (producer)
        //   v26 = add v1, v2  (consumer, kills v1 and v2)
        //   v27 = add v3, v4  (consumer, kills v3 and v4)
        //   ...
        //   ret
        //
        // With threshold=20: after 20 defs, pressure-aware will prefer consumers.
        let mut insts: Vec<MachInst> = Vec::new();
        let num_producers = 25;

        // 25 independent movs: v1..v25.
        for i in 1..=(num_producers as u32) {
            insts.push(MachInst::new(
                AArch64Opcode::MovI,
                vec![vreg(i), imm(i as i64)],
            ));
        }

        // 12 consumers: pair up v1+v2, v3+v4, ... v23+v24, and v25 unused.
        let consumer_start = num_producers as u32 + 1;
        for i in 0..12u32 {
            let src1 = i * 2 + 1;
            let src2 = i * 2 + 2;
            insts.push(MachInst::new(
                AArch64Opcode::AddRR,
                vec![vreg(consumer_start + i), vreg(src1), vreg(src2)],
            ));
        }

        insts.push(MachInst::new(AArch64Opcode::Ret, vec![]));
        let func = make_func_with_insts(insts.clone());

        // Measure pressure with basic scheduler.
        let basic_schedule: Vec<InstId> = {
            let mut dag = build_dag(&func, func.entry);
            schedule_list(&mut dag)
        };
        let basic_pressure = compute_register_pressure(&func, func.entry, &basic_schedule);

        // Measure pressure with pressure-aware scheduler.
        let func_pa = make_func_with_insts(insts);
        let entry = func_pa.entry;
        let mut dag = build_dag(&func_pa, entry);
        let (pa_schedule, pa_tracker) = schedule_list_pressure_aware(&func_pa, &mut dag);
        let pa_pressure = compute_register_pressure(&func_pa, entry, &pa_schedule);

        // The pressure-aware scheduler should achieve lower or equal peak GPR
        // pressure than the basic scheduler.
        assert!(
            pa_pressure.max_gpr_pressure <= basic_pressure.max_gpr_pressure,
            "pressure-aware scheduler should not increase peak pressure: \
             PA={} vs basic={}",
            pa_pressure.max_gpr_pressure,
            basic_pressure.max_gpr_pressure,
        );

        // Verify the tracker itself tracked pressure.
        assert!(
            pa_tracker.peak_gpr > 0,
            "pressure tracker should have observed some GPR pressure"
        );
    }

    #[test]
    fn test_pressure_aware_preserves_dependencies() {
        // Verify that pressure-aware scheduling still respects data dependencies.
        // v1 = add v0, #1    (inst0, def v1)
        // v2 = add v1, #2    (inst1, depends on v1)
        // ret                  (inst2)
        let add1 = MachInst::new(AArch64Opcode::AddRI, vec![vreg(1), vreg(0), imm(1)]);
        let add2 = MachInst::new(AArch64Opcode::AddRI, vec![vreg(2), vreg(1), imm(2)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![add1, add2, ret]);

        let entry = func.entry;
        let (_changed, _tracker) = schedule_block_pressure_aware(&mut func, entry);

        let block = func.block(func.entry);
        let order: Vec<InstId> = block.insts.clone();

        // add1 must come before add2 (data dependency on v1).
        let pos_add1 = order.iter().position(|&id| id == InstId(0)).unwrap();
        let pos_add2 = order.iter().position(|&id| id == InstId(1)).unwrap();
        assert!(
            pos_add1 < pos_add2,
            "pressure-aware scheduler must respect data deps: add1@{} add2@{}",
            pos_add1,
            pos_add2,
        );

        // ret must be last.
        assert_eq!(*order.last().unwrap(), InstId(2));
    }

    #[test]
    fn test_pressure_aware_preserves_memory_ordering() {
        // str v0, [v10, #0]   (store, inst0)
        // v1 = ldr [v2, #0]   (load, inst1 — must come after store)
        // ret                   (inst2)
        let store = MachInst::new(AArch64Opcode::StrRI, vec![vreg(0), vreg(10), imm(0)]);
        let load = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(1), vreg(2), imm(0)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![store, load, ret]);

        let entry = func.entry;
        let (_changed, _tracker) = schedule_block_pressure_aware(&mut func, entry);

        let block = func.block(func.entry);
        let order: Vec<InstId> = block.insts.clone();

        let pos_store = order.iter().position(|&id| id == InstId(0)).unwrap();
        let pos_load = order.iter().position(|&id| id == InstId(1)).unwrap();
        assert!(
            pos_store < pos_load,
            "pressure-aware scheduler must respect memory deps"
        );
    }

    #[test]
    fn test_pressure_aware_preserves_load_load_ordering() {
        // v1 = ldr [v0, #0]    (inst0)
        // v3 = ldr [v2, #8]    (inst1)
        // v4 = add v1, v3      (inst2)
        // ret                   (inst3)
        let load1 = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(1), vreg(0), imm(0)]);
        let load2 = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(3), vreg(2), imm(8)]);
        let add = MachInst::new(AArch64Opcode::AddRR, vec![vreg(4), vreg(1), vreg(3)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![load1, load2, add, ret]);

        let entry = func.entry;
        let (_changed, _tracker) = schedule_block_pressure_aware(&mut func, entry);

        let order = &func.block(func.entry).insts;
        assert!(
            pos(InstId(0), order) < pos(InstId(1), order),
            "pressure-aware scheduler must preserve load-load ordering"
        );
    }

    #[test]
    fn test_pressure_aware_allows_proven_reorderable_load_overlap() {
        // The pressure-aware scheduler shares the same legality DAG, so
        // proven load-load overlap must remain available on that path too.
        let load1 = proof_reorderable_load(1, 0, 0);
        let load2 = proof_reorderable_load(3, 2, 8);
        let add1 = MachInst::new(AArch64Opcode::AddRI, vec![vreg(4), vreg(1), imm(1)]);
        let add2 = MachInst::new(AArch64Opcode::AddRI, vec![vreg(5), vreg(3), imm(1)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let func = make_func_with_insts(vec![load1, load2, add1, add2, ret]);

        let mut dag = build_dag(&func, func.entry);
        let (_order, _tracker) = schedule_list_pressure_aware(&func, &mut dag);

        assert_eq!(dag.nodes[0].earliest_start, 0);
        assert!(
            dag.nodes[1].earliest_start < dag.nodes[0].latency,
            "pressure-aware scheduler should overlap proven loads: start={} latency={}",
            dag.nodes[1].earliest_start,
            dag.nodes[0].latency
        );
    }

    #[test]
    fn test_pressure_aware_pass_interface() {
        // Verify PressureAwareScheduler implements MachinePass correctly.
        let add1 = MachInst::new(AArch64Opcode::AddRI, vec![vreg(1), vreg(0), imm(1)]);
        let mul = MachInst::new(AArch64Opcode::MulRR, vec![vreg(2), vreg(3), vreg(4)]);
        let add2 = MachInst::new(AArch64Opcode::AddRI, vec![vreg(5), vreg(2), imm(1)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![add1, mul, add2, ret]);

        let mut pass = PressureAwareScheduler;
        assert_eq!(pass.name(), "pressure-aware-scheduler");
        pass.run(&mut func);

        // Just verify it doesn't crash and produces a valid schedule.
        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 4);
        assert_eq!(*block.insts.last().unwrap(), InstId(3), "ret must be last");
    }

    #[test]
    fn test_pressure_aware_empty_and_single() {
        // Empty block.
        let mut func = MachFunction::new("empty".to_string(), Signature::new(vec![], vec![]));
        let entry = func.entry;
        let (changed, tracker) = schedule_block_pressure_aware(&mut func, entry);
        assert!(!changed);
        assert_eq!(tracker.peak_gpr, 0);

        // Single instruction.
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func2 = make_func_with_insts(vec![ret]);
        let entry2 = func2.entry;
        let (changed2, tracker2) = schedule_block_pressure_aware(&mut func2, entry2);
        assert!(!changed2);
        assert_eq!(tracker2.peak_gpr, 0);
    }

    #[test]
    fn test_pressure_aware_function_scheduling() {
        // Verify schedule_function_pressure_aware works across multiple blocks.
        let add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(1), vreg(0), imm(1)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![add, ret]);

        let (changed, peak_gpr, peak_fpr) = schedule_function_pressure_aware(&mut func);
        // Two instructions, no reordering expected.
        assert!(!changed);
        // Tracker should have observed the def.
        assert!(peak_gpr <= 1);
        assert_eq!(peak_fpr, 0);
    }

    #[test]
    fn test_pressure_aware_idempotent() {
        // Pressure-aware scheduling should be idempotent.
        let add1 = MachInst::new(AArch64Opcode::AddRI, vec![vreg(1), vreg(0), imm(1)]);
        let add2 = MachInst::new(AArch64Opcode::AddRI, vec![vreg(2), vreg(0), imm(2)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![add1, add2, ret]);

        let mut pass = PressureAwareScheduler;
        pass.run(&mut func);
        let order1: Vec<InstId> = func.block(func.entry).insts.clone();

        let changed = pass.run(&mut func);
        let order2: Vec<InstId> = func.block(func.entry).insts.clone();

        assert_eq!(
            order1, order2,
            "pressure-aware scheduler should be idempotent"
        );
        assert!(!changed, "second run should report no change");
    }

    #[test]
    fn test_pressure_aware_fpr_tracking() {
        // Verify FPR pressure is tracked separately from GPR.
        // v1 = fadd v0, v0   (FPR def)
        // v2 = fadd v1, v1   (FPR def, uses v1)
        // ret
        let fadd1 = MachInst::new(AArch64Opcode::FaddRR, vec![fpreg(1), fpreg(0), fpreg(0)]);
        let fadd2 = MachInst::new(AArch64Opcode::FaddRR, vec![fpreg(2), fpreg(1), fpreg(1)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![fadd1, fadd2, ret]);

        let entry = func.entry;
        let (_changed, tracker) = schedule_block_pressure_aware(&mut func, entry);

        // Should track FPR pressure, not GPR.
        assert!(tracker.peak_fpr >= 1, "FPR ops should track FPR pressure");
        assert_eq!(
            tracker.peak_gpr, 0,
            "FPR-only code should have no GPR pressure"
        );
    }
}
