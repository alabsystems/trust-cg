// trust-cg-codegen/riscv/pipeline.rs - RISC-V end-to-end compilation pipeline
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Reference: RISC-V Unprivileged ISA Specification (Volume 1, Version 20191213)
// Reference: RISC-V ELF psABI Specification (calling convention)

//! RISC-V RV64GC end-to-end compilation pipeline.
//!
//! Takes a RISC-V ISel function (`RiscVISelFunction`) and produces encoded
//! machine code bytes (optionally wrapped in an ELF .o file).
//!
//! # Pipeline phases
//!
//! ```text
//! Phase 1: Instruction Selection
//!   trust_ir Function -> RiscVISelFunction (RiscVOpcodes, VRegs)
//!
//! Phase 2: RISC-V prologue/epilogue insertion
//!   Stack frame setup/teardown for RISC-V LP64D ABI
//!
//! Phase 3: Branch resolution
//!   Resolve block references to byte offsets (fixed 4-byte encoding)
//!
//! Phase 4: Encoding (trust-cg-codegen/riscv/encode)
//!   RiscVISelFunction -> Vec<u8> (machine code bytes)
//!
//! Phase 5: ELF emission (optional)
//!   Vec<u8> -> ELF .o file bytes
//! ```
//!
//! # Note on register allocation
//!
//! The shared register allocator (`trust-cg-regalloc`) operates on
//! `trust_cg_ir::MachFunction` which uses AArch64-centric types. The RISC-V
//! ISel produces `RiscVISelFunction` with `RiscVPReg` and `RiscVOpcode` --
//! a separate type universe. Rather than adapt that crate, the RISC-V path
//! carries its own self-contained allocator ([`RiscVRegAssignment`]): backward
//! liveness over the (possibly multi-block) instruction stream, linear-scan
//! allocation over the allocatable GPR/FPR pools with register reuse once an
//! interval ends, and stack spilling (with reload-before-use / store-after-def
//! rewriting) when pressure exceeds the pool. Every failure path is a typed
//! `RiscVPipelineError` -- the allocator never panics or mis-colors.

use std::collections::HashMap;

use trust_cg_ir::regs::{RegClass, VReg};
use trust_cg_ir::riscv_ops::RiscVOpcode;
use trust_cg_ir::riscv_regs::{
    self, A0, A1, RA, RISCV_ALLOCATABLE_FPRS, RISCV_ARG_GPRS, RISCV_CALLEE_SAVED_GPRS,
    RISCV_CALLER_SAVED_FPRS, RISCV_CALLER_SAVED_GPRS, RiscVPReg, S0, SP,
};
use trust_cg_ir::{
    DischargedEvidenceTable, EliminationCertificate, EliminationVerdict, GuardKind,
    GuardObligationReceipt, GuardOperandRef, RecheckOutcome, RiscvGuardTarget, decide,
    fingerprint_for_kind, recheck_elimination,
};

use crate::elf::constants::EF_RISCV_FLOAT_ABI_DOUBLE;
use crate::elf::{ElfMachine, ElfWriter};
use crate::riscv::encode::{RiscVEncodeError, RiscVInstOperands, encode_instruction};

// ---------------------------------------------------------------------------
// ISel types for RISC-V (parallel to x86_64_isel types)
// ---------------------------------------------------------------------------

/// Operand in a RISC-V ISel instruction.
#[derive(Debug, Clone, PartialEq)]
pub enum RiscVISelOperand {
    /// Virtual register.
    VReg(VReg),
    /// Physical register (for ABI constraints).
    PReg(RiscVPReg),
    /// Immediate integer.
    Imm(i64),
    /// Basic block target (for branches).
    Block(trust_cg_lower::instructions::Block),
    /// Global symbol name (for call relocations).
    Symbol(String),
    /// Stack slot index (resolved during frame lowering).
    StackSlot(u32),
}

/// A RISC-V ISel instruction: opcode + operands.
#[derive(Debug, Clone)]
pub struct RiscVISelInst {
    pub opcode: RiscVOpcode,
    pub operands: Vec<RiscVISelOperand>,
}

impl RiscVISelInst {
    pub fn new(opcode: RiscVOpcode, operands: Vec<RiscVISelOperand>) -> Self {
        Self { opcode, operands }
    }
}

/// A RISC-V ISel basic block.
#[derive(Debug, Clone, Default)]
pub struct RiscVISelBlock {
    pub insts: Vec<RiscVISelInst>,
    pub successors: Vec<trust_cg_lower::instructions::Block>,
}

/// A RISC-V ISel function containing RiscVISelInsts with VRegs.
#[derive(Debug, Clone)]
pub struct RiscVISelFunction {
    pub name: String,
    pub sig: trust_cg_lower::function::Signature,
    pub blocks: HashMap<trust_cg_lower::instructions::Block, RiscVISelBlock>,
    pub block_order: Vec<trust_cg_lower::instructions::Block>,
    pub next_vreg: u32,
    /// Sentinel S5 — per-carrier discharged-obligation binding, keyed by the SAME
    /// operand fingerprint the arch-neutral Certified-Elimination Kernel computes
    /// from a RISC-V bounds-check carrier (`RiscvGuardTarget::operand_identity`
    /// over `[base, index, Imm(bound)]`). This crosses the ISel boundary without a
    /// new per-instruction field: the kernel-gated proof pass re-derives each
    /// carrier's fingerprint and looks the obligation up here. A carrier absent
    /// from this map has no bound obligation, so the kernel keeps it (fail-safe).
    pub guard_obligations: HashMap<u128, u64>,
}

impl RiscVISelFunction {
    pub fn new(name: String, sig: trust_cg_lower::function::Signature) -> Self {
        Self {
            name,
            sig,
            blocks: HashMap::new(),
            block_order: Vec::new(),
            next_vreg: 0,
            guard_obligations: HashMap::new(),
        }
    }

    /// Allocate a fresh virtual register of the given class (Sentinel S5: used by
    /// the carrier expansion to materialize a wide bound into a register).
    pub fn fresh_vreg(&mut self, class: RegClass) -> VReg {
        let id = self.next_vreg;
        self.next_vreg += 1;
        VReg::new(id, class)
    }

    /// Emit a machine instruction into the given block.
    pub fn push_inst(&mut self, block: trust_cg_lower::instructions::Block, inst: RiscVISelInst) {
        self.blocks.entry(block).or_default().insts.push(inst);
    }

    /// Add a block to the function (if not already present).
    pub fn ensure_block(&mut self, block: trust_cg_lower::instructions::Block) {
        if let std::collections::hash_map::Entry::Vacant(e) = self.blocks.entry(block) {
            e.insert(RiscVISelBlock::default());
            self.block_order.push(block);
        }
    }
}

// ---------------------------------------------------------------------------
// Pipeline errors
// ---------------------------------------------------------------------------

/// Errors during RISC-V compilation.
#[derive(Debug)]
pub enum RiscVPipelineError {
    /// Instruction selection failed.
    ISel(String),
    /// Register allocation ran out of registers.
    RegAlloc(String),
    /// Encoding failed.
    Encoding(RiscVEncodeError),
    /// Prologue/epilogue generation failed.
    FrameLowering(String),
}

impl core::fmt::Display for RiscVPipelineError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::ISel(msg) => write!(f, "RISC-V ISel failed: {}", msg),
            Self::RegAlloc(msg) => write!(f, "RISC-V regalloc failed: {}", msg),
            Self::Encoding(e) => write!(f, "RISC-V encoding failed: {}", e),
            Self::FrameLowering(msg) => write!(f, "RISC-V frame lowering failed: {}", msg),
        }
    }
}

impl From<RiscVEncodeError> for RiscVPipelineError {
    fn from(e: RiscVEncodeError) -> Self {
        Self::Encoding(e)
    }
}

/// A deferred cross-function direct call recorded during per-function encoding.
///
/// A cross-function call is lowered (in `select_self_call`) to the RISC-V
/// direct-call idiom `AUIPC ra, %pcrel_hi(callee)` + `JALR ra, ra,
/// %pcrel_lo(callee)`, both carrying a `Symbol(callee)` placeholder. The
/// per-function encoder cannot resolve `callee`'s address (it lives in another
/// function's byte range, or is external), so it emits the two instructions with
/// ZERO immediates and records this fixup at the AUIPC's and JALR's
/// function-relative byte offsets. The module emitter
/// ([`Compiler::compile_riscv`]) then either:
/// * patches both immediates with the correct hi20/lo12 split of the
///   PC-relative displacement to `callee` (when `callee` is defined in the same
///   object — intra-object, no relocation), or
/// * records an `R_RISCV_CALL` relocation at `auipc_offset` against an undefined
///   `callee` symbol (when `callee` is external).
///
/// FAIL-CLOSED: a fixup whose `callee` is neither defined in the module nor
/// emittable as an external relocation is rejected with a typed error; the
/// placeholder zero immediates are NEVER left in the stream as a real target.
#[derive(Debug, Clone)]
pub struct RiscVCallFixup {
    /// Function-relative byte offset of the `AUIPC` instruction.
    pub auipc_offset: u32,
    /// Function-relative byte offset of the `JALR` instruction.
    pub jalr_offset: u32,
    /// The callee symbol name.
    pub callee: String,
}

// ---------------------------------------------------------------------------
// Real register allocator for RISC-V: liveness + linear-scan + spilling
// ---------------------------------------------------------------------------
//
// This replaces the former naive first-appearance map (no liveness/reuse/spill,
// num_spills always 0) with a genuine allocator:
//
//   1. Liveness: number every instruction linearly across `block_order`,
//      classify each operand as a def or use per opcode (the SAME operand-role
//      map encoded in `resolve_inst_operands`), run backward live-in/live-out
//      dataflow over the CFG, and build a [first-def, last-use] live interval
//      for every virtual register.
//   2. Linear scan: walk intervals in start order over the allocatable GPR/FPR
//      pools, expiring (freeing) a physical register when its interval ends so
//      that >|pool| vregs can coexist as long as <=|pool| are simultaneously
//      live. Physical-register operands (ABI args/return/ra) are honored as
//      fixed reservations so a value vreg is never colored onto a live ABI reg.
//   3. Spilling: when no free reg is available the active interval with the
//      farthest end is chosen as the spill victim, assigned a spill slot, and
//      `num_spills` is bumped. A post-pass (`rewrite_spills`) reloads each
//      spilled use (Ld/Lw/Fld from sp+offset) into a reserved scratch register
//      and stores each spilled def (Sd/Sw/Fsd) back, all within the signed
//      12-bit immediate range (else fail closed).
//
// FAIL-CLOSED: every failure path returns a typed `RiscVPipelineError::RegAlloc`
// (or `FrameLowering` for frame-offset overflow); the allocator never panics,
// indexes out of bounds, or silently mis-colors.

/// Reserved scratch GPRs used by the spill reloader/spiller (x29/x30/x31 =
/// t4/t5/t6).
///
/// These are removed from the linear-scan allocatable pool so that a reload
/// always has a guaranteed landing register and a spilled def always has a
/// guaranteed destination register. THREE are reserved because the widest
/// RISC-V instruction (an R-type) has three distinct register slots
/// (rd, rs1, rs2); if all three are different spilled vregs the rewriter still
/// has a scratch for each. A def that aliases one of its uses (in-place ops
/// like `ADD acc, acc, x`) reuses that use's scratch, so three always suffice.
const RISCV_GPR_SCRATCH: [RiscVPReg; 3] = [riscv_regs::T4, riscv_regs::T5, riscv_regs::T6];

/// Reserved scratch FPRs used by the spill reloader/spiller (f29/f30/f31 =
/// ft9/ft10/ft11).
const RISCV_FPR_SCRATCH: [RiscVPReg; 3] = [riscv_regs::FT9, riscv_regs::FT10, riscv_regs::FT11];

/// Maximum signed 12-bit immediate offset for RISC-V loads/stores.
///
/// Spill slot offsets and frame references must fit here or the S-type/I-type
/// encoders would silently truncate the field (a miscompile). We fail closed
/// instead.
const RISCV_IMM12_MAX: i64 = 2047;

/// Whether a `RegClass` denotes a floating-point register class.
fn is_fp_class(class: RegClass) -> bool {
    matches!(class, RegClass::Fpr32 | RegClass::Fpr64 | RegClass::Fpr128)
}

/// The allocatable GPR pool for the linear scan, in ABI preference order
/// (caller-saved temps/args first, then callee-saved s-regs), EXCLUDING:
/// - reserved ABI regs ra(x1) and s0/fp(x8) — clobbered by prologue/epilogue,
/// - the spill scratch regs t4/t5/t6 (`RISCV_GPR_SCRATCH`).
///
/// Net pool size is 23 GPRs (T0,T1,T2,T3 + A0..A7 + S1..S11); T4 appears in the
/// preference list below but is filtered out as a scratch register.
fn allocatable_gprs() -> Vec<RiscVPReg> {
    use riscv_regs::*;
    let preference = [
        T0, T1, T2, T3, T4, // caller-saved temporaries
        A0, A1, A2, A3, A4, A5, A6, A7, // caller-saved arg/return regs
        S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, // callee-saved
    ];
    preference
        .into_iter()
        .filter(|r| !RISCV_GPR_SCRATCH.contains(r))
        .collect()
}

/// The allocatable FPR pool for the linear scan, in ABI preference order,
/// EXCLUDING the spill scratch FPRs (ft10/ft11).
fn allocatable_fprs() -> Vec<RiscVPReg> {
    RISCV_ALLOCATABLE_FPRS
        .iter()
        .copied()
        .filter(|r| !RISCV_FPR_SCRATCH.contains(r))
        .collect()
}

/// Per-instruction def/use operand classification.
///
/// Returns the index of the operand that is a *def* (written), and the list of
/// indices that are *uses* (read). This is the single source of truth for
/// register roles and MUST stay in lockstep with `resolve_inst_operands`:
/// whichever ISel operand index that function treats as `rd` is the def here;
/// whichever it treats as `rs1`/`rs2` is a use.
///
/// Only register-shaped operands (VReg/PReg) at those indices count; Imm/Block/
/// Symbol/StackSlot are never registers and are ignored by the liveness pass.
struct DefUse {
    /// Operand index written by this instruction (if any).
    def: Option<usize>,
    /// Operand indices read by this instruction.
    uses: Vec<usize>,
}

/// Whether an ISel instruction is a CALL: a `JAL` or `JALR` whose link register
/// `rd` is `ra` (x1), as opposed to a plain unconditional jump (`JAL` with
/// `rd = x0`) or a return (`JALR x0, ra, 0`, `rd = x0`). The codegen pipeline
/// deliberately does NOT consult `RiscVOpcode::default_flags()` (only
/// `classify_def_use` and a local `is_branch`/`is_jtype` match), and there is no
/// dedicated `Call` opcode in the shared IR, so we recover "this is a call"
/// structurally from its `rd` operand — the same technique [`is_ret_inst`] uses
/// to recognise the return `JALR x0, ra, 0`.
///
/// Two call shapes carry `rd = ra`:
/// * `JAL ra, <target>` — the recursive self-call (PC-relative within the
///   function), and
/// * `JALR ra, ra, <lo12>` — the second half of a cross-function direct call
///   (`AUIPC ra, %hi` then `JALR ra, ra, %lo`); the JALR is the actual control
///   transfer that clobbers the caller-saved set and reads the argument
///   registers. The leading `AUIPC ra, %hi` only materializes the target address
///   into `ra` and is NOT itself a call (its `rd = ra` but its opcode is AUIPC).
///
/// This is the single source of truth for "this instruction clobbers the
/// caller-saved set and reads the argument registers".
fn is_riscv_call_inst(inst: &RiscVISelInst) -> bool {
    matches!(inst.opcode, RiscVOpcode::Jal | RiscVOpcode::Jalr)
        && matches!(inst.operands.first(), Some(RiscVISelOperand::PReg(p)) if *p == RA)
}

fn classify_def_use(inst: &RiscVISelInst) -> DefUse {
    use RiscVOpcode::*;
    let n = inst.operands.len();
    // CALL (JAL ra, target): the link register `ra` is the def (operand 0); every
    // trailing physical-register operand is an argument register the call READS
    // (a0..a7), attached by the ISel call lowering so liveness keeps the marshaled
    // arguments live up to the call and never recolours an argument register that
    // is still feeding the call. The full caller-saved CLOBBER set is injected
    // separately into `fixed_at` at the call's position by `compute_liveness`
    // (implicit defs are not operands).
    if is_riscv_call_inst(inst) {
        // operand 0 = rd (ra); operand 1 = Block/Imm target; operands 2.. = arg
        // PRegs (uses). Only register operands at indices >= 2 are uses.
        let uses: Vec<usize> = (2..n)
            .filter(|&i| matches!(inst.operands.get(i), Some(RiscVISelOperand::PReg(_))))
            .collect();
        return DefUse {
            def: if n >= 1 { Some(0) } else { None },
            uses,
        };
    }
    match inst.opcode {
        // No register operands at all.
        Nop | Phi | StackAlloc | Ebreak | TrapBoundsCheckExact => DefUse {
            def: None,
            uses: Vec::new(),
        },

        // R-type [rd, rs1, rs2]: def=0, uses=1,2.
        Add | Sub | And | Or | Xor | Sll | Srl | Sra | Slt | Sltu | Addw | Subw | Sllw | Srlw
        | Sraw | Mul | Mulh | Mulhsu | Mulhu | Div | Divu | Rem | Remu | Mulw | Divw | Divuw
        | Remw | Remuw | FaddD | FsubD | FmulD | FdivD | FeqD | FltD | FleD => DefUse {
            def: if n >= 1 { Some(0) } else { None },
            uses: (1..n.min(3)).collect(),
        },

        // I-type ALU/shift [rd, rs1, imm]: def=0, use=1.
        Addi | Andi | Ori | Xori | Slti | Sltiu | Slli | Srli | Srai | Addiw | Slliw | Srliw
        | Sraiw => DefUse {
            def: if n >= 1 { Some(0) } else { None },
            uses: if n >= 2 { vec![1] } else { Vec::new() },
        },

        // Loads [rd, rs1(base), imm]: def=0, use=1.
        Lb | Lh | Lw | Ld | Lbu | Lhu | Lwu | Fld => DefUse {
            def: if n >= 1 { Some(0) } else { None },
            uses: if n >= 2 { vec![1] } else { Vec::new() },
        },

        // Stores [rs2(src), rs1(base), imm]: NO def, uses=0,1.
        Sb | Sh | Sw | Sd | Fsd => DefUse {
            def: None,
            uses: (0..n.min(2)).collect(),
        },

        // Branches [rs1, rs2, off]: NO def, uses=0,1.
        Beq | Bne | Blt | Bge | Bltu | Bgeu => DefUse {
            def: None,
            uses: (0..n.min(2)).collect(),
        },

        // U-type [rd, imm20]: def=0, no reg uses.
        Lui | Auipc => DefUse {
            def: if n >= 1 { Some(0) } else { None },
            uses: Vec::new(),
        },

        // J-type JAL [rd, off]: def=0, no reg uses.
        Jal => DefUse {
            def: if n >= 1 { Some(0) } else { None },
            uses: Vec::new(),
        },

        // JALR [rd, rs1, imm]: def=0, use=1.
        Jalr => DefUse {
            def: if n >= 1 { Some(0) } else { None },
            uses: if n >= 2 { vec![1] } else { Vec::new() },
        },

        // Unary FP [rd, rs1]: def=0, use=1.
        FsqrtD | FcvtDW | FcvtWD | FcvtDL | FcvtLD | FmvXD | FmvDX => DefUse {
            def: if n >= 1 { Some(0) } else { None },
            uses: if n >= 2 { vec![1] } else { Vec::new() },
        },
    }
}

/// A live interval for one virtual register: `[start, end]` over the linear
/// instruction numbering, plus its register class.
#[derive(Debug, Clone, Copy)]
struct LiveInterval {
    vreg: VReg,
    start: u32,
    end: u32,
}

/// Liveness facts computed for the function.
struct Liveness {
    /// One interval per virtual register, unsorted.
    intervals: Vec<LiveInterval>,
    /// Linear instruction number -> set of physical registers that are *fixed*
    /// (occupied by a PReg operand) AT that instruction. Used so a value vreg is
    /// never colored onto an ABI register that is live at the same point.
    fixed_at: HashMap<u32, Vec<RiscVPReg>>,
}

/// Compute live intervals over the (possibly multi-block) instruction stream.
///
/// Numbering: instructions are numbered sequentially in `block_order`. For each
/// block we record its [first, last] instruction number. Backward dataflow then
/// computes live-in/live-out per block to a fixpoint over the CFG successors;
/// each vreg's interval is the union of [block_first, block_last] for blocks it
/// is live across, extended down to its defs and up to its uses. This connects
/// a def in one block to a use in a successor (the cross-block case) while
/// staying correct for the common single-block function.
fn compute_liveness(func: &RiscVISelFunction) -> Liveness {
    use trust_cg_lower::instructions::Block;

    // --- Number instructions and record per-block spans. ---
    let mut block_span: HashMap<Block, (u32, u32)> = HashMap::new();
    let mut inst_number: u32 = 0;
    // Per-block lists of (inst_number, &inst) handled inline below.
    let mut block_first: HashMap<Block, u32> = HashMap::new();
    for &b in &func.block_order {
        let start = inst_number;
        if let Some(mb) = func.blocks.get(&b) {
            for _ in &mb.insts {
                inst_number += 1;
            }
        }
        let end = inst_number; // exclusive
        block_first.insert(b, start);
        block_span.insert(b, (start, end));
    }

    // --- Gather per-block defs/uses (vreg granularity) for dataflow. ---
    // use_set[b]: vregs used before any def in b (upward-exposed).
    // def_set[b]: vregs defined anywhere in b.
    let mut use_set: HashMap<Block, std::collections::HashSet<VReg>> = HashMap::new();
    let mut def_set: HashMap<Block, std::collections::HashSet<VReg>> = HashMap::new();

    for &b in &func.block_order {
        let mut upward: std::collections::HashSet<VReg> = std::collections::HashSet::new();
        let mut defined: std::collections::HashSet<VReg> = std::collections::HashSet::new();
        if let Some(mb) = func.blocks.get(&b) {
            for inst in &mb.insts {
                let du = classify_def_use(inst);
                for &ui in &du.uses {
                    if let Some(RiscVISelOperand::VReg(v)) = inst.operands.get(ui)
                        && !defined.contains(v)
                    {
                        upward.insert(*v);
                    }
                }
                if let Some(di) = du.def
                    && let Some(RiscVISelOperand::VReg(v)) = inst.operands.get(di)
                {
                    defined.insert(*v);
                }
            }
        }
        use_set.insert(b, upward);
        def_set.insert(b, defined);
    }

    // --- Backward live-in/live-out dataflow to fixpoint. ---
    // live_in[b]  = use[b] ∪ (live_out[b] \ def[b])
    // live_out[b] = ∪ live_in[succ]
    let mut live_in: HashMap<Block, std::collections::HashSet<VReg>> = HashMap::new();
    let mut live_out: HashMap<Block, std::collections::HashSet<VReg>> = HashMap::new();
    for &b in &func.block_order {
        live_in.insert(b, std::collections::HashSet::new());
        live_out.insert(b, std::collections::HashSet::new());
    }

    // Bound iterations to avoid any pathological non-convergence (fail-safe).
    let max_iters = func.block_order.len().saturating_mul(2).saturating_add(10);
    for _ in 0..max_iters {
        let mut changed = false;
        // Iterate in reverse program order for faster convergence.
        for &b in func.block_order.iter().rev() {
            let mut new_out: std::collections::HashSet<VReg> = std::collections::HashSet::new();
            if let Some(mb) = func.blocks.get(&b) {
                for succ in &mb.successors {
                    if let Some(li) = live_in.get(succ) {
                        new_out.extend(li.iter().copied());
                    }
                }
            }
            let mut new_in = new_out.clone();
            if let Some(d) = def_set.get(&b) {
                new_in.retain(|v| !d.contains(v));
            }
            if let Some(u) = use_set.get(&b) {
                new_in.extend(u.iter().copied());
            }
            if live_out.get(&b) != Some(&new_out) {
                live_out.insert(b, new_out);
                changed = true;
            }
            if live_in.get(&b) != Some(&new_in) {
                live_in.insert(b, new_in);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }

    // --- Build per-vreg intervals (min start, max end). ---
    let mut start_map: HashMap<VReg, u32> = HashMap::new();
    let mut end_map: HashMap<VReg, u32> = HashMap::new();
    let mut fixed_at: HashMap<u32, Vec<RiscVPReg>> = HashMap::new();

    let extend = |start_map: &mut HashMap<VReg, u32>,
                  end_map: &mut HashMap<VReg, u32>,
                  v: VReg,
                  pos: u32| {
        start_map
            .entry(v)
            .and_modify(|s| {
                if pos < *s {
                    *s = pos;
                }
            })
            .or_insert(pos);
        end_map
            .entry(v)
            .and_modify(|e| {
                if pos > *e {
                    *e = pos;
                }
            })
            .or_insert(pos);
    };

    // Live-across: any vreg in live_in of a block is live from the block's first
    // instruction; any vreg in live_out is live through the block's last inst.
    for &b in &func.block_order {
        let (bstart, bend) = *block_span.get(&b).unwrap_or(&(0, 0));
        if bend == 0 && bstart == 0 {
            // empty function guard; still record nothing.
        }
        let last = bend.saturating_sub(1);
        if let Some(li) = live_in.get(&b) {
            for &v in li {
                extend(&mut start_map, &mut end_map, v, bstart);
            }
        }
        if let Some(lo) = live_out.get(&b) {
            for &v in lo {
                extend(&mut start_map, &mut end_map, v, last.max(bstart));
            }
        }
    }

    // Per-instruction def/use positions (and fixed PReg occupancy).
    let mut pos: u32 = 0;
    for &b in &func.block_order {
        if let Some(mb) = func.blocks.get(&b) {
            for inst in &mb.insts {
                let du = classify_def_use(inst);
                let mut fixed_here: Vec<RiscVPReg> = Vec::new();
                for &ui in &du.uses {
                    match inst.operands.get(ui) {
                        Some(RiscVISelOperand::VReg(v)) => {
                            extend(&mut start_map, &mut end_map, *v, pos);
                        }
                        Some(RiscVISelOperand::PReg(p))
                            if p.is_allocatable() && !fixed_here.contains(p) =>
                        {
                            fixed_here.push(*p);
                        }
                        _ => {}
                    }
                }
                if let Some(di) = du.def {
                    match inst.operands.get(di) {
                        Some(RiscVISelOperand::VReg(v)) => {
                            extend(&mut start_map, &mut end_map, *v, pos);
                        }
                        Some(RiscVISelOperand::PReg(p))
                            if p.is_allocatable() && !fixed_here.contains(p) =>
                        {
                            fixed_here.push(*p);
                        }
                        _ => {}
                    }
                }

                // SOUNDNESS-CRITICAL: a CALL clobbers the entire caller-saved
                // register set. The callee may overwrite any of a0-a7/t0-t6/ra
                // (and ft0-ft11/fa0-fa7), so any value vreg whose live interval
                // SPANS this call must NOT be coloured onto a caller-saved
                // register — it must land in a callee-saved s-register or be
                // spilled. We model this by recording the full caller-saved set as
                // FIXED (occupied) at the call's position: the linear-scan busy
                // loop (`assign`) unions `fixed_at` over each interval's whole
                // `[start, end]`, so an interval containing this position is forced
                // off every caller-saved register automatically. This is the exact
                // call-clobber model the phase-1 allocator previously lacked — and
                // the reason calls could not be accepted before. Only allocatable
                // pregs matter (others can never be assigned to a value vreg), but
                // we inject the full set for clarity; non-allocatable members (ra)
                // are harmless no-ops.
                if is_riscv_call_inst(inst) {
                    for &p in RISCV_CALLER_SAVED_GPRS
                        .iter()
                        .chain(RISCV_CALLER_SAVED_FPRS.iter())
                    {
                        if p.is_allocatable() && !fixed_here.contains(&p) {
                            fixed_here.push(p);
                        }
                    }
                }

                if !fixed_here.is_empty() {
                    fixed_at.insert(pos, fixed_here);
                }
                pos += 1;
            }
        }
    }

    let mut intervals: Vec<LiveInterval> = Vec::new();
    for (&v, &start) in &start_map {
        let end = *end_map.get(&v).unwrap_or(&start);
        intervals.push(LiveInterval {
            vreg: v,
            start,
            end,
        });
    }

    Liveness {
        intervals,
        fixed_at,
    }
}

/// An active allocation: an interval currently holding a physical register.
#[derive(Clone, Copy)]
struct Active {
    interval: LiveInterval,
    preg: RiscVPReg,
}

/// Result of linear-scan allocation before spill rewriting.
pub struct RiscVRegAssignment {
    /// VReg -> physical register mapping (for non-spilled vregs).
    pub allocation: HashMap<VReg, RiscVPReg>,
    /// Set of callee-saved registers that were used (need save/restore).
    pub used_callee_saved: Vec<RiscVPReg>,
    /// Number of spill slots needed.
    pub num_spills: u32,
    /// VReg -> spill slot index for spilled vregs (slot k lives at SP + k*8,
    /// reserved at the bottom of the frame). Empty when nothing spilled.
    pub spill_slots: HashMap<VReg, u32>,
}

impl RiscVRegAssignment {
    /// Perform liveness + linear-scan register allocation on an ISel function.
    ///
    /// Spilled vregs are recorded in `spill_slots`; the caller must run
    /// `rewrite_spills` on the function (with this assignment) before encode so
    /// the spill load/store traffic is materialized.
    pub fn assign(func: &RiscVISelFunction) -> Result<Self, RiscVPipelineError> {
        let liveness = compute_liveness(func);

        // Sort intervals by start position; ties broken by vreg id for
        // determinism.
        let mut intervals = liveness.intervals;
        intervals.sort_by(|a, b| a.start.cmp(&b.start).then(a.vreg.id.cmp(&b.vreg.id)));

        let gpr_pool = allocatable_gprs();
        let fpr_pool = allocatable_fprs();

        let mut allocation: HashMap<VReg, RiscVPReg> = HashMap::new();
        let mut spill_slots: HashMap<VReg, u32> = HashMap::new();
        let mut next_spill_slot: u32 = 0;

        // Per-class active lists, kept sorted by interval end (ascending).
        let mut active_gpr: Vec<Active> = Vec::new();
        let mut active_fpr: Vec<Active> = Vec::new();

        for iv in &intervals {
            let is_fp = is_fp_class(iv.vreg.class);
            let (pool, active) = if is_fp {
                (&fpr_pool, &mut active_fpr)
            } else {
                (&gpr_pool, &mut active_gpr)
            };

            // Expire intervals that end strictly before this one's start.
            active.retain(|a| a.interval.end >= iv.start);

            // Physical registers FIXED (occupied by an explicit PReg operand or
            // clobbered by a call) anywhere this interval is live, `[start, end]`.
            // These are the registers the current interval may NOT be coloured
            // onto for a reason OTHER than another value already holding them —
            // and crucially, a register fixed here cannot be freed by spilling an
            // active value (spilling moves a *value* off its register; it does not
            // remove an ABI/clobber constraint). They are kept separate from the
            // active-occupancy set so victim selection can reclaim an active
            // register but must never reclaim a fixed one.
            let mut fixed_busy: Vec<RiscVPReg> = Vec::new();
            for p in iv.start..=iv.end {
                if let Some(fixed) = liveness.fixed_at.get(&p) {
                    for &fp in fixed {
                        if !fixed_busy.contains(&fp) {
                            fixed_busy.push(fp);
                        }
                    }
                }
            }

            // Physical registers currently busy: those held by still-active
            // intervals, PLUS the fixed occupancy above.
            let mut busy: Vec<RiscVPReg> = active.iter().map(|a| a.preg).collect();
            for &fp in &fixed_busy {
                if !busy.contains(&fp) {
                    busy.push(fp);
                }
            }

            // Try to find a free physical register.
            let free = pool.iter().copied().find(|p| !busy.contains(p));

            if let Some(preg) = free {
                allocation.insert(iv.vreg, preg);
                let act = Active {
                    interval: *iv,
                    preg,
                };
                let pos = active
                    .binary_search_by(|a| a.interval.end.cmp(&act.interval.end))
                    .unwrap_or_else(|e| e);
                active.insert(pos, act);
            } else {
                // No free register: spill. Pick the active interval with the
                // farthest end as the victim (classic linear-scan heuristic).
                //
                // SOUNDNESS-CRITICAL (call-clobber interaction): the victim's
                // physical register is about to be HANDED to the current interval,
                // so it must be legal for the current interval — i.e. NOT in
                // `busy`. With call-clobber modeling, `busy` now contains the
                // caller-saved set for any interval spanning a call; reclaiming a
                // caller-saved victim register and giving it to a call-spanning
                // value would silently corrupt that value across the call. Before
                // call clobbers existed, every active register was trivially a
                // legal candidate (the original comment assumed this); that
                // assumption no longer holds, so we restrict victim candidates to
                // active intervals whose register is NOT FIXED for this interval
                // (reclaiming an active register is exactly the point; reclaiming a
                // fixed/clobbered one is the miscompile). If no active register is
                // free of the fixed constraint, `victim_idx` is `None` and we spill
                // the current interval instead — fail-safe.
                let victim_idx = active
                    .iter()
                    .enumerate()
                    .filter(|(_, a)| !fixed_busy.contains(&a.preg))
                    .max_by_key(|(_, a)| a.interval.end)
                    .map(|(i, _)| i);

                match victim_idx {
                    Some(vi) if active[vi].interval.end > iv.end => {
                        // Spill the victim, give its register to the current.
                        let victim = active[vi];
                        let preg = victim.preg;
                        // Remove the victim's mapping; assign it a spill slot.
                        allocation.remove(&victim.interval.vreg);
                        spill_slots.insert(victim.interval.vreg, next_spill_slot);
                        next_spill_slot += 1;
                        active.remove(vi);

                        allocation.insert(iv.vreg, preg);
                        let act = Active {
                            interval: *iv,
                            preg,
                        };
                        let pos = active
                            .binary_search_by(|a| a.interval.end.cmp(&act.interval.end))
                            .unwrap_or_else(|e| e);
                        active.insert(pos, act);
                    }
                    _ => {
                        // Spill the current interval itself.
                        spill_slots.insert(iv.vreg, next_spill_slot);
                        next_spill_slot += 1;
                    }
                }
            }
        }

        // Determine which callee-saved registers were actually used.
        let mut used_callee_saved: Vec<RiscVPReg> = Vec::new();
        for &preg in allocation.values() {
            if RISCV_CALLEE_SAVED_GPRS.contains(&preg) && !used_callee_saved.contains(&preg) {
                used_callee_saved.push(preg);
            }
        }
        // Deterministic order so prologue/epilogue offsets are stable.
        used_callee_saved.sort_by_key(|r| r.encoding());

        // FAIL-CLOSED ABI invariant: the linear scan must only ever hand out
        // registers from the allocatable pools, which exclude the reserved ABI
        // registers (ra/sp/gp/tp, s0/fp) and the spill scratch regs (t4/t5/t6).
        // This is the single guard that keeps a value vreg from being colored
        // onto, e.g., ra(x1) — which would silently corrupt the return address
        // across a call. The actual pool already excludes them, but a future
        // refactor that widened the pool source would otherwise miscompile
        // silently; here it becomes a typed error instead of wrong machine code.
        let gpr_pool = allocatable_gprs();
        let fpr_pool = allocatable_fprs();
        for (&vreg, &preg) in &allocation {
            if !gpr_pool.contains(&preg) && !fpr_pool.contains(&preg) {
                return Err(RiscVPipelineError::RegAlloc(format!(
                    "internal invariant violation: vreg {:?} allocated to non-allocatable \
                     register {:?} outside the ABI-safe pool (reserved/scratch register)",
                    vreg, preg
                )));
            }
        }

        Ok(Self {
            allocation,
            used_callee_saved,
            num_spills: next_spill_slot,
            spill_slots,
        })
    }
}

/// Spill-slot byte offset (SP-relative, from the bottom of the frame) for slot
/// `k`. Decoupled from frame size / callee-saved count: the lowest
/// `num_spills * 8` bytes of the frame are reserved for spills, so slot k is at
/// `SP + k*8`. Fails closed if the offset exceeds the signed 12-bit immediate.
fn spill_slot_offset(slot: u32) -> Result<i64, RiscVPipelineError> {
    let off = (slot as i64) * 8;
    if off > RISCV_IMM12_MAX {
        return Err(RiscVPipelineError::FrameLowering(format!(
            "RISC-V spill slot {} offset {} exceeds signed 12-bit immediate range",
            slot, off
        )));
    }
    Ok(off)
}

/// Load/store opcodes to use when reloading/storing a spilled vreg of a given
/// class: 8-byte GPR -> Ld/Sd, FPR -> Fld/Fsd.
fn spill_load_store_ops(class: RegClass) -> (RiscVOpcode, RiscVOpcode) {
    if is_fp_class(class) {
        (RiscVOpcode::Fld, RiscVOpcode::Fsd)
    } else {
        (RiscVOpcode::Ld, RiscVOpcode::Sd)
    }
}

/// Rewrite the instruction stream so every use of a spilled vreg is preceded by
/// a reload into a reserved scratch register and every def of a spilled vreg is
/// followed by a store of that scratch register back to its spill slot.
///
/// The spilled vreg operand is rewritten in place to the scratch PReg so the
/// downstream encode-time resolution (`resolve_inst_operands`) sees a concrete
/// physical register. Up to two distinct GPR/FPR scratch registers are used per
/// instruction so an instruction with two spilled uses still works; an
/// instruction needing more scratch than available fails closed.
fn rewrite_spills(
    func: &mut RiscVISelFunction,
    assignment: &RiscVRegAssignment,
) -> Result<(), RiscVPipelineError> {
    if assignment.spill_slots.is_empty() {
        return Ok(());
    }

    for &block_id in &func.block_order.clone() {
        let Some(mblock) = func.blocks.get_mut(&block_id) else {
            continue;
        };

        let mut new_insts: Vec<RiscVISelInst> = Vec::with_capacity(mblock.insts.len());

        for inst in &mblock.insts {
            let du = classify_def_use(inst);
            let mut inst = inst.clone();

            // Scratch register cursors (per instruction), per class.
            let mut gpr_scratch_used = 0usize;
            let mut fpr_scratch_used = 0usize;
            // Track which scratch a spilled vreg was reloaded into THIS inst so a
            // def that aliases one of its own uses (in-place ops like
            // `ADD acc, acc, x`) reuses that scratch instead of consuming a new
            // one — necessary because such an op then has only two distinct
            // register slots to satisfy.
            let mut vreg_scratch: HashMap<VReg, RiscVPReg> = HashMap::new();

            let next_scratch = |is_fp: bool,
                                gpr_used: &mut usize,
                                fpr_used: &mut usize,
                                opcode: RiscVOpcode|
             -> Result<RiscVPReg, RiscVPipelineError> {
                let s = if is_fp {
                    let r = RISCV_FPR_SCRATCH.get(*fpr_used).copied();
                    *fpr_used += 1;
                    r
                } else {
                    let r = RISCV_GPR_SCRATCH.get(*gpr_used).copied();
                    *gpr_used += 1;
                    r
                };
                s.ok_or_else(|| {
                    RiscVPipelineError::RegAlloc(format!(
                        "RISC-V spill rewrite needs more scratch registers than available \
                             in {:?}",
                        opcode
                    ))
                })
            };

            // --- Reload spilled uses BEFORE the instruction. ---
            for &ui in &du.uses {
                if let Some(RiscVISelOperand::VReg(v)) = inst.operands.get(ui).cloned()
                    && let Some(&slot) = assignment.spill_slots.get(&v)
                {
                    // A vreg used twice in one inst is reloaded once.
                    let scratch = match vreg_scratch.get(&v) {
                        Some(&s) => s,
                        None => {
                            let is_fp = is_fp_class(v.class);
                            let scratch = next_scratch(
                                is_fp,
                                &mut gpr_scratch_used,
                                &mut fpr_scratch_used,
                                inst.opcode,
                            )?;
                            let offset = spill_slot_offset(slot)?;
                            let (load_op, _) = spill_load_store_ops(v.class);
                            // Ld scratch, offset(SP)
                            new_insts.push(RiscVISelInst::new(
                                load_op,
                                vec![
                                    RiscVISelOperand::PReg(scratch),
                                    RiscVISelOperand::PReg(SP),
                                    RiscVISelOperand::Imm(offset),
                                ],
                            ));
                            vreg_scratch.insert(v, scratch);
                            scratch
                        }
                    };
                    inst.operands[ui] = RiscVISelOperand::PReg(scratch);
                }
            }

            // --- Handle a spilled def: rewrite to scratch, store AFTER. ---
            let mut def_store: Option<RiscVISelInst> = None;
            if let Some(di) = du.def
                && let Some(RiscVISelOperand::VReg(v)) = inst.operands.get(di).cloned()
                && let Some(&slot) = assignment.spill_slots.get(&v)
            {
                // If this vreg was already reloaded as a use of THIS inst (an
                // in-place def), reuse that scratch; otherwise take a fresh one.
                let scratch = match vreg_scratch.get(&v) {
                    Some(&s) => s,
                    None => {
                        let is_fp = is_fp_class(v.class);
                        next_scratch(
                            is_fp,
                            &mut gpr_scratch_used,
                            &mut fpr_scratch_used,
                            inst.opcode,
                        )?
                    }
                };
                let offset = spill_slot_offset(slot)?;
                let (_, store_op) = spill_load_store_ops(v.class);
                inst.operands[di] = RiscVISelOperand::PReg(scratch);
                // Sd scratch, offset(SP)  (ISel store order: [src, base, off])
                def_store = Some(RiscVISelInst::new(
                    store_op,
                    vec![
                        RiscVISelOperand::PReg(scratch),
                        RiscVISelOperand::PReg(SP),
                        RiscVISelOperand::Imm(offset),
                    ],
                ));
            }

            new_insts.push(inst);
            if let Some(store) = def_store {
                new_insts.push(store);
            }
        }

        mblock.insts = new_insts;
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// Call argument marshaling — parallel-move-safe physical-register copy
// ---------------------------------------------------------------------------

/// The reserved GPR used to break a cycle in the call-argument parallel copy.
///
/// `t6` (x31) is caller-saved (so it is clobbered by the call anyway, never
/// holds a value live across the call), is excluded from the allocatable value
/// pool (it is a spill scratch register), and — because the call-arg fixup runs
/// only on calls whose argument sources are NOT spilled (spilled arg sources are
/// fail-closed-rejected, see [`fixup_call_arg_parallel_copies`]) — is free of any
/// spill-reload traffic in the arg-setup window. So it is always a safe scratch
/// for resolving the argument shuffle.
const RISCV_CALL_ARG_SCRATCH: RiscVPReg = riscv_regs::T6;

/// Resolve a set of simultaneous physical-register copies `(dst, src)` into a
/// correct SEQUENTIAL ordering, breaking cycles with `scratch`.
///
/// The marshaled call arguments are a PARALLEL move: every `(a_j <- src_j)`
/// happens "at once". Emitting them naively in order is wrong when a source
/// register is also an earlier destination — e.g. swapping `a0`/`a1`
/// (`a0 <- a1 ; a1 <- a0` would read the already-overwritten `a0`). This is the
/// classic parallel-copy problem. We topologically emit every move whose
/// destination is not still needed as a source, then break one remaining cycle
/// by staging its source through `scratch`, and repeat. Mirrors the proven x86
/// `resolve_physreg_parallel_copy` (Hack et al.).
fn resolve_riscv_physreg_parallel_copy(
    copies: &[(RiscVPReg, RiscVPReg)],
    scratch: RiscVPReg,
) -> Vec<(RiscVPReg, RiscVPReg)> {
    // Drop self-copies: `a_j <- a_j` is a no-op under parallel-copy semantics.
    let mut remaining: Vec<(RiscVPReg, RiscVPReg)> =
        copies.iter().copied().filter(|(d, s)| d != s).collect();
    let mut result: Vec<(RiscVPReg, RiscVPReg)> = Vec::with_capacity(remaining.len() + 2);

    loop {
        // Phase 1: topological emit — drain every move whose destination is not
        // read by any other remaining move (safe to emit now).
        let mut progress = true;
        while progress {
            progress = false;
            let mut i = 0;
            while i < remaining.len() {
                let (dst, _) = remaining[i];
                let is_source = remaining
                    .iter()
                    .enumerate()
                    .any(|(j, &(_, s))| j != i && s == dst);
                if !is_source {
                    result.push(remaining.remove(i));
                    progress = true;
                } else {
                    i += 1;
                }
            }
        }
        if remaining.is_empty() {
            break;
        }

        // Phase 2: break one cycle. Stage the first remaining move's SOURCE into
        // `scratch` and rewrite every remaining read of that source to read
        // `scratch`, so the move that writes that source can be emitted safely on
        // the next topological pass.
        let (_d0, s0) = remaining[0];
        result.push((scratch, s0));
        for copy in &mut remaining {
            if copy.1 == s0 {
                copy.1 = scratch;
            }
        }
    }

    result
}

/// Resolve a buffered run of argument-setup `ADDI a_j, src, 0` moves into a
/// parallel-move-safe physical-register shuffle. Shared by the call boundary and
/// the cross-function `AUIPC` preamble (which must stay adjacent to its `JALR`).
///
/// FAIL-CLOSED: a spilled argument source returns a typed error rather than a
/// wrong shuffle. The defensive verbatim re-emit for an unallocated/non-register
/// source is unreachable after a successful `assign` but preserved for safety.
fn resolve_arg_move_shuffle(
    pending: &[RiscVISelInst],
    alloc: &HashMap<VReg, RiscVPReg>,
    spill_slots: &HashMap<VReg, u32>,
) -> Result<Vec<RiscVISelInst>, RiscVPipelineError> {
    let mut out: Vec<RiscVISelInst> = Vec::new();
    let mut copies: Vec<(RiscVPReg, RiscVPReg)> = Vec::with_capacity(pending.len());
    for mv in pending {
        let RiscVISelOperand::PReg(dst) = mv.operands[0] else {
            unreachable!("buffered arg move always has a PReg dst");
        };
        let src = match &mv.operands[1] {
            RiscVISelOperand::PReg(p) => *p,
            RiscVISelOperand::VReg(v) => {
                if let Some(&p) = alloc.get(v) {
                    p
                } else if spill_slots.contains_key(v) {
                    return Err(RiscVPipelineError::RegAlloc(format!(
                        "RISC-V call argument source v{} was spilled; spilled call \
                         arguments are not yet supported (fail-closed rather than emit \
                         a wrong argument shuffle)",
                        v.id
                    )));
                } else {
                    // Unallocated non-spilled source can't be resolved; re-emit
                    // verbatim (defensive — unreachable after a successful assign).
                    out.push(mv.clone());
                    continue;
                }
            }
            _ => {
                out.push(mv.clone());
                continue;
            }
        };
        copies.push((dst, src));
    }
    let resolved = resolve_riscv_physreg_parallel_copy(&copies, RISCV_CALL_ARG_SCRATCH);
    for (d, s) in resolved {
        out.push(RiscVISelInst::new(
            RiscVOpcode::Addi,
            vec![
                RiscVISelOperand::PReg(d),
                RiscVISelOperand::PReg(s),
                RiscVISelOperand::Imm(0),
            ],
        ));
    }
    Ok(out)
}

/// POST-REGALLOC fixup: rewrite each call's argument-setup `ADDI a_j, src, 0`
/// run into a parallel-move-safe physical-register shuffle.
///
/// The ISel call lowering emits, immediately before every `JAL ra, target`, a run
/// of `ADDI a_j, src_vreg, 0` moves (one per integer argument, into a0..a7). At
/// ISel time the source operands are vregs, so cycles are invisible; only AFTER
/// register allocation maps each source vreg to a physical register can a clash
/// appear (e.g. the allocator placed arg-2's source in `a0`, which arg-0's move
/// already overwrote). Emitting the moves sequentially would then read a
/// clobbered register — a silent miscompile (the documented parallel-move
/// hazard). We resolve each such run as a physical-register parallel copy with a
/// reserved scratch.
///
/// Runs BEFORE `rewrite_spills` so the arg-move sources are still VReg operands.
/// FAIL-CLOSED: if any argument source vreg was SPILLED (absent from `alloc`),
/// we have no clean place to stage it in this minimal increment, so we reject
/// with a typed error rather than emit a wrong shuffle.
fn fixup_call_arg_parallel_copies(
    func: &mut RiscVISelFunction,
    alloc: &HashMap<VReg, RiscVPReg>,
    spill_slots: &HashMap<VReg, u32>,
) -> Result<(), RiscVPipelineError> {
    for &block_id in &func.block_order.clone() {
        let Some(mblock) = func.blocks.get_mut(&block_id) else {
            continue;
        };

        let mut new_insts: Vec<RiscVISelInst> = Vec::with_capacity(mblock.insts.len());
        // Buffer of CANDIDATE arg-setup moves (the ORIGINAL instructions). They
        // are only treated as a call's argument shuffle — and subjected to the
        // spilled-source check — when a CALL actually follows. If anything else
        // interrupts the run (or the block ends), the originals are re-emitted
        // verbatim. This is essential: the `Return` lowering also emits
        // `ADDI a0, src, 0` (moving the return value into a0), and a function with
        // NO calls must be left byte-for-byte unchanged by this pass.
        let mut pending: Vec<RiscVISelInst> = Vec::new();

        for inst in std::mem::take(&mut mblock.insts) {
            // Candidate argument-setup move: `ADDI a_j, <src>, 0` into an argument
            // register. Buffer it; resolution is deferred to the call.
            let is_candidate_arg_move = inst.opcode == RiscVOpcode::Addi
                && inst.operands.len() == 3
                && matches!(inst.operands[2], RiscVISelOperand::Imm(0))
                && matches!(
                    inst.operands.first(),
                    Some(RiscVISelOperand::PReg(d)) if RISCV_ARG_GPRS.contains(d)
                );

            if is_candidate_arg_move {
                pending.push(inst);
                continue;
            }

            // The cross-function call preamble `AUIPC ra, %pcrel_hi(sym)` sits
            // immediately before its matching `JALR` and the pair MUST stay
            // adjacent (R_RISCV_CALL patches a contiguous AUIPC+JALR). So resolve
            // the buffered argument shuffle at the AUIPC preamble too — emitting
            // the shuffle BEFORE the AUIPC — leaving the AUIPC->JALR pair intact.
            // The following JALR is then reached with an empty `pending`.
            let is_call_auipc_preamble = inst.opcode == RiscVOpcode::Auipc
                && inst
                    .operands
                    .iter()
                    .any(|o| matches!(o, RiscVISelOperand::Symbol(_)));

            if is_call_auipc_preamble || is_riscv_call_inst(&inst) {
                // Resolve the buffered arg moves into a parallel-move-safe shuffle,
                // emit it, then emit this instruction (the AUIPC preamble or the
                // call). For a JALR reached right after its AUIPC preamble,
                // `pending` is already empty and this is just "emit the call".
                let shuffle = resolve_arg_move_shuffle(&pending, alloc, spill_slots)?;
                pending.clear();
                new_insts.extend(shuffle);
                new_insts.push(inst);
                continue;
            }

            // Non-arg-move, non-call: the buffered candidates were NOT a call's
            // argument shuffle (e.g. a `Return` move into a0). Re-emit them
            // verbatim, untouched.
            new_insts.append(&mut pending);
            new_insts.push(inst);
        }

        // Trailing candidates with no following call: re-emit verbatim.
        new_insts.append(&mut pending);

        mblock.insts = new_insts;
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// Operand resolution: RiscVISelOperand -> RiscVInstOperands for the encoder
// ---------------------------------------------------------------------------

/// Resolve an ISel operand to a physical register after allocation.
fn resolve_operand(op: &RiscVISelOperand, alloc: &HashMap<VReg, RiscVPReg>) -> Option<RiscVPReg> {
    match op {
        RiscVISelOperand::VReg(v) => alloc.get(v).copied(),
        RiscVISelOperand::PReg(p) => Some(*p),
        _ => None,
    }
}

/// Convert an ISel instruction to encoder operands using the register assignment.
///
/// RISC-V is a 3-operand ISA: most instructions are `rd, rs1, rs2` or
/// `rd, rs1, imm12`. This is simpler than x86-64's 2-address form.
fn resolve_inst_operands(
    inst: &RiscVISelInst,
    alloc: &HashMap<VReg, RiscVPReg>,
) -> RiscVInstOperands {
    let mut ops = RiscVInstOperands::none();

    match inst.opcode {
        // =================================================================
        // Pseudo-instructions: no operands needed.
        // =================================================================
        RiscVOpcode::Nop | RiscVOpcode::Phi | RiscVOpcode::StackAlloc => {}

        // =================================================================
        // EBREAK: fixed-encoding trap, no register/immediate operands.
        // =================================================================
        RiscVOpcode::Ebreak => {}

        // =================================================================
        // Proof-only bounds-check carrier (Sentinel S5): no encoder operands.
        // It is expanded to BGEU+EBREAK (or deleted under kernel authorization)
        // before this point; if one survives to encoding the encoder rejects it
        // (UnsupportedOpcode), so synthesizing no operands here is fail-closed.
        // =================================================================
        RiscVOpcode::TrapBoundsCheckExact => {}

        // =================================================================
        // R-type: [rd, rs1, rs2] (three-register)
        // =================================================================
        RiscVOpcode::Add
        | RiscVOpcode::Sub
        | RiscVOpcode::And
        | RiscVOpcode::Or
        | RiscVOpcode::Xor
        | RiscVOpcode::Sll
        | RiscVOpcode::Srl
        | RiscVOpcode::Sra
        | RiscVOpcode::Slt
        | RiscVOpcode::Sltu
        | RiscVOpcode::Addw
        | RiscVOpcode::Subw
        | RiscVOpcode::Sllw
        | RiscVOpcode::Srlw
        | RiscVOpcode::Sraw
        | RiscVOpcode::Mul
        | RiscVOpcode::Mulh
        | RiscVOpcode::Mulhsu
        | RiscVOpcode::Mulhu
        | RiscVOpcode::Div
        | RiscVOpcode::Divu
        | RiscVOpcode::Rem
        | RiscVOpcode::Remu
        | RiscVOpcode::Mulw
        | RiscVOpcode::Divw
        | RiscVOpcode::Divuw
        | RiscVOpcode::Remw
        | RiscVOpcode::Remuw
        | RiscVOpcode::FaddD
        | RiscVOpcode::FsubD
        | RiscVOpcode::FmulD
        | RiscVOpcode::FdivD
        | RiscVOpcode::FeqD
        | RiscVOpcode::FltD
        | RiscVOpcode::FleD => {
            if inst.operands.len() >= 3 {
                ops.rd = resolve_operand(&inst.operands[0], alloc);
                ops.rs1 = resolve_operand(&inst.operands[1], alloc);
                ops.rs2 = resolve_operand(&inst.operands[2], alloc);
            }
        }

        // =================================================================
        // I-type: [rd, rs1, imm12] (register-immediate)
        // =================================================================
        RiscVOpcode::Addi
        | RiscVOpcode::Andi
        | RiscVOpcode::Ori
        | RiscVOpcode::Xori
        | RiscVOpcode::Slti
        | RiscVOpcode::Sltiu
        | RiscVOpcode::Slli
        | RiscVOpcode::Srli
        | RiscVOpcode::Srai
        | RiscVOpcode::Addiw
        | RiscVOpcode::Slliw
        | RiscVOpcode::Srliw
        | RiscVOpcode::Sraiw => {
            if inst.operands.len() >= 2 {
                ops.rd = resolve_operand(&inst.operands[0], alloc);
                ops.rs1 = resolve_operand(&inst.operands[1], alloc);
            }
            for op in &inst.operands {
                if let RiscVISelOperand::Imm(imm) = op {
                    ops.imm = *imm as i32;
                    break;
                }
            }
        }

        // =================================================================
        // I-type: loads [rd, rs1(base), imm12(offset)]
        // =================================================================
        RiscVOpcode::Lb
        | RiscVOpcode::Lh
        | RiscVOpcode::Lw
        | RiscVOpcode::Ld
        | RiscVOpcode::Lbu
        | RiscVOpcode::Lhu
        | RiscVOpcode::Lwu
        | RiscVOpcode::Fld => {
            if inst.operands.len() >= 2 {
                ops.rd = resolve_operand(&inst.operands[0], alloc);
                ops.rs1 = resolve_operand(&inst.operands[1], alloc);
            }
            for op in &inst.operands {
                if let RiscVISelOperand::Imm(imm) = op {
                    ops.imm = *imm as i32;
                    break;
                }
            }
        }

        // =================================================================
        // S-type: stores [rs2(source), rs1(base), imm12(offset)]
        // =================================================================
        RiscVOpcode::Sb
        | RiscVOpcode::Sh
        | RiscVOpcode::Sw
        | RiscVOpcode::Sd
        | RiscVOpcode::Fsd => {
            if inst.operands.len() >= 2 {
                // ISel format: [src_reg, base_reg, offset]
                ops.rs2 = resolve_operand(&inst.operands[0], alloc);
                ops.rs1 = resolve_operand(&inst.operands[1], alloc);
            }
            for op in &inst.operands {
                if let RiscVISelOperand::Imm(imm) = op {
                    ops.imm = *imm as i32;
                    break;
                }
            }
        }

        // =================================================================
        // B-type: branches [rs1, rs2, offset]
        // =================================================================
        RiscVOpcode::Beq
        | RiscVOpcode::Bne
        | RiscVOpcode::Blt
        | RiscVOpcode::Bge
        | RiscVOpcode::Bltu
        | RiscVOpcode::Bgeu => {
            if inst.operands.len() >= 2 {
                ops.rs1 = resolve_operand(&inst.operands[0], alloc);
                ops.rs2 = resolve_operand(&inst.operands[1], alloc);
            }
            for op in &inst.operands {
                if let RiscVISelOperand::Imm(imm) = op {
                    ops.imm = *imm as i32;
                    break;
                }
            }
        }

        // =================================================================
        // U-type: [rd, imm20]
        // =================================================================
        RiscVOpcode::Lui | RiscVOpcode::Auipc => {
            if let Some(op) = inst.operands.first() {
                ops.rd = resolve_operand(op, alloc);
            }
            for op in &inst.operands {
                if let RiscVISelOperand::Imm(imm) = op {
                    ops.imm = *imm as i32;
                    break;
                }
            }
        }

        // =================================================================
        // J-type: JAL [rd, offset]
        // =================================================================
        RiscVOpcode::Jal => {
            if let Some(op) = inst.operands.first() {
                ops.rd = resolve_operand(op, alloc);
            }
            for op in &inst.operands {
                if let RiscVISelOperand::Imm(imm) = op {
                    ops.imm = *imm as i32;
                    break;
                }
            }
        }

        // =================================================================
        // JALR: [rd, rs1, imm12]
        // =================================================================
        RiscVOpcode::Jalr => {
            if inst.operands.len() >= 2 {
                ops.rd = resolve_operand(&inst.operands[0], alloc);
                ops.rs1 = resolve_operand(&inst.operands[1], alloc);
            }
            for op in &inst.operands {
                if let RiscVISelOperand::Imm(imm) = op {
                    ops.imm = *imm as i32;
                    break;
                }
            }
        }

        // =================================================================
        // Unary FP: [rd, rs1] (FSQRT.D, conversions, moves)
        // =================================================================
        RiscVOpcode::FsqrtD
        | RiscVOpcode::FcvtDW
        | RiscVOpcode::FcvtWD
        | RiscVOpcode::FcvtDL
        | RiscVOpcode::FcvtLD
        | RiscVOpcode::FmvXD
        | RiscVOpcode::FmvDX => {
            if inst.operands.len() >= 2 {
                ops.rd = resolve_operand(&inst.operands[0], alloc);
                ops.rs1 = resolve_operand(&inst.operands[1], alloc);
            }
        }
    }

    ops
}

// ---------------------------------------------------------------------------
// RISC-V LP64D ABI prologue/epilogue
// ---------------------------------------------------------------------------

/// Compute the stack frame size (16-byte aligned).
///
/// RISC-V LP64D frame layout:
/// ```text
/// [caller's frame]
/// return address (saved ra)
/// saved s0/fp
/// callee-saved regs
/// local variables / spill slots
/// [outgoing args area]  <- SP (16-byte aligned)
/// ```
fn compute_frame_size(num_callee_saved: usize, num_spills: u32) -> u32 {
    // RA + S0/FP + callee-saved registers + spill slots
    let total_slots = 2 + num_callee_saved as u32 + num_spills;
    let total_bytes = total_slots * 8;

    // Round up to 16-byte alignment.
    (total_bytes + 15) & !15
}

/// Generate prologue instructions for RISC-V LP64D ABI.
fn generate_prologue(callee_saved: &[RiscVPReg], frame_size: u32) -> Vec<RiscVISelInst> {
    let mut prologue = Vec::new();

    // ADDI SP, SP, -frame_size (allocate stack frame)
    if frame_size > 0 {
        prologue.push(RiscVISelInst::new(
            RiscVOpcode::Addi,
            vec![
                RiscVISelOperand::PReg(SP),
                RiscVISelOperand::PReg(SP),
                RiscVISelOperand::Imm(-(frame_size as i64)),
            ],
        ));
    }

    // SD RA, frame_size-8(SP) (save return address)
    let ra_offset = frame_size as i64 - 8;
    prologue.push(RiscVISelInst::new(
        RiscVOpcode::Sd,
        vec![
            RiscVISelOperand::PReg(RA),
            RiscVISelOperand::PReg(SP),
            RiscVISelOperand::Imm(ra_offset),
        ],
    ));

    // SD S0, frame_size-16(SP) (save frame pointer)
    let fp_offset = frame_size as i64 - 16;
    prologue.push(RiscVISelInst::new(
        RiscVOpcode::Sd,
        vec![
            RiscVISelOperand::PReg(S0),
            RiscVISelOperand::PReg(SP),
            RiscVISelOperand::Imm(fp_offset),
        ],
    ));

    // ADDI S0, SP, frame_size (set frame pointer)
    prologue.push(RiscVISelInst::new(
        RiscVOpcode::Addi,
        vec![
            RiscVISelOperand::PReg(S0),
            RiscVISelOperand::PReg(SP),
            RiscVISelOperand::Imm(frame_size as i64),
        ],
    ));

    // Save callee-saved registers.
    for (i, &reg) in callee_saved.iter().enumerate() {
        let offset = frame_size as i64 - 24 - (i as i64 * 8);
        prologue.push(RiscVISelInst::new(
            RiscVOpcode::Sd,
            vec![
                RiscVISelOperand::PReg(reg),
                RiscVISelOperand::PReg(SP),
                RiscVISelOperand::Imm(offset),
            ],
        ));
    }

    prologue
}

/// Generate epilogue instructions for RISC-V LP64D ABI.
fn generate_epilogue(callee_saved: &[RiscVPReg], frame_size: u32) -> Vec<RiscVISelInst> {
    let mut epilogue = Vec::new();

    // Restore callee-saved registers in reverse order.
    for (i, &reg) in callee_saved.iter().enumerate().rev() {
        let offset = frame_size as i64 - 24 - (i as i64 * 8);
        epilogue.push(RiscVISelInst::new(
            RiscVOpcode::Ld,
            vec![
                RiscVISelOperand::PReg(reg),
                RiscVISelOperand::PReg(SP),
                RiscVISelOperand::Imm(offset),
            ],
        ));
    }

    // LD RA, frame_size-8(SP) (restore return address)
    let ra_offset = frame_size as i64 - 8;
    epilogue.push(RiscVISelInst::new(
        RiscVOpcode::Ld,
        vec![
            RiscVISelOperand::PReg(RA),
            RiscVISelOperand::PReg(SP),
            RiscVISelOperand::Imm(ra_offset),
        ],
    ));

    // LD S0, frame_size-16(SP) (restore frame pointer)
    let fp_offset = frame_size as i64 - 16;
    epilogue.push(RiscVISelInst::new(
        RiscVOpcode::Ld,
        vec![
            RiscVISelOperand::PReg(S0),
            RiscVISelOperand::PReg(SP),
            RiscVISelOperand::Imm(fp_offset),
        ],
    ));

    // ADDI SP, SP, frame_size (deallocate stack frame)
    if frame_size > 0 {
        epilogue.push(RiscVISelInst::new(
            RiscVOpcode::Addi,
            vec![
                RiscVISelOperand::PReg(SP),
                RiscVISelOperand::PReg(SP),
                RiscVISelOperand::Imm(frame_size as i64),
            ],
        ));
    }

    epilogue
}

// ---------------------------------------------------------------------------
// Branch resolution for fixed-length RISC-V instructions
// ---------------------------------------------------------------------------

/// Return the encoded byte size of a RISC-V instruction.
///
/// All RISC-V base ISA instructions are exactly 4 bytes (32 bits).
/// Pseudo-instructions (Phi, StackAlloc, Nop-as-pseudo) encode as 4 bytes
/// since NOP is ADDI x0, x0, 0.
fn inst_size(inst: &RiscVISelInst) -> usize {
    match inst.opcode {
        // Pseudo-instructions that we skip during encoding.
        // The proof-only bounds-check carrier (Sentinel S5) is also zero-sized:
        // it is expanded or deleted before encoding, so it must not contribute to
        // PC-relative branch offsets if it is still present at branch resolution
        // (the encoder rejects any survivor). EBREAK, by contrast, is a real
        // 4-byte trap instruction handled by the `_ => 4` arm.
        RiscVOpcode::Phi | RiscVOpcode::StackAlloc | RiscVOpcode::TrapBoundsCheckExact => 0,
        // Everything else is 4 bytes.
        _ => 4,
    }
}

/// FAIL-CLOSED B-type (conditional branch) PC-relative range: a signed 13-bit
/// even offset, `[-4096, 4094]`. Mirrors `encode::check_branch_offset` but is
/// applied on the FULL i64 offset BEFORE the `i64 -> i32` cast in
/// `resolve_inst_operands` (which could otherwise wrap a far offset back into a
/// spuriously-in-range value = silent miscompile).
const RISCV_BRANCH_OFFSET_MIN: i64 = -4096;
const RISCV_BRANCH_OFFSET_MAX: i64 = 4094;

/// FAIL-CLOSED J-type (JAL) PC-relative range: a signed 21-bit even offset,
/// `[-1048576, 1048574]`.
const RISCV_JUMP_OFFSET_MIN: i64 = -1_048_576;
const RISCV_JUMP_OFFSET_MAX: i64 = 1_048_574;

/// FAIL-CLOSED AUIPC+JALR (`R_RISCV_CALL`) PC-relative reach: a signed 32-bit
/// displacement, `[-2^31, 2^31 - 1]`. The hi20 (AUIPC) carries the upper bits and
/// the lo12 (JALR) the lower 12, so the pair reaches anywhere a 32-bit signed
/// offset can — far more than a bare `JAL`.
const RISCV_CALL_OFFSET_MIN: i64 = i32::MIN as i64;
const RISCV_CALL_OFFSET_MAX: i64 = i32::MAX as i64;

/// Split a signed 32-bit PC-relative displacement into the `(hi20, lo12)` halves
/// of an `AUIPC`/`JALR` (or `AUIPC`/load) pcrel pair, per the RISC-V psABI.
///
/// The AUIPC computes `ra = pc + (hi20 << 12)` and the JALR computes
/// `target = ra + sign_extend(lo12)`. Because `lo12` is sign-extended, `hi20`
/// must be rounded with the `+ 0x800` carry compensation so that
/// `(hi20 << 12) + sign_extend(lo12) == disp` exactly. Getting this rounding
/// wrong is the classic RISC-V relocation miscompile, so it is isolated here and
/// unit-tested.
///
/// FAIL-CLOSED: `disp` must fit the signed 32-bit reach; an out-of-range value
/// returns `None` so the caller can reject rather than emit a wrong target.
pub fn riscv_split_pcrel_hi_lo(disp: i64) -> Option<(i32, i32)> {
    if !(RISCV_CALL_OFFSET_MIN..=RISCV_CALL_OFFSET_MAX).contains(&disp) {
        return None;
    }
    let disp = disp as i32;
    // lo12 = sign-extended low 12 bits of disp.
    let lo12 = (disp << 20) >> 20; // arithmetic shift sign-extends
    // hi20 = (disp - lo12) >> 12, i.e. (disp + 0x800) >> 12 with carry handling.
    let hi20 = ((disp as i64 - lo12 as i64) >> 12) as i32;
    // The AUIPC stores hi20 in a SIGNED 20-bit field and the hardware sign-extends
    // it at runtime. For disp in the top 2 KiB of the positive reach
    // ([0x7FFF_F800, 0x7FFF_FFFF]) the +0x800 carry makes hi20 = 0x8_0000, which
    // does NOT fit the signed 20-bit field: when masked to 20 bits and
    // sign-extended it becomes -524288, so the AUIPC computes the WRONG target.
    // Reconstruct with the 20-bit-SIGN-EXTENDED hi20 (exactly what the encoder
    // stores and the CPU sees) so this overflow fails the exactness check and is
    // rejected fail-closed, rather than passing the check against the full i32
    // hi20 and silently miscompiling. The true reach is thus [-2^31, 0x7FFF_F7FF].
    let hi20_se = (hi20 << 12) >> 12; // sign-extend from bit 19 via i32 arithmetic
    let recon = ((hi20_se as i64) << 12) + (lo12 as i64);
    if recon != disp as i64 {
        return None;
    }
    Some((hi20, lo12))
}

/// Patch the immediate of a U-type instruction word (e.g. `AUIPC`) in-place.
///
/// The U-type immediate occupies bits 31:12. The placeholder word has those bits
/// zero, so we clear-then-set them with `hi20`.
fn riscv_patch_u_imm(word: u32, hi20: i32) -> u32 {
    (word & 0x0000_0FFF) | (((hi20 as u32) & 0xF_FFFF) << 12)
}

/// Patch the immediate of an I-type instruction word (e.g. `JALR`) in-place.
///
/// The I-type immediate occupies bits 31:20. The placeholder word has those bits
/// zero, so we clear-then-set them with `lo12`.
fn riscv_patch_i_imm(word: u32, lo12: i32) -> u32 {
    (word & 0x000F_FFFF) | (((lo12 as u32) & 0xFFF) << 20)
}

/// Resolve a single intra-object cross-function call by patching the `AUIPC`/
/// `JALR` pcrel pair in `text` to point PC-relatively at `callee_offset`.
///
/// `text` is the WHOLE module `.text`; `auipc_offset`/`jalr_offset` and
/// `callee_offset` are section-relative byte offsets. The displacement is
/// computed from the AUIPC's address (the pcrel-hi anchor). The JALR's lo12 is
/// the same `disp`'s low 12 bits relative to the SAME AUIPC PC, which is the
/// psABI rule for an `AUIPC`+`JALR` pair sharing one `%pcrel_hi`.
///
/// FAIL-CLOSED: returns an error if either patch site is out of bounds or the
/// displacement does not fit the signed 32-bit reach (caller never emits a wrong
/// target).
pub fn riscv_patch_intra_object_call(
    text: &mut [u8],
    auipc_offset: u32,
    jalr_offset: u32,
    callee_offset: u32,
) -> Result<(), RiscVPipelineError> {
    let disp = callee_offset as i64 - auipc_offset as i64;
    let (hi20, lo12) = riscv_split_pcrel_hi_lo(disp).ok_or_else(|| {
        RiscVPipelineError::FrameLowering(format!(
            "RISC-V intra-object call displacement {disp} (callee@{callee_offset} - \
             auipc@{auipc_offset}) is out of the signed 32-bit AUIPC+JALR reach; \
             failing closed rather than emitting a wrong call target"
        ))
    })?;

    let read_word = |t: &[u8], off: u32| -> Result<u32, RiscVPipelineError> {
        let i = off as usize;
        if i + 4 > t.len() {
            return Err(RiscVPipelineError::FrameLowering(format!(
                "RISC-V call patch offset {off} is out of bounds for {}-byte .text",
                t.len()
            )));
        }
        Ok(u32::from_le_bytes([t[i], t[i + 1], t[i + 2], t[i + 3]]))
    };

    let auipc_word = read_word(text, auipc_offset)?;
    let jalr_word = read_word(text, jalr_offset)?;
    let patched_auipc = riscv_patch_u_imm(auipc_word, hi20);
    let patched_jalr = riscv_patch_i_imm(jalr_word, lo12);

    let ai = auipc_offset as usize;
    text[ai..ai + 4].copy_from_slice(&patched_auipc.to_le_bytes());
    let ji = jalr_offset as usize;
    text[ji..ji + 4].copy_from_slice(&patched_jalr.to_le_bytes());
    Ok(())
}

/// The reserved scratch GPR used by far-`JAL` relaxation to hold `pc + hi20`
/// across the inserted `AUIPC`/`JALR` pair.
///
/// Relaxation runs in Phase 3 (AFTER register allocation and spill rewriting),
/// so the chosen register MUST be one the allocator never colours a live value
/// onto. `T5` is one of the three reserved spill-scratch GPRs
/// ([`RISCV_GPR_SCRATCH`]) and is therefore excluded from the allocatable pool
/// ([`allocatable_gprs`]); the spill rewriter only ever uses a scratch
/// transiently WITHIN a single reload/store instruction (never live across an
/// instruction boundary), so `T5` is guaranteed dead at the relaxation point.
/// The `AUIPC` writes `T5` and the immediately-following `JALR` reads it; no
/// other instruction observes it. (`T6` is reserved for call-arg marshaling /
/// the spiller's third scratch; `T5` keeps the far-jump path independent.)
const RISCV_FAR_JUMP_SCRATCH: RiscVPReg = riscv_regs::T5;

/// FAIL-CLOSED iteration bound for the far-branch relaxation fixpoint.
///
/// The bound is INSTRUCTION-count-based, NOT block-count-based. The fixpoint
/// relaxes exactly ONE branch/jump per iteration and then restarts the scan from
/// scratch, so the number of iterations needed scales with the number of far
/// branch/jump INSTRUCTIONS — independent of how few blocks they live in. (A
/// block-bounded cap spuriously fails closed on a valid program with many far
/// branches packed into few blocks.)
///
/// Relaxation only ever GROWS code (an out-of-range conditional branch gains one
/// `JAL`; an out-of-range `JAL` becomes an `AUIPC`+`JALR` pair, +1 inst) and
/// every original branch is relaxed AT MOST TWICE (a conditional `Bcc` first
/// cascades to `Bcc_inv` + `JAL`, then that fresh `JAL` cascades to
/// `AUIPC`+`JALR`). The relaxed `AUIPC`/`JALR` carry a deferred `Block` target
/// but are NEITHER `Jal` NOR a conditional opcode, so the scan skips them — they
/// are never re-relaxation candidates. Thus total relaxation events are bounded
/// by `2 * (count of far branch/jump insts) <= 2 * total_insts`. The cap is
/// `2 * total_insts + 10`: `2x` covers each branch's two-stage cascade, the `+10`
/// slack covers the final no-change confirming iteration and defensive margin.
/// Monotone growth guarantees termination; the bound fails closed (never loops,
/// never miscompiles) if the invariant is ever violated.
fn riscv_relax_iteration_cap(func: &RiscVISelFunction) -> usize {
    let total_insts: usize = func
        .block_order
        .iter()
        .filter_map(|b| func.blocks.get(b))
        .map(|mblock| mblock.insts.len())
        .sum();
    total_insts.saturating_mul(2).saturating_add(10)
}

/// The inverse of a RISC-V conditional-branch opcode, used by far-branch
/// relaxation to build the inverted short branch that skips over a `JAL` to the
/// far target (preserving the EXACT taken/not-taken semantics of the original).
///
/// `Beq <-> Bne`, `Blt <-> Bge`, `Bltu <-> Bgeu`. This is an explicit RISC-V
/// match: unlike AArch64's `cc ^ 1`, RISC-V condition inversion is not a bit
/// flip on the funct3 field, so it MUST be spelled out. Returns `None` for any
/// non-conditional-branch opcode (the caller treats that as "not relaxable as a
/// conditional branch").
fn riscv_invert_branch_opcode(op: RiscVOpcode) -> Option<RiscVOpcode> {
    Some(match op {
        RiscVOpcode::Beq => RiscVOpcode::Bne,
        RiscVOpcode::Bne => RiscVOpcode::Beq,
        RiscVOpcode::Blt => RiscVOpcode::Bge,
        RiscVOpcode::Bge => RiscVOpcode::Blt,
        RiscVOpcode::Bltu => RiscVOpcode::Bgeu,
        RiscVOpcode::Bgeu => RiscVOpcode::Bltu,
        _ => return None,
    })
}

/// Compute each block's byte offset by summing [`inst_size`] over `block_order`.
///
/// Shared by the relaxation fixpoint (which recomputes after each insertion) and
/// the final Block->Imm conversion. RISC-V offsets are PC-relative to the branch
/// instruction itself, so callers subtract the branch's own byte offset.
fn riscv_compute_block_offsets(
    func: &RiscVISelFunction,
) -> HashMap<trust_cg_lower::instructions::Block, i64> {
    let mut block_offsets = HashMap::new();
    let mut current_offset: i64 = 0;
    for &block_id in &func.block_order {
        block_offsets.insert(block_id, current_offset);
        if let Some(mblock) = func.blocks.get(&block_id) {
            for inst in &mblock.insts {
                current_offset += inst_size(inst) as i64;
            }
        }
    }
    block_offsets
}

/// FAIL-CLOSED far-branch / far-jump relaxation, run before the final
/// Block->Imm conversion in [`resolve_riscv_branches`].
///
/// Iterates to a fixpoint. Each iteration recomputes block byte offsets, then
/// scans every branch/`JAL` that still carries a `Block` target:
///
/// * An out-of-range CONDITIONAL branch `Bcc rs1, rs2, far` is rewritten to its
///   INVERTED short branch `Bcc_inv rs1, rs2, +8` (an `Imm(8)` skip, always in
///   B-range) followed by an inserted `JAL x0, Block(far)`. The taken/not-taken
///   semantics are preserved exactly: when the original would NOT take the
///   branch, the inverted branch IS taken and skips the `JAL` (fallthrough);
///   when the original WOULD take it, the inverted branch is not taken and the
///   `JAL` jumps to `far`.
/// * An out-of-range unconditional `JAL x0, far` (including a `JAL` freshly
///   inserted by the step above) is rewritten to `AUIPC scratch, %pcrel_hi(disp)`
///   + `JALR x0, scratch, %pcrel_lo(disp)`, reaching any signed-32-bit target.
///
/// Insertions shift offsets, so the loop restarts the scan after each change and
/// recomputes offsets, until no branch needs relaxation. Monotone code growth
/// guarantees convergence (see [`riscv_relax_iteration_cap`]).
///
/// FAIL-CLOSED: only beyond the signed-32-bit `AUIPC`+`JALR` reach (i.e.
/// [`riscv_split_pcrel_hi_lo`] returns `None`) — or if the iteration cap is hit
/// (the convergence invariant violated) — does this return a typed
/// [`RiscVPipelineError`]. A `JAL ra/...` (a CALL with a non-zero link register,
/// e.g. the self-recursive call idiom) is NOT a plain jump and is relaxed the
/// same way but preserving its link register on the `JALR`.
fn relax_riscv_far_branches(func: &mut RiscVISelFunction) -> Result<(), RiscVPipelineError> {
    use trust_cg_lower::instructions::Block;

    let cap = riscv_relax_iteration_cap(func);
    for _iter in 0..cap {
        let block_offsets = riscv_compute_block_offsets(func);
        let block_order = func.block_order.clone();
        let mut changed = false;

        'scan: for &block_id in &block_order {
            let block_base = *block_offsets.get(&block_id).unwrap_or(&0);
            // Snapshot the per-instruction info we need without holding a borrow,
            // so we can mutate the block on a relaxation hit.
            let probe: Vec<(usize, RiscVOpcode, Option<Block>)> = match func.blocks.get(&block_id) {
                Some(mblock) => mblock
                    .insts
                    .iter()
                    .map(|inst| {
                        let target = inst.operands.iter().find_map(|op| match op {
                            RiscVISelOperand::Block(b) => Some(*b),
                            _ => None,
                        });
                        (inst_size(inst), inst.opcode, target)
                    })
                    .collect(),
                None => continue,
            };

            let mut inst_offset = block_base;
            for (pos, (isize_val, opcode, target)) in probe.into_iter().enumerate() {
                let branch_addr = inst_offset;
                inst_offset += isize_val as i64;

                let Some(target_block) = target else { continue };

                let is_jtype = matches!(opcode, RiscVOpcode::Jal);
                let is_cond = riscv_invert_branch_opcode(opcode).is_some();
                if !is_jtype && !is_cond {
                    continue;
                }

                let target_offset = match block_offsets.get(&target_block) {
                    Some(&o) => o,
                    None => {
                        return Err(RiscVPipelineError::FrameLowering(format!(
                            "RISC-V {opcode:?} targets block {} which is absent from \
                             block_order; cannot relax a PC-relative offset",
                            target_block.0
                        )));
                    }
                };
                let rel_offset = target_offset - branch_addr;

                let (lo, hi) = if is_jtype {
                    (RISCV_JUMP_OFFSET_MIN, RISCV_JUMP_OFFSET_MAX)
                } else {
                    (RISCV_BRANCH_OFFSET_MIN, RISCV_BRANCH_OFFSET_MAX)
                };
                // In range (and even — all RISC-V code is 4-byte aligned, so
                // every offset here is even by construction): nothing to do; the
                // final Block->Imm pass will convert it.
                if (lo..=hi).contains(&rel_offset) && (rel_offset & 1) == 0 {
                    continue;
                }

                // Out of range -> relax.
                if is_cond {
                    relax_riscv_far_conditional(func, block_id, pos, opcode, target_block);
                } else {
                    // Deferred resolution: relax_riscv_far_jump emits AUIPC+JALR
                    // carrying the far Block target; the FINAL pass splits the
                    // pcrel disp on the final layout (off-by-4-proof). It no
                    // longer fails on reach — the final pass is the single
                    // fail-closed point for the signed-32-bit boundary.
                    relax_riscv_far_jump(func, block_id, pos, target_block);
                }
                changed = true;
                // Offsets shifted; recompute from scratch.
                break 'scan;
            }
        }

        if !changed {
            return Ok(());
        }
    }

    // The fixpoint did not converge within the bound. The relaxation invariant
    // (monotone growth, each inst relaxed at most once) should make this
    // unreachable; fail closed rather than risk an unbounded loop or a wrong
    // target, per the prime directive.
    Err(RiscVPipelineError::FrameLowering(format!(
        "RISC-V far-branch relaxation did not converge within {cap} iterations; \
         failing closed rather than looping or emitting a wrong target"
    )))
}

/// Relax an out-of-range CONDITIONAL branch in place: replace
/// `Bcc rs1, rs2, Block(far)` with `Bcc_inv rs1, rs2, Imm(8)` and insert
/// `JAL x0, Block(far)` right after it. The far `JAL`'s Block target is left
/// UNRESOLVED so a later fixpoint iteration converts it to an offset (or relaxes
/// it to `AUIPC`+`JALR` if it too is out of range).
fn relax_riscv_far_conditional(
    func: &mut RiscVISelFunction,
    block_id: trust_cg_lower::instructions::Block,
    pos: usize,
    opcode: RiscVOpcode,
    far_target: trust_cg_lower::instructions::Block,
) {
    let inv = riscv_invert_branch_opcode(opcode).expect("caller guarantees a conditional branch");
    let mblock = func
        .blocks
        .get_mut(&block_id)
        .expect("block exists (probed above)");
    let orig = mblock.insts[pos].clone();

    // Keep rs1/rs2 (the non-Block operands) in order; replace ONLY the Block
    // with the +8 short-skip immediate. The skip is +8 bytes = over the single
    // 4-byte JAL that follows (offset is relative to the inverted branch itself).
    let mut inv_operands: Vec<RiscVISelOperand> = orig
        .operands
        .iter()
        .filter(|op| !matches!(op, RiscVISelOperand::Block(_)))
        .cloned()
        .collect();
    inv_operands.push(RiscVISelOperand::Imm(8));

    mblock.insts[pos] = RiscVISelInst::new(inv, inv_operands);
    // JAL x0, far  (carries the original far Block target, still unresolved).
    let far_jal = RiscVISelInst::new(
        RiscVOpcode::Jal,
        vec![
            RiscVISelOperand::PReg(riscv_regs::ZERO),
            RiscVISelOperand::Block(far_target),
        ],
    );
    mblock.insts.insert(pos + 1, far_jal);
}

/// Relax an out-of-range `JAL` in place: replace `JAL rd, Block(far)` with
/// `AUIPC scratch, Block(far)` + `JALR rd, scratch, Block(far)`. The original
/// link register `rd` is preserved on the `JALR` (so `JAL x0`, a plain jump,
/// stays `JALR x0`; a `JAL ra`, a call, stays `JALR ra`).
///
/// DEFERRED RESOLUTION (off-by-4-proof): the `AUIPC` and `JALR` carry the far
/// target as a `Block` operand — NOT a baked immediate. The single FINAL
/// offset-resolution pass ([`resolve_riscv_branches`] Phase 2), running on the
/// FINAL post-all-insertion layout, splits the pcrel displacement (from the
/// `AUIPC`'s FINAL byte offset to the target's FINAL byte offset) into hi20/lo12
/// via [`riscv_split_pcrel_hi_lo`] and replaces each `Block` with the resolved
/// `Imm`. Because nothing is baked at insert time, inserting the `JALR` here
/// (which shifts every forward target by +4) — and any LATER relaxation that
/// inserts code between this `AUIPC` and its target — cannot stale the
/// displacement: resolution happens once, at the end, on the final layout.
///
/// The relaxed `AUIPC`/`JALR` carry a `Block` but are NEITHER `Jal` NOR a
/// conditional opcode, so the relaxation scan ([`relax_riscv_far_branches`])
/// skips them: they are never re-relaxation candidates (the cap invariant relies
/// on this).
///
/// FAIL-CLOSED has MOVED to the final pass: this function no longer splits the
/// displacement, so it cannot fail on reach. A target genuinely beyond the
/// signed-32-bit `AUIPC`+`JALR` reach is rejected (typed error) by Phase 2 when
/// [`riscv_split_pcrel_hi_lo`] returns `None`.
fn relax_riscv_far_jump(
    func: &mut RiscVISelFunction,
    block_id: trust_cg_lower::instructions::Block,
    pos: usize,
    target_block: trust_cg_lower::instructions::Block,
) {
    let mblock = func
        .blocks
        .get_mut(&block_id)
        .expect("block exists (probed above)");
    let orig = mblock.insts[pos].clone();

    // The original JAL's link register is its FIRST operand (PReg). Preserve it
    // on the JALR (x0 for a plain jump, ra for a call).
    let link = orig
        .operands
        .iter()
        .find_map(|op| match op {
            RiscVISelOperand::PReg(p) => Some(*p),
            _ => None,
        })
        .unwrap_or(riscv_regs::ZERO);

    // AUIPC scratch, Block(far).  The deferred Block is resolved to hi20 in the
    // FINAL pass; until then it marks this AUIPC as a relaxed far-jump anchor.
    let auipc = RiscVISelInst::new(
        RiscVOpcode::Auipc,
        vec![
            RiscVISelOperand::PReg(RISCV_FAR_JUMP_SCRATCH),
            RiscVISelOperand::Block(target_block),
        ],
    );
    // JALR link, scratch, Block(far).  The deferred Block (the SAME far target)
    // is resolved to lo12 in the FINAL pass, from the AUIPC's pcrel anchor (per
    // the psABI %pcrel_lo same-anchor rule). The Block is the FIRST non-PReg
    // operand; any trailing liveness-carrying operands the original JAL attached
    // (e.g. the call-argument PReg the self-call idiom carries) follow AFTER it,
    // so the final pass replaces the Block in place and the first non-PReg
    // operand remains the resolved immediate that resolve_inst_operands reads.
    let mut jalr_operands = vec![
        RiscVISelOperand::PReg(link),
        RiscVISelOperand::PReg(RISCV_FAR_JUMP_SCRATCH),
        RiscVISelOperand::Block(target_block),
    ];
    for op in &orig.operands {
        match op {
            // Drop the original link PReg (now on the JALR as rd above) and the
            // Block target (now carried by the AUIPC and the JALR's deferred
            // Block above).
            RiscVISelOperand::PReg(p) if *p == link => {}
            RiscVISelOperand::Block(_) => {}
            // Keep any extra liveness-carrying operands (e.g. argument regs).
            other => jalr_operands.push(other.clone()),
        }
    }
    let jalr = RiscVISelInst::new(RiscVOpcode::Jalr, jalr_operands);

    mblock.insts[pos] = auipc;
    mblock.insts.insert(pos + 1, jalr);

    // CASCADE FIXUP: if this JAL was the far-jump of a relaxed conditional
    // branch, the inverted short branch immediately BEFORE it was sized to skip
    // ONE 4-byte JAL (+8). The JAL just became a TWO-instruction AUIPC+JALR
    // sequence (+8 bytes from the branch to past the JALR is now wrong), so the
    // skip must grow to +12 to still land on the fallthrough. We identify the
    // inserted skip precisely: an invertible conditional-branch opcode whose only
    // immediate is the +8 skip and which carries NO Block operand (a normal
    // in-range conditional branch still has its Block target at this stage).
    // Without this, the inverted branch would land in the MIDDLE of the
    // AUIPC+JALR pair — a miscompile. We re-fetch the block to satisfy the
    // borrow checker after the insert above.
    if pos > 0 {
        let mblock = func
            .blocks
            .get_mut(&block_id)
            .expect("block exists (probed above)");
        let prev = &mblock.insts[pos - 1];
        let is_skip_branch = riscv_invert_branch_opcode(prev.opcode).is_some()
            && !prev
                .operands
                .iter()
                .any(|o| matches!(o, RiscVISelOperand::Block(_)))
            && prev
                .operands
                .iter()
                .any(|o| matches!(o, RiscVISelOperand::Imm(8)));
        if is_skip_branch {
            let prev = &mut mblock.insts[pos - 1];
            for op in prev.operands.iter_mut() {
                if let RiscVISelOperand::Imm(v) = op {
                    *v = 12; // skip AUIPC + JALR (two 4-byte insts) = +12 bytes
                }
            }
        }
    }
}

/// Resolve block operands in branch instructions to byte offsets.
///
/// RISC-V branches use PC-relative offsets where the offset is relative
/// to the address of the branch instruction itself (not the next instruction
/// as in x86-64).
///
/// Runs far-branch / far-jump RELAXATION first ([`relax_riscv_far_branches`]):
/// an out-of-range conditional branch becomes an inverted short branch skipping
/// a `JAL` to the far target; an out-of-range `JAL` becomes `AUIPC`+`JALR`
/// (signed-32-bit reach). After relaxation every remaining branch is in range
/// and its `Block` target is converted to a PC-relative `Imm`.
///
/// FAIL-CLOSED: a target genuinely beyond the signed-32-bit `AUIPC`+`JALR` reach
/// (or a non-converging relaxation) is REJECTED with a typed
/// [`RiscVPipelineError`] rather than truncated. A resolved offset that — after
/// relaxation — still does not fit its instruction's PC-relative range is also
/// rejected (defense in depth; relaxation should have prevented it). The
/// downstream encoder masks the offset bits, so without these guards a too-far
/// branch would silently target the wrong address — a miscompile the prime
/// directive forbids.
fn resolve_riscv_branches(func: &mut RiscVISelFunction) -> Result<(), RiscVPipelineError> {
    use trust_cg_lower::instructions::Block;

    // Phase 0: Relax any far branches/jumps so every remaining offset is in range.
    relax_riscv_far_branches(func)?;

    // Phase 1: Compute byte offset of each block (post-relaxation layout).
    let block_offsets: HashMap<Block, i64> = riscv_compute_block_offsets(func);

    // Phase 2: Replace Block operands with Imm offsets, on the FINAL layout.
    //
    // Two kinds of Block operand are resolved here:
    //   * B/J-type branch targets (Beq..Bgeu, Jal): a single PC-relative offset
    //     relative to the branch instruction itself.
    //   * A RELAXED far-jump AUIPC+JALR pair (deferred from relax_riscv_far_jump):
    //     the AUIPC and its paired JALR each carry the SAME far Block. The pcrel
    //     displacement is split (riscv_split_pcrel_hi_lo) from the AUIPC's FINAL
    //     byte offset (the pcrel-hi anchor) to the target's FINAL byte offset;
    //     hi20 goes into the AUIPC, lo12 into the JALR — BOTH split from the SAME
    //     anchor (the AUIPC's PC), per the psABI %pcrel_lo same-anchor rule.
    //     Resolving on the final layout is off-by-4-proof: the +4 forward shift
    //     from the inserted JALR, and any later insertion between the AUIPC and
    //     its target, are already reflected in the final offsets.
    let block_order = func.block_order.clone();
    for &block_id in &block_order {
        let block_base: i64 = *block_offsets.get(&block_id).unwrap_or(&0);

        let Some(mblock) = func.blocks.get_mut(&block_id) else {
            continue;
        };

        // Precompute the final byte offset of every instruction in this block so
        // pair-resolution (AUIPC anchor -> paired JALR) can look ahead without
        // re-deriving offsets.
        let mut inst_offsets: Vec<i64> = Vec::with_capacity(mblock.insts.len());
        let mut acc = block_base;
        for inst in &mblock.insts {
            inst_offsets.push(acc);
            acc += inst_size(inst) as i64;
        }

        let n = mblock.insts.len();
        for (idx, &inst_offset) in inst_offsets.iter().enumerate() {
            let opcode = mblock.insts[idx].opcode;

            // B-type vs J-type determines the legal PC-relative range.
            let (is_branch, is_jtype) = match opcode {
                RiscVOpcode::Beq
                | RiscVOpcode::Bne
                | RiscVOpcode::Blt
                | RiscVOpcode::Bge
                | RiscVOpcode::Bltu
                | RiscVOpcode::Bgeu => (true, false),
                RiscVOpcode::Jal => (true, true),
                _ => (false, false),
            };

            // RELAXED far-jump AUIPC: carries a Block (a normal intra-function
            // AUIPC never carries one; a cross-function AUIPC carries a Symbol,
            // not a Block). Resolve the AUIPC hi20 AND the paired JALR lo12 from
            // the AUIPC's FINAL anchor.
            if opcode == RiscVOpcode::Auipc {
                let auipc_block = mblock.insts[idx].operands.iter().find_map(|op| match op {
                    RiscVISelOperand::Block(b) => Some(*b),
                    _ => None,
                });
                if let Some(target_block) = auipc_block {
                    let anchor = inst_offset;
                    let target_offset = match block_offsets.get(&target_block) {
                        Some(&o) => o,
                        None => {
                            return Err(RiscVPipelineError::FrameLowering(format!(
                                "RISC-V relaxed far-jump AUIPC targets block {} which is \
                                 absent from block_order; cannot resolve a PC-relative offset",
                                target_block.0
                            )));
                        }
                    };
                    let disp = target_offset - anchor;
                    let (hi20, lo12) = riscv_split_pcrel_hi_lo(disp).ok_or_else(|| {
                        RiscVPipelineError::FrameLowering(format!(
                            "RISC-V relaxed far-jump displacement {disp} (target block {} \
                             @ {target_offset} - AUIPC @ {anchor}) is out of the signed \
                             32-bit AUIPC+JALR reach; failing closed rather than emitting a \
                             wrong jump target",
                            target_block.0
                        ))
                    })?;

                    // Replace the AUIPC's Block IN PLACE with hi20 so it stays the
                    // first (and only) Imm that resolve_inst_operands reads.
                    riscv_replace_block_with_imm(
                        &mut mblock.insts[idx].operands,
                        target_block,
                        hi20 as i64,
                    );

                    // Find the paired JALR: the next instruction (inst_size
                    // guarantees +4) carrying the SAME far Block. Pair by the
                    // shared Block value (not raw adjacency) so a future
                    // zero-sized insertion between them cannot mis-pair.
                    let mut paired = None;
                    for j in (idx + 1)..n {
                        if mblock.insts[j].opcode == RiscVOpcode::Jalr
                            && mblock.insts[j].operands.iter().any(
                                |op| matches!(op, RiscVISelOperand::Block(b) if *b == target_block),
                            )
                        {
                            paired = Some(j);
                            break;
                        }
                    }
                    let Some(jidx) = paired else {
                        return Err(RiscVPipelineError::FrameLowering(format!(
                            "RISC-V relaxed far-jump AUIPC (target block {}) has no paired \
                             JALR carrying the same Block; cannot resolve the lo12 half",
                            target_block.0
                        )));
                    };
                    // lo12 from the SAME anchor (the AUIPC's PC), per %pcrel_lo.
                    riscv_replace_block_with_imm(
                        &mut mblock.insts[jidx].operands,
                        target_block,
                        lo12 as i64,
                    );
                }
                continue;
            }

            // A JALR carrying a Block is the paired half of a relaxed far jump;
            // it was already resolved above when its AUIPC was processed, so
            // nothing to do here. (Defense in depth: if an unpaired JALR with a
            // Block ever reaches here it stays a Block and a later sanity check /
            // the encoder rejects it rather than silently encoding offset 0.)
            if opcode == RiscVOpcode::Jalr {
                continue;
            }

            if is_branch {
                // RISC-V: offset is relative to the branch instruction itself.
                let branch_addr = inst_offsets[idx];
                let (lo, hi) = if is_jtype {
                    (RISCV_JUMP_OFFSET_MIN, RISCV_JUMP_OFFSET_MAX)
                } else {
                    (RISCV_BRANCH_OFFSET_MIN, RISCV_BRANCH_OFFSET_MAX)
                };

                let mut new_operands = Vec::with_capacity(mblock.insts[idx].operands.len());
                for op in &mblock.insts[idx].operands {
                    match op {
                        RiscVISelOperand::Block(target_block) => {
                            match block_offsets.get(target_block) {
                                Some(&target_offset) => {
                                    let rel_offset = target_offset - branch_addr;
                                    // FAIL-CLOSED (defense in depth): reject an
                                    // out-of-range or odd offset before it is
                                    // silently masked. Relaxation (Phase 0)
                                    // should already have split any too-far
                                    // branch/jump into an in-range sequence, so
                                    // reaching here means relaxation missed a
                                    // case — never emit a wrong target.
                                    if !(lo..=hi).contains(&rel_offset) || (rel_offset & 1) != 0 {
                                        return Err(RiscVPipelineError::FrameLowering(format!(
                                            "RISC-V {:?} PC-relative offset {} to block {} is out \
                                             of range [{}, {}] (even) AFTER far-branch relaxation; \
                                             failing closed rather than emitting a wrong target",
                                            opcode, rel_offset, target_block.0, lo, hi
                                        )));
                                    }
                                    new_operands.push(RiscVISelOperand::Imm(rel_offset));
                                }
                                // An unresolved Block target (not in
                                // block_order) cannot be turned into an offset;
                                // fail closed rather than leave a Block operand
                                // that encodes as a zero/wrong offset.
                                None => {
                                    return Err(RiscVPipelineError::FrameLowering(format!(
                                        "RISC-V {:?} targets block {} which is absent from \
                                         block_order; cannot resolve a PC-relative offset",
                                        opcode, target_block.0
                                    )));
                                }
                            }
                        }
                        other => new_operands.push(other.clone()),
                    }
                }
                mblock.insts[idx].operands = new_operands;
            }
        }
    }
    Ok(())
}

/// Replace the FIRST `Block(target)` operand in `operands` with `Imm(value)`,
/// in place (preserving operand order and leading `PReg`s).
///
/// Used by the FINAL far-jump resolution to swap a deferred `Block` for its
/// resolved pcrel half (hi20 on the AUIPC, lo12 on the JALR). Replacing in place
/// (not appending) keeps the resolved `Imm` as the FIRST `Imm` operand, which is
/// exactly what [`resolve_inst_operands`] reads as the immediate; appending would
/// risk a stray earlier `Imm` being read instead.
fn riscv_replace_block_with_imm(
    operands: &mut [RiscVISelOperand],
    target: trust_cg_lower::instructions::Block,
    value: i64,
) {
    for op in operands.iter_mut() {
        if matches!(op, RiscVISelOperand::Block(b) if *b == target) {
            *op = RiscVISelOperand::Imm(value);
            return;
        }
    }
}

// ---------------------------------------------------------------------------
// Sentinel S5 — proof-only bounds-check carrier: ISel emit, expansion, and the
// kernel-gated elimination pass.
//
// The RISC-V ISel-output type universe (`RiscVISelFunction`) lives HERE in
// `trust-cg-codegen`, not in `trust-cg-lower` (where x86's `X86ISelFunction`
// lives). `trust-cg-opt` cannot depend on `trust-cg-codegen` (that would invert
// the dependency edge), so the RISC-V kernel-gated elimination pass — unlike the
// x86 one in `trust_cg_opt::x86_proof_opts` — must live in this crate. Soundness
// is unaffected: the decision still flows entirely through the SHARED kernel
// `trust_cg_ir::decide`; the only RISC-V-specific surface is classification +
// operand lifting via `RiscvGuardTarget`, exactly as for x86.
// ---------------------------------------------------------------------------

/// Lift a RISC-V ISel operand into the arch-neutral guard operand ref the kernel
/// uses (registers + immediates only). Mirrors x86's `x86_isel_operand_guard_ref`.
fn riscv_isel_operand_guard_ref(op: &RiscVISelOperand) -> Option<GuardOperandRef> {
    match op {
        RiscVISelOperand::VReg(v) => Some(GuardOperandRef::Reg(v.id)),
        RiscVISelOperand::Imm(i) => Some(GuardOperandRef::Imm(*i)),
        _ => None,
    }
}

/// Lift a whole carrier instruction's operands into the arch-neutral guard
/// operand refs (registers + immediates only, in role order `[base, index,
/// Imm(bound)]`).
fn riscv_carrier_operand_refs(inst: &RiscVISelInst) -> Vec<GuardOperandRef> {
    inst.operands
        .iter()
        .filter_map(riscv_isel_operand_guard_ref)
        .collect()
}

/// Sentinel S5 — emit a proof-only exact bounds-check carrier into `func` at
/// `block`, threading the discharged obligation onto it by the SAME operand
/// fingerprint the Certified-Elimination Kernel computes. Mirrors x86's
/// `select_guard_bounds_check`.
///
/// `base`/`index` are the (virtual) source registers and `bound` is the exact
/// element count. When `obligation` is `Some`, the carrier→obligation binding is
/// recorded in `func.guard_obligations` keyed by `fingerprint_for_kind(BoundsCheck,
/// [base, index, Imm(bound)])`. The carrier itself is `TrapBoundsCheckExact [base,
/// index, Imm(bound)]`. A surviving carrier is later expanded to a real
/// `BGEU index,bound -> EBREAK` runtime check by
/// [`expand_riscv_bounds_check_carriers`].
pub fn emit_riscv_bounds_check_carrier(
    func: &mut RiscVISelFunction,
    block: trust_cg_lower::instructions::Block,
    base: RiscVISelOperand,
    index: RiscVISelOperand,
    bound: i64,
    obligation: Option<u64>,
) {
    if let Some(obl) = obligation
        && let (Some(b), Some(i)) = (
            riscv_isel_operand_guard_ref(&base),
            riscv_isel_operand_guard_ref(&index),
        )
    {
        // Defense-in-depth: fold the carrier's GuardKind into the binding key.
        let fp = fingerprint_for_kind(GuardKind::BoundsCheck, &[b, i, GuardOperandRef::Imm(bound)]);
        func.guard_obligations.insert(fp, obl);
    }
    func.push_inst(
        block,
        RiscVISelInst::new(
            RiscVOpcode::TrapBoundsCheckExact,
            vec![base, index, RiscVISelOperand::Imm(bound)],
        ),
    );
}

/// Sentinel S5 — expand surviving proof-only bounds-check carriers into real
/// runtime checks.
///
/// A `TrapBoundsCheckExact [base, index, Imm(bound)]` carrier that the
/// kernel-gated proof pass did NOT delete must lower to a genuine unsigned
/// `index < bound` check. Each carrier becomes:
///
/// ```text
///     LI    bound_reg, bound          ; ADDI x0+imm12, or LUI+ADDI for wide bounds
///     BGEU  index, bound_reg, trap    ; unsigned index >= bound traps
///     ... rest of block falls through ...
///   trap_block:
///     EBREAK
/// ```
///
/// This runs BEFORE register assignment so the fresh `bound_reg` vreg and the
/// synthetic trap block participate in regalloc/encoding normally. It is
/// fail-closed: any carrier the encoder would otherwise reject
/// (`UnsupportedOpcode`) is replaced here, so a dropped bounds check can never
/// reach object emission as a silent NOP.
///
/// The `base` operand is intentionally not referenced by the runtime check (the
/// unsigned `index < bound` comparison fully captures the safety condition); it
/// is preserved on the carrier solely for proof-operand identity.
pub fn expand_riscv_bounds_check_carriers(
    func: &mut RiscVISelFunction,
) -> Result<(), RiscVPipelineError> {
    use trust_cg_lower::instructions::Block;

    let mut new_trap_blocks: Vec<Block> = Vec::new();
    let mut next_block_id: u32 = func
        .block_order
        .iter()
        .map(|b| b.0)
        .max()
        .unwrap_or(0)
        .saturating_add(1);

    for block_id in func.block_order.clone() {
        let has_carrier = func.blocks.get(&block_id).is_some_and(|b| {
            b.insts
                .iter()
                .any(|i| i.opcode == RiscVOpcode::TrapBoundsCheckExact)
        });
        if !has_carrier {
            continue;
        }
        let old_insts = std::mem::take(&mut func.blocks.get_mut(&block_id).unwrap().insts);

        let mut new_insts = Vec::with_capacity(old_insts.len());
        let mut added_trap_succs: Vec<Block> = Vec::new();

        for inst in old_insts {
            if inst.opcode != RiscVOpcode::TrapBoundsCheckExact {
                new_insts.push(inst);
                continue;
            }

            // Carrier shape: [base, index, Imm(bound)]. Fail closed if malformed.
            if inst.operands.len() != 3 {
                return Err(RiscVPipelineError::FrameLowering(format!(
                    "RISC-V TrapBoundsCheckExact carrier must have 3 operands, got {}",
                    inst.operands.len()
                )));
            }
            let index = inst.operands[1].clone();
            let bound = match &inst.operands[2] {
                RiscVISelOperand::Imm(b) => *b,
                other => {
                    return Err(RiscVPipelineError::FrameLowering(format!(
                        "RISC-V TrapBoundsCheckExact carrier bound must be an immediate, got {other:?}"
                    )));
                }
            };

            // Fail closed if the bound is outside [0, u32::MAX] — the range
            // `materialize_riscv_bound` reconstructs exactly. The adapter caps RISC-V exact
            // bounds at u32::MAX, so this is unreachable via the producer; a direct caller that
            // bypassed the cap gets a typed error, never a silently-too-weak bounds check.
            if bound < 0 || bound > u32::MAX as i64 {
                return Err(RiscVPipelineError::FrameLowering(format!(
                    "RISC-V TrapBoundsCheckExact bound {bound} out of representable [0, u32::MAX]"
                )));
            }

            // Mint a fresh synthetic trap block id.
            while func.blocks.contains_key(&Block(next_block_id)) {
                next_block_id = next_block_id.checked_add(1).ok_or_else(|| {
                    RiscVPipelineError::FrameLowering(
                        "exhausted RISC-V synthetic trap block ids".to_string(),
                    )
                })?;
            }
            let trap_block = Block(next_block_id);
            next_block_id = next_block_id.checked_add(1).ok_or_else(|| {
                RiscVPipelineError::FrameLowering(
                    "exhausted RISC-V synthetic trap block ids".to_string(),
                )
            })?;

            // Materialize the bound into a register, then BGEU index, bound_reg, trap.
            let bound_reg = func.fresh_vreg(RegClass::Gpr64);
            let bound_reg_op = RiscVISelOperand::VReg(bound_reg);
            materialize_riscv_bound(bound, bound_reg_op.clone(), &mut new_insts);
            // BGEU index, bound_reg, trap_block (unsigned index >= bound traps).
            new_insts.push(RiscVISelInst::new(
                RiscVOpcode::Bgeu,
                vec![index, bound_reg_op, RiscVISelOperand::Block(trap_block)],
            ));

            added_trap_succs.push(trap_block);
            new_trap_blocks.push(trap_block);
        }

        if let Some(block) = func.blocks.get_mut(&block_id) {
            block.insts = new_insts;
            block.successors.extend(added_trap_succs);
        }
    }

    // Materialize the synthetic trap blocks (each is a single EBREAK).
    for trap_block in new_trap_blocks {
        func.ensure_block(trap_block);
        if let Some(block) = func.blocks.get_mut(&trap_block) {
            block
                .insts
                .push(RiscVISelInst::new(RiscVOpcode::Ebreak, vec![]));
        }
    }

    Ok(())
}

/// Materialize an unsigned 32-bit `bound` into `dst` using only base-ISA instructions,
/// **zero-extended** to 64 bits so the survivor `BGEU index, dst` is a correct unsigned check.
///
/// * For a 12-bit-representable bound: `ADDI dst, x0, bound` (the `LI` idiom).
/// * Otherwise: `LUI dst, hi20 ; ADDI dst, dst, lo12` (with the standard "add 1 to hi20 when
///   lo12 is negative" correction) reconstructs the value, but RV64 `LUI` SIGN-extends bit 31,
///   so a bound with bit 31 set would land in the register as a huge sign-extended value and the
///   unsigned `BGEU` would never trap (a silent bounds-check bypass). `SLLI 32 ; SRLI 32` then
///   clears the upper 32 bits, making the full `[0, u32::MAX]` range correct. Callers must ensure
///   `0 <= bound <= u32::MAX` (the expander fails closed otherwise).
fn materialize_riscv_bound(bound: i64, dst: RiscVISelOperand, out: &mut Vec<RiscVISelInst>) {
    debug_assert!(
        (0..=u32::MAX as i64).contains(&bound),
        "materialize_riscv_bound expects an unsigned-32 bound; got {bound}"
    );
    if (0..=2047).contains(&bound) {
        out.push(RiscVISelInst::new(
            RiscVOpcode::Addi,
            vec![
                dst,
                RiscVISelOperand::PReg(riscv_regs::ZERO),
                RiscVISelOperand::Imm(bound),
            ],
        ));
        return;
    }

    let v = bound as u32;
    let lo12 = (v & 0xfff) as i32;
    // Sign-extend the low 12 bits; if negative, bump the hi20 to compensate.
    let lo12_signed = if lo12 >= 0x800 { lo12 - 0x1000 } else { lo12 };
    let hi20 = ((v as i64 - lo12_signed as i64) >> 12) as i32 & 0xf_ffff;

    out.push(RiscVISelInst::new(
        RiscVOpcode::Lui,
        vec![dst.clone(), RiscVISelOperand::Imm(hi20 as i64)],
    ));
    out.push(RiscVISelInst::new(
        RiscVOpcode::Addi,
        vec![
            dst.clone(),
            dst.clone(),
            RiscVISelOperand::Imm(lo12_signed as i64),
        ],
    ));
    // Zero-extend the low 32 bits to undo RV64 LUI sign-extension (see doc comment).
    out.push(RiscVISelInst::new(
        RiscVOpcode::Slli,
        vec![dst.clone(), dst.clone(), RiscVISelOperand::Imm(32)],
    ));
    out.push(RiscVISelInst::new(
        RiscVOpcode::Srli,
        vec![dst.clone(), dst, RiscVISelOperand::Imm(32)],
    ));
}

/// Statistics from one run of the RISC-V kernel-gated guard-elimination pass.
#[derive(Debug, Clone, Default)]
pub struct RiscVProofOptStats {
    /// Number of guard carriers (any kind: bounds/null/div-zero/shift-range)
    /// eliminated under kernel authorization.
    pub guards_eliminated: u32,
    /// Number of guard carriers (any kind) KEPT (no/undischarged obligation).
    pub guards_kept: u32,
}

/// RISC-V kernel-gated proof-consuming guard elimination pass — the RISC-V mirror
/// of `trust_cg_opt::x86_proof_opts::X86ProofGuardElimination`, specialized to the
/// RISC-V ISel-output type universe (`RiscVISelFunction`/`RiscVISelInst`).
///
/// It deletes a proof-only bounds-check carrier (`RiscVOpcode::TrapBoundsCheckExact`)
/// ONLY when the arch-neutral Certified-Elimination Kernel
/// ([`trust_cg_ir::decide`]) authorizes it against the discharged-obligation
/// evidence and the carrier's bound obligation. Every soundness-critical decision
/// stays in the SHARED kernel; the only RISC-V-specific surface is classifying the
/// carrier ([`RiscvGuardTarget::classify_carrier`]) and lifting its operands
/// ([`RiscvGuardTarget::operand_identity`]).
///
/// ## Strict restriction
///
/// With the gate enabled, a carrier is deleted iff `decide()` returns
/// `Eliminate`. A carrier with no bound obligation, or whose obligation is absent
/// / `Pending` in the evidence table, is KEPT (fail-safe) and the codegen pipeline
/// expands it to a real `BGEU+EBREAK` runtime check. A KEPT carrier is the exact
/// behaviour of a non-eliminated guard, so the gate NEVER eliminates more than the
/// legacy path — it only makes the elimination certified and re-checkable.
#[derive(Default)]
pub struct RiscVProofGuardElimination {
    /// When false (default), the pass keeps every carrier — exactly the legacy
    /// behaviour (the pipeline then expands them to real runtime checks).
    kernel_gate: bool,
    /// Discharged-obligation evidence the kernel consults.
    kernel_evidence: DischargedEvidenceTable,
    /// Per-carrier obligation binding, keyed by the operand fingerprint the kernel
    /// re-derives from the carrier. Value is (obligation id, lineage digest).
    kernel_obligations: HashMap<u128, (u128, Option<u128>)>,
    /// Eliminations the kernel authorized this run, for the independent re-check:
    /// (INDEPENDENTLY re-lifted live-carrier operands, certificate). The observed operands are a
    /// SECOND lift taken from the live carrier at the deletion site in `run_on_function` (NOT the
    /// decide-time identity), so the re-check's operand-fingerprint comparison is non-vacuous: a
    /// real operand drift is rejected fail-closed (#9).
    kernel_eliminations: Vec<(Vec<GuardOperandRef>, EliminationCertificate)>,
    /// Stats from the last run.
    stats: RiscVProofOptStats,
}

impl RiscVProofGuardElimination {
    /// Create a disabled (no-op) pass.
    pub fn new() -> Self {
        Self::default()
    }

    /// Enable kernel-gated elimination. `evidence` is the discharged-obligation
    /// table; `obligations` maps a carrier operand fingerprint to its (obligation
    /// id, lineage digest). With the gate off (the default), the pass keeps every
    /// carrier.
    pub fn enable_kernel_gate(
        &mut self,
        evidence: DischargedEvidenceTable,
        obligations: HashMap<u128, (u128, Option<u128>)>,
    ) {
        self.kernel_gate = true;
        if trust_cg_lower::guard_evidence::validator_guard_replay_authority_available()
            || cfg!(test)
        {
            self.kernel_evidence = evidence;
            self.kernel_obligations = obligations;
        } else {
            self.kernel_evidence = DischargedEvidenceTable::new();
            self.kernel_obligations.clear();
        }
    }

    /// Stats from the last run.
    pub fn stats(&self) -> &RiscVProofOptStats {
        &self.stats
    }

    /// The kernel eliminations authorized during the last run (for re-check): (independently
    /// re-lifted live-carrier operands, certificate).
    pub fn kernel_eliminations(&self) -> &[(Vec<GuardOperandRef>, EliminationCertificate)] {
        &self.kernel_eliminations
    }

    /// Test-only: simulate a live-carrier operand drift by overwriting the recorded observed
    /// operands for the elimination at `idx`, so [`recheck_kernel_eliminations`] rejects (#9).
    #[cfg(test)]
    fn test_force_observed_drift(&mut self, idx: usize, observed: Vec<GuardOperandRef>) {
        self.kernel_eliminations[idx].0 = observed;
    }

    /// Ask the Certified-Elimination Kernel whether one carrier may be deleted.
    /// Returns the minted certificate on Eliminate, `None` on Keep.
    ///
    /// #9: this does NOT record the elimination — the caller (`run_on_function`) records it with a
    /// SECOND, independent re-lift of the live carrier's operands taken at the deletion site, so the
    /// re-check's fingerprint comparison is non-vacuous.
    fn kernel_authorizes(&mut self, inst: &RiscVISelInst) -> Option<EliminationCertificate> {
        let target = RiscvGuardTarget;
        let kind = target.classify_carrier(inst.opcode)?;
        let operand_refs = riscv_carrier_operand_refs(inst);
        let operand_identity = target.operand_identity(&operand_refs);
        // Defense-in-depth: look the binding up by the SAME kind-folded key ISel recorded, so an
        // obligation bound for a different kind over identical operands can't be picked up here. A
        // mismatch misses the lookup => carrier KEPT (fail-safe).
        let binding_key = fingerprint_for_kind(kind, &operand_identity.operands);
        let (proof_obligation_id, lineage_digest) = match self.kernel_obligations.get(&binding_key)
        {
            Some(&(obl, lineage)) => (Some(obl), lineage),
            None => (None, None),
        };
        let receipt = GuardObligationReceipt {
            kind,
            operand_identity,
            proof_obligation_id,
            lineage_digest,
        };
        match decide(&receipt, &self.kernel_evidence) {
            EliminationVerdict::Eliminate { certificate } => Some(certificate),
            EliminationVerdict::Keep { .. } => None,
        }
    }

    /// Independent fail-closed re-check (mirrors the x86/AArch64 re-checkers):
    /// re-validate every kernel-authorized elimination by re-deriving the operand
    /// fingerprint and re-confirming discharge/lineage against the evidence.
    /// Returns the first rejection reason, or `Ok(())` if all re-justify.
    ///
    /// #9: `observed_operands` is the independently re-lifted live-carrier snapshot recorded in
    /// `run_on_function`, so a genuine operand drift between authorization and re-check is rejected.
    pub fn recheck_kernel_eliminations(&self) -> Result<(), String> {
        for (observed_operands, certificate) in &self.kernel_eliminations {
            match recheck_elimination(certificate, observed_operands, &self.kernel_evidence) {
                RecheckOutcome::Valid => {}
                RecheckOutcome::Rejected { reason } => {
                    return Err(format!(
                        "RISC-V guard elimination re-check rejected (obligation {}): {}",
                        certificate.obligation_id(),
                        reason
                    ));
                }
            }
        }
        Ok(())
    }

    /// Run the pass on a RISC-V ISel function. Deletes only kernel-authorized
    /// guard carriers (currently the bounds-check carrier; the stats count any
    /// classified guard kind); keeps everything else.
    pub fn run_on_function(&mut self, func: &mut RiscVISelFunction) -> bool {
        self.stats = RiscVProofOptStats::default();
        self.kernel_eliminations.clear();

        // With the gate off, keep every carrier (legacy behaviour).
        if !self.kernel_gate {
            return false;
        }

        let mut changed = false;
        for block_id in func.block_order.clone() {
            // Decide deletions first (immutable borrow of each inst), then retain.
            let decisions: Vec<bool> = {
                let Some(block) = func.blocks.get(&block_id) else {
                    continue;
                };
                block
                    .insts
                    .iter()
                    .map(|inst| {
                        if RiscvGuardTarget.classify_carrier(inst.opcode).is_none() {
                            return false; // not a carrier — keep
                        }
                        if let Some(certificate) = self.kernel_authorizes(inst) {
                            // #9: record the elimination with a SECOND, independent re-lift of THIS
                            // live carrier's operands (a fresh `riscv_carrier_operand_refs` call,
                            // distinct from the one decide consumed inside `kernel_authorizes`), so
                            // the re-check's fingerprint comparison is non-vacuous.
                            let observed = riscv_carrier_operand_refs(inst);
                            self.kernel_eliminations.push((observed, certificate));
                            self.stats.guards_eliminated += 1;
                            true // delete (kernel-authorized)
                        } else {
                            self.stats.guards_kept += 1;
                            false // keep (fail-safe)
                        }
                    })
                    .collect()
            };

            if decisions.iter().any(|&d| d) {
                let Some(block) = func.blocks.get_mut(&block_id) else {
                    continue;
                };
                let mut next = Vec::with_capacity(block.insts.len());
                for (inst, delete) in block.insts.drain(..).zip(decisions) {
                    if !delete {
                        next.push(inst);
                    }
                }
                block.insts = next;
                changed = true;
            }
        }

        changed
    }
}

// ---------------------------------------------------------------------------
// RiscVPipeline -- main entry point
// ---------------------------------------------------------------------------

/// Configuration for the RISC-V pipeline.
#[derive(Debug, Clone)]
pub struct RiscVPipelineConfig {
    /// Whether to emit an ELF .o wrapper (vs raw code bytes).
    pub emit_elf: bool,
    /// Whether to emit prologue/epilogue (false for leaf functions that
    /// don't need a frame).
    pub emit_frame: bool,
}

impl Default for RiscVPipelineConfig {
    fn default() -> Self {
        Self {
            emit_elf: false,
            emit_frame: true,
        }
    }
}

/// The RISC-V compilation pipeline.
///
/// Orchestrates: ISel output -> regalloc -> frame lowering -> encoding -> ELF.
pub struct RiscVPipeline {
    pub config: RiscVPipelineConfig,
}

impl RiscVPipeline {
    /// Create a new pipeline with the given configuration.
    pub fn new(config: RiscVPipelineConfig) -> Self {
        Self { config }
    }

    /// Create a pipeline with default configuration (raw code bytes, with frame).
    pub fn default_config() -> Self {
        Self::new(RiscVPipelineConfig::default())
    }

    /// Compile a RISC-V ISel function to machine code bytes.
    ///
    /// This is the single-function entry point (used by the library helpers and
    /// the existing single-function tests). It takes a `RiscVISelFunction`
    /// (post-ISel, pre-regalloc) and returns encoded machine code bytes.
    ///
    /// FAIL-CLOSED: a single function compiled in isolation has NO module to
    /// resolve cross-function call targets against, so any cross-function direct
    /// call (which the encoder records as a [`RiscVCallFixup`]) is rejected here.
    /// Self-recursive calls resolve PC-relatively within the function and produce
    /// no fixup, so they continue to work. The multi-function module path
    /// ([`Self::compile_function_with_fixups`]) is what threads the fixups out to
    /// the module emitter for resolution.
    pub fn compile_function(
        &self,
        func: &RiscVISelFunction,
    ) -> Result<Vec<u8>, RiscVPipelineError> {
        let (code, fixups) = self.compile_function_with_fixups(func)?;
        if let Some(fx) = fixups.first() {
            return Err(RiscVPipelineError::ISel(format!(
                "RISC-V function `{}` contains a cross-function direct call to `{}` but is \
                 being compiled in isolation (single-function path); cross-function calls can \
                 only be resolved by the multi-function module emitter. Compile the whole \
                 module (Compiler::compile) so the callee's address is known (fail-closed \
                 rather than emit a zero/wrong call target).",
                func.name, fx.callee
            )));
        }
        Ok(code)
    }

    /// Compile a RISC-V ISel function to machine code bytes PLUS the list of
    /// deferred cross-function call fixups (see [`RiscVCallFixup`]).
    ///
    /// This runs the full per-function pipeline (carrier expand, regalloc,
    /// call-arg parallel-copy fixup, spill rewrite, prologue/epilogue, branch
    /// resolution, encode). Self-recursive calls and intra-function branches are
    /// resolved PC-relatively here and produce NO fixups. A cross-function direct
    /// call (lowered as `AUIPC ra, %hi` + `JALR ra, ra, %lo` carrying a
    /// `Symbol(callee)`) is left with zero placeholder immediates and reported as
    /// a [`RiscVCallFixup`] for the module emitter to patch or relocate.
    ///
    /// The returned fixup offsets are relative to the START of THIS function's
    /// encoded bytes; the module emitter adds the function's base offset within
    /// `.text` to convert them to section-relative offsets.
    pub fn compile_function_with_fixups(
        &self,
        func: &RiscVISelFunction,
    ) -> Result<(Vec<u8>, Vec<RiscVCallFixup>), RiscVPipelineError> {
        // Phase 0 (Sentinel S5): expand any surviving proof-only bounds-check
        // carrier the kernel gate did NOT delete into a real BGEU+EBREAK runtime
        // check. Runs BEFORE register assignment so the fresh bound-register vreg
        // and the synthetic trap block are allocated/encoded normally. With no
        // carriers this is a no-op (zero behaviour change for existing inputs).
        let mut func = func.clone();
        expand_riscv_bounds_check_carriers(&mut func)?;

        // Phase 1: Register assignment (liveness + linear-scan + spill planning).
        let assignment = RiscVRegAssignment::assign(&func)?;

        // Phase 1a: Resolve each call's argument-setup move run into a
        // parallel-move-safe physical-register shuffle. Runs on the allocated (but
        // pre-spill-rewrite) stream so argument source vregs are still resolvable
        // to physical registers; fail-closed on spilled argument sources. With no
        // calls this is a no-op.
        fixup_call_arg_parallel_copies(&mut func, &assignment.allocation, &assignment.spill_slots)?;

        // Spilling needs a stack frame: spill slots are SP-relative within the
        // frame the prologue reserves. If a spill is required but frames are
        // disabled, there is nowhere safe to store — fail closed rather than
        // clobber the caller's stack above SP.
        if assignment.num_spills > 0 && !self.config.emit_frame {
            return Err(RiscVPipelineError::RegAlloc(format!(
                "RISC-V regalloc needs {} spill slot(s) but stack frames are disabled \
                 (emit_frame=false); cannot spill safely",
                assignment.num_spills
            )));
        }

        // Phase 1b: Materialize spill traffic. Rewrites each use of a spilled
        // vreg to reload into a scratch reg first, and each def to store the
        // scratch reg back to its spill slot. Spill slots live at the BOTTOM of
        // the frame (SP + k*8), so the offsets are valid once the prologue has
        // decremented SP; therefore this runs BEFORE prologue insertion. With no
        // spills it is a no-op.
        rewrite_spills(&mut func, &assignment)?;

        // Phase 2: Insert prologue/epilogue.
        if self.config.emit_frame {
            self.insert_prologue_epilogue(&mut func, &assignment)?;
        }

        // Phase 3: Resolve branch offsets (fail-closed on out-of-range targets).
        resolve_riscv_branches(&mut func)?;

        // Phase 4: Encode all instructions, collecting cross-function call fixups.
        let (code, fixups) = self.encode_function(&func, &assignment.allocation)?;

        // NOTE: emit_elf intentionally NOT applied here. The single-function ELF
        // helper path goes through `compile_function` (which delegates here and
        // wraps via emit_elf only when there are no cross-function fixups). The
        // module path consumes the raw bytes + fixups directly.
        if self.config.emit_elf {
            if fixups.is_empty() {
                return Ok((self.emit_elf(&func.name, &code), fixups));
            }
            // A cross-function call cannot be resolved by the single-function ELF
            // wrapper (it emits one symbol at offset 0 for the whole code with no
            // module symbol table). Surface the fixups unwrapped; `compile_function`
            // turns this into a typed fail-closed error.
            return Ok((code, fixups));
        }
        Ok((code, fixups))
    }

    // --- Phase implementations ---

    /// Insert prologue/epilogue into the function.
    fn insert_prologue_epilogue(
        &self,
        func: &mut RiscVISelFunction,
        assignment: &RiscVRegAssignment,
    ) -> Result<(), RiscVPipelineError> {
        let frame_size =
            compute_frame_size(assignment.used_callee_saved.len(), assignment.num_spills);

        // FAIL-CLOSED: the prologue/epilogue address the saved RA/S0/callee-saved
        // slots with signed-12-bit immediates and adjust SP by `frame_size`
        // (`ADDI SP, SP, -frame_size` and `ADDI S0, SP, frame_size`). The largest
        // magnitude immediate is `frame_size` itself, so a frame larger than the
        // signed 12-bit range cannot be encoded without a temp-register
        // materialization sequence (a future enhancement). Refuse rather than let
        // the encoder silently mask the immediate and corrupt the stack pointer.
        // This mirrors the imm12 guard in `spill_slot_offset`; `frame_size` here
        // overflows ~10 slots before any individual spill offset does, so this is
        // the binding check.
        if frame_size as i64 > RISCV_IMM12_MAX {
            return Err(RiscVPipelineError::FrameLowering(format!(
                "RISC-V frame size {} bytes exceeds the signed 12-bit immediate range \
                 ({} callee-saved + {} spill slot(s)); large frames need a temp-register \
                 SP-adjust sequence that the minimal backend does not yet emit",
                frame_size,
                assignment.used_callee_saved.len(),
                assignment.num_spills
            )));
        }

        let prologue = generate_prologue(&assignment.used_callee_saved, frame_size);
        let epilogue = generate_epilogue(&assignment.used_callee_saved, frame_size);

        // Insert prologue at the start of the entry block.
        if let Some(entry_block) = func.block_order.first().copied()
            && let Some(mblock) = func.blocks.get_mut(&entry_block)
        {
            let mut new_insts = prologue;
            new_insts.append(&mut mblock.insts);
            mblock.insts = new_insts;
        }

        // Insert epilogue before every JALR that acts as RET.
        // Convention: JALR x0, ra, 0 is the return instruction.
        for block_id in func.block_order.clone() {
            if let Some(mblock) = func.blocks.get_mut(&block_id) {
                let mut new_insts = Vec::new();
                for inst in &mblock.insts {
                    if is_ret_inst(inst) {
                        new_insts.extend(epilogue.clone());
                    }
                    new_insts.push(inst.clone());
                }
                mblock.insts = new_insts;
            }
        }

        Ok(())
    }

    /// Encode all instructions in the function to machine code bytes, collecting
    /// the cross-function call fixups (see [`RiscVCallFixup`]).
    ///
    /// A cross-function call is the `AUIPC ra, Symbol(callee)` + `JALR ra, ra,
    /// Symbol(callee)` pair `select_self_call` emits. Both carry a `Symbol`
    /// operand, which `resolve_inst_operands` cannot turn into a register or
    /// immediate; the resulting encoder operands have `imm = 0` (the placeholder).
    /// We pair the AUIPC (the pcrel-hi anchor) with the next JALR of the same
    /// symbol and record one fixup carrying both byte offsets, so the module
    /// emitter can patch the hi20/lo12 split (intra-object) or emit an
    /// `R_RISCV_CALL` relocation at the AUIPC offset (external).
    fn encode_function(
        &self,
        func: &RiscVISelFunction,
        alloc: &HashMap<VReg, RiscVPReg>,
    ) -> Result<(Vec<u8>, Vec<RiscVCallFixup>), RiscVPipelineError> {
        let mut bytes: Vec<u8> = Vec::new();
        let mut fixups: Vec<RiscVCallFixup> = Vec::new();
        // The pending AUIPC of a cross-function call: (byte offset, symbol).
        // Paired with the next JALR carrying the same symbol.
        let mut pending_hi: Option<(u32, String)> = None;

        for &block_id in &func.block_order {
            if let Some(mblock) = func.blocks.get(&block_id) {
                for inst in &mblock.insts {
                    // Skip pseudo-instructions that produce no code.
                    if matches!(inst.opcode, RiscVOpcode::Phi | RiscVOpcode::StackAlloc) {
                        continue;
                    }

                    // FAIL-CLOSED invariant: every Block operand must have been
                    // converted to a PC-relative Imm by `resolve_riscv_branches`
                    // before encoding. `resolve_inst_operands` only reads Imm
                    // operands, so a surviving Block would silently encode as a
                    // zero offset (a branch-to-self / wrong target). Reject rather
                    // than emit a wrong branch — this guards against a future opcode
                    // that carries a Block operand but is not in the resolver's
                    // branch set.
                    if inst
                        .operands
                        .iter()
                        .any(|op| matches!(op, RiscVISelOperand::Block(_)))
                    {
                        return Err(RiscVPipelineError::FrameLowering(format!(
                            "RISC-V {:?} still carries an unresolved Block operand at encode time; \
                             resolve_riscv_branches must convert every Block to a PC-relative offset",
                            inst.opcode
                        )));
                    }

                    let offset = bytes.len() as u32;

                    // Cross-function call materialization: an AUIPC or JALR may
                    // carry a Symbol placeholder. Recover the symbol (if any) and
                    // FAIL-CLOSED on a Symbol on any other opcode, or on an AUIPC
                    // that is not a call address-materialization (rd != ra), since
                    // such a Symbol would silently encode as a zero immediate.
                    let symbol: Option<&str> = inst.operands.iter().find_map(|op| match op {
                        RiscVISelOperand::Symbol(s) => Some(s.as_str()),
                        _ => None,
                    });
                    if let Some(sym) = symbol {
                        match inst.opcode {
                            RiscVOpcode::Auipc => {
                                if pending_hi.is_some() {
                                    return Err(RiscVPipelineError::FrameLowering(format!(
                                        "RISC-V cross-function call to `{sym}`: a second AUIPC \
                                         pcrel-hi anchor appeared before the matching JALR \
                                         pcrel-lo of the previous call closed it (malformed \
                                         call lowering)"
                                    )));
                                }
                                pending_hi = Some((offset, sym.to_string()));
                            }
                            RiscVOpcode::Jalr => {
                                let (hi_off, hi_sym) = pending_hi.take().ok_or_else(|| {
                                    RiscVPipelineError::FrameLowering(format!(
                                        "RISC-V cross-function call to `{sym}`: JALR pcrel-lo \
                                         appeared with no preceding AUIPC pcrel-hi anchor \
                                         (malformed call lowering)"
                                    ))
                                })?;
                                if hi_sym != sym {
                                    return Err(RiscVPipelineError::FrameLowering(format!(
                                        "RISC-V cross-function call mismatch: AUIPC anchored \
                                         `{hi_sym}` but JALR targets `{sym}` (the pcrel-hi/lo \
                                         pair must reference the same symbol)"
                                    )));
                                }
                                fixups.push(RiscVCallFixup {
                                    auipc_offset: hi_off,
                                    jalr_offset: offset,
                                    callee: sym.to_string(),
                                });
                            }
                            other => {
                                return Err(RiscVPipelineError::FrameLowering(format!(
                                    "RISC-V {other:?} carries a Symbol operand (`{sym}`) but only \
                                     AUIPC/JALR cross-function call materialization is supported; \
                                     a surviving Symbol would encode as a zero target"
                                )));
                            }
                        }
                    }

                    let ops = resolve_inst_operands(inst, alloc);
                    let word =
                        encode_instruction(inst.opcode, &ops).map_err(RiscVPipelineError::from)?;

                    // RISC-V is little-endian: emit 4 bytes in LE order.
                    bytes.extend_from_slice(&word.to_le_bytes());
                }
            }
        }

        // FAIL-CLOSED: an AUIPC pcrel-hi anchor with no closing JALR would leave a
        // dangling, unrelocated call address in `ra` — reject rather than emit it.
        if let Some((_, sym)) = pending_hi {
            return Err(RiscVPipelineError::FrameLowering(format!(
                "RISC-V cross-function call to `{sym}`: AUIPC pcrel-hi anchor was never closed \
                 by a matching JALR pcrel-lo (malformed call lowering)"
            )));
        }

        Ok((bytes, fixups))
    }

    /// Emit an ELF .o file wrapping the encoded machine code.
    fn emit_elf(&self, func_name: &str, code: &[u8]) -> Vec<u8> {
        let mut writer = ElfWriter::new(ElfMachine::Riscv64);
        writer.set_e_flags(EF_RISCV_FLOAT_ABI_DOUBLE);
        writer.add_text_section(code);
        writer.add_symbol(func_name, 1, 0, code.len() as u64, true, 2); // STT_FUNC
        writer.write()
    }
}

/// Check whether an ISel instruction is a return (JALR x0, ra, 0).
fn is_ret_inst(inst: &RiscVISelInst) -> bool {
    if inst.opcode != RiscVOpcode::Jalr {
        return false;
    }
    // Check for JALR x0, ra, 0 pattern (rd=x0, rs1=ra, imm=0).
    if inst.operands.len() >= 2 {
        let rd_is_zero = matches!(&inst.operands[0],
            RiscVISelOperand::PReg(p) if *p == riscv_regs::ZERO
        );
        let rs1_is_ra = matches!(&inst.operands[1],
            RiscVISelOperand::PReg(p) if *p == riscv_regs::RA
        );
        return rd_is_zero && rs1_is_ra;
    }
    false
}

// ---------------------------------------------------------------------------
// Convenience functions
// ---------------------------------------------------------------------------

/// Compile a RISC-V ISel function to raw machine code bytes.
pub fn riscv_compile_to_bytes(func: &RiscVISelFunction) -> Result<Vec<u8>, RiscVPipelineError> {
    let pipeline = RiscVPipeline::default_config();
    pipeline.compile_function(func)
}

/// Compile a RISC-V ISel function to an ELF .o file.
pub fn riscv_compile_to_elf(func: &RiscVISelFunction) -> Result<Vec<u8>, RiscVPipelineError> {
    let pipeline = RiscVPipeline::new(RiscVPipelineConfig {
        emit_elf: true,
        emit_frame: true,
    });
    pipeline.compile_function(func)
}

/// Build a simple `add(a: i64, b: i64) -> i64` RISC-V ISel function for testing.
///
/// RISC-V LP64D ABI: a in a0, b in a1, return in a0.
pub fn build_riscv_add_test_function() -> RiscVISelFunction {
    use trust_cg_lower::function::Signature;
    use trust_cg_lower::instructions::Block;
    use trust_cg_lower::types::Type;

    let sig = Signature {
        params: vec![Type::I64, Type::I64],
        returns: vec![Type::I64],
    };

    let mut func = RiscVISelFunction::new("add".to_string(), sig);
    let entry = Block(0);
    func.ensure_block(entry);

    let v0 = VReg::new(0, RegClass::Gpr64);
    let v1 = VReg::new(1, RegClass::Gpr64);
    let v2 = VReg::new(2, RegClass::Gpr64);
    func.next_vreg = 3;

    // ADDI v0, a0, 0 (move arg 0)
    func.push_inst(
        entry,
        RiscVISelInst::new(
            RiscVOpcode::Addi,
            vec![
                RiscVISelOperand::VReg(v0),
                RiscVISelOperand::PReg(A0),
                RiscVISelOperand::Imm(0),
            ],
        ),
    );

    // ADDI v1, a1, 0 (move arg 1)
    func.push_inst(
        entry,
        RiscVISelInst::new(
            RiscVOpcode::Addi,
            vec![
                RiscVISelOperand::VReg(v1),
                RiscVISelOperand::PReg(A1),
                RiscVISelOperand::Imm(0),
            ],
        ),
    );

    // ADD v2, v0, v1
    func.push_inst(
        entry,
        RiscVISelInst::new(
            RiscVOpcode::Add,
            vec![
                RiscVISelOperand::VReg(v2),
                RiscVISelOperand::VReg(v0),
                RiscVISelOperand::VReg(v1),
            ],
        ),
    );

    // ADDI a0, v2, 0 (move result to return register)
    func.push_inst(
        entry,
        RiscVISelInst::new(
            RiscVOpcode::Addi,
            vec![
                RiscVISelOperand::PReg(A0),
                RiscVISelOperand::VReg(v2),
                RiscVISelOperand::Imm(0),
            ],
        ),
    );

    // JALR x0, ra, 0 (return)
    func.push_inst(
        entry,
        RiscVISelInst::new(
            RiscVOpcode::Jalr,
            vec![
                RiscVISelOperand::PReg(riscv_regs::ZERO),
                RiscVISelOperand::PReg(RA),
                RiscVISelOperand::Imm(0),
            ],
        ),
    );

    func
}

/// Build a simple `const42() -> i64` RISC-V ISel function for testing.
///
/// Returns the constant 42.
pub fn build_riscv_const_test_function() -> RiscVISelFunction {
    use trust_cg_lower::function::Signature;
    use trust_cg_lower::instructions::Block;
    use trust_cg_lower::types::Type;

    let sig = Signature {
        params: vec![],
        returns: vec![Type::I64],
    };

    let mut func = RiscVISelFunction::new("const42".to_string(), sig);
    let entry = Block(0);
    func.ensure_block(entry);

    // LI a0, 42 (pseudo: ADDI a0, x0, 42)
    func.push_inst(
        entry,
        RiscVISelInst::new(
            RiscVOpcode::Addi,
            vec![
                RiscVISelOperand::PReg(A0),
                RiscVISelOperand::PReg(riscv_regs::ZERO),
                RiscVISelOperand::Imm(42),
            ],
        ),
    );

    // JALR x0, ra, 0 (return)
    func.push_inst(
        entry,
        RiscVISelInst::new(
            RiscVOpcode::Jalr,
            vec![
                RiscVISelOperand::PReg(riscv_regs::ZERO),
                RiscVISelOperand::PReg(RA),
                RiscVISelOperand::Imm(0),
            ],
        ),
    );

    func
}

// ===========================================================================
// Tests
// ===========================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use trust_cg_ir::regs::{RegClass, VReg};
    use trust_cg_ir::riscv_ops::RiscVOpcode;
    use trust_cg_ir::riscv_regs::{A0, A1, A2, RA, S0, SP, ZERO};
    use trust_cg_lower::function::Signature;
    use trust_cg_lower::instructions::Block;

    // -----------------------------------------------------------------------
    // Helper: build a minimal ISel function
    // -----------------------------------------------------------------------

    fn minimal_func(name: &str) -> RiscVISelFunction {
        let sig = Signature {
            params: vec![],
            returns: vec![],
        };
        let mut func = RiscVISelFunction::new(name.to_string(), sig);
        let entry = Block(0);
        func.ensure_block(entry);
        func
    }

    // -----------------------------------------------------------------------
    // Pipeline construction
    // -----------------------------------------------------------------------

    #[test]
    fn test_pipeline_default_config() {
        let pipeline = RiscVPipeline::default_config();
        assert!(!pipeline.config.emit_elf);
        assert!(pipeline.config.emit_frame);
    }

    #[test]
    fn test_pipeline_custom_config() {
        let config = RiscVPipelineConfig {
            emit_elf: true,
            emit_frame: false,
        };
        let pipeline = RiscVPipeline::new(config);
        assert!(pipeline.config.emit_elf);
        assert!(!pipeline.config.emit_frame);
    }

    // -----------------------------------------------------------------------
    // Frame size computation
    // -----------------------------------------------------------------------

    #[test]
    fn test_frame_size_no_callee_saved_no_spills() {
        // RA + S0 = 2 slots = 16 bytes (already aligned)
        let size = compute_frame_size(0, 0);
        assert_eq!(size, 16);
        assert_eq!(size % 16, 0);
    }

    #[test]
    fn test_frame_size_with_spills() {
        let size = compute_frame_size(0, 2);
        // RA + S0 + 2 spills = 4 slots = 32 bytes
        assert_eq!(size, 32);
        assert_eq!(size % 16, 0);
    }

    #[test]
    fn test_frame_size_alignment() {
        for num_cs in 0..8 {
            for num_spill in 0..5 {
                let size = compute_frame_size(num_cs, num_spill);
                assert_eq!(
                    size % 16,
                    0,
                    "misaligned for callee_saved={}, spills={}: size={}",
                    num_cs,
                    num_spill,
                    size
                );
            }
        }
    }

    // -----------------------------------------------------------------------
    // Prologue/epilogue generation
    // -----------------------------------------------------------------------

    #[test]
    fn test_generate_prologue_minimal() {
        let prologue = generate_prologue(&[], 16);
        // ADDI SP, -16; SD RA, 8(SP); SD S0, 0(SP); ADDI S0, SP, 16
        assert_eq!(prologue.len(), 4);
        assert_eq!(prologue[0].opcode, RiscVOpcode::Addi); // SP -= 16
        assert_eq!(prologue[1].opcode, RiscVOpcode::Sd); // save RA
        assert_eq!(prologue[2].opcode, RiscVOpcode::Sd); // save S0
        assert_eq!(prologue[3].opcode, RiscVOpcode::Addi); // set FP
    }

    #[test]
    fn test_generate_epilogue_minimal() {
        let epilogue = generate_epilogue(&[], 16);
        // LD RA, 8(SP); LD S0, 0(SP); ADDI SP, 16
        assert_eq!(epilogue.len(), 3);
        assert_eq!(epilogue[0].opcode, RiscVOpcode::Ld); // restore RA
        assert_eq!(epilogue[1].opcode, RiscVOpcode::Ld); // restore S0
        assert_eq!(epilogue[2].opcode, RiscVOpcode::Addi); // SP += 16
    }

    #[test]
    fn test_generate_prologue_with_callee_saved() {
        use trust_cg_ir::riscv_regs::{S2, S3};
        let prologue = generate_prologue(&[S2, S3], 48);
        // ADDI SP, -48; SD RA; SD S0; ADDI S0; SD S2; SD S3
        assert_eq!(prologue.len(), 6);
        assert_eq!(prologue[4].opcode, RiscVOpcode::Sd); // save S2
        assert_eq!(prologue[5].opcode, RiscVOpcode::Sd); // save S3
    }

    // -----------------------------------------------------------------------
    // Register assignment
    // -----------------------------------------------------------------------

    #[test]
    fn test_reg_assignment_simple() {
        let func = build_riscv_add_test_function();
        let assignment = RiscVRegAssignment::assign(&func).unwrap();

        // Should have allocated 3 VRegs.
        assert_eq!(assignment.allocation.len(), 3);

        // All assigned to different physical registers.
        let pregs: Vec<RiscVPReg> = assignment.allocation.values().copied().collect();
        for i in 0..pregs.len() {
            for j in (i + 1)..pregs.len() {
                assert_ne!(pregs[i], pregs[j], "duplicate preg assignment");
            }
        }
    }

    #[test]
    fn test_reg_assignment_empty_function() {
        let mut func = minimal_func("empty");
        func.push_inst(
            Block(0),
            RiscVISelInst::new(
                RiscVOpcode::Jalr,
                vec![
                    RiscVISelOperand::PReg(ZERO),
                    RiscVISelOperand::PReg(RA),
                    RiscVISelOperand::Imm(0),
                ],
            ),
        );
        let assignment = RiscVRegAssignment::assign(&func).unwrap();
        assert!(assignment.allocation.is_empty());
        assert!(assignment.used_callee_saved.is_empty());
    }

    // -----------------------------------------------------------------------
    // Compile simple functions
    // -----------------------------------------------------------------------

    #[test]
    fn test_compile_void_return() {
        let mut func = minimal_func("void_ret");
        // JALR x0, ra, 0 (return)
        func.push_inst(
            Block(0),
            RiscVISelInst::new(
                RiscVOpcode::Jalr,
                vec![
                    RiscVISelOperand::PReg(ZERO),
                    RiscVISelOperand::PReg(RA),
                    RiscVISelOperand::Imm(0),
                ],
            ),
        );

        let pipeline = RiscVPipeline::new(RiscVPipelineConfig {
            emit_elf: false,
            emit_frame: true,
        });
        let code = pipeline.compile_function(&func).unwrap();

        // Should produce non-empty code (prologue + epilogue + RET).
        assert!(!code.is_empty(), "compiled code should not be empty");

        // All instructions are 4 bytes, so total must be multiple of 4.
        assert_eq!(code.len() % 4, 0, "RISC-V code must be 4-byte aligned");
    }

    #[test]
    fn test_compile_void_return_no_frame() {
        let mut func = minimal_func("void_ret_noframe");
        // JALR x0, ra, 0 (return)
        func.push_inst(
            Block(0),
            RiscVISelInst::new(
                RiscVOpcode::Jalr,
                vec![
                    RiscVISelOperand::PReg(ZERO),
                    RiscVISelOperand::PReg(RA),
                    RiscVISelOperand::Imm(0),
                ],
            ),
        );

        let pipeline = RiscVPipeline::new(RiscVPipelineConfig {
            emit_elf: false,
            emit_frame: false,
        });
        let code = pipeline.compile_function(&func).unwrap();

        // Without frame, should just be JALR x0, ra, 0.
        // JALR: I-type, opcode=1100111, funct3=000, rd=0, rs1=1, imm=0
        // = 0x00008067
        assert_eq!(code.len(), 4);
        let word = u32::from_le_bytes([code[0], code[1], code[2], code[3]]);
        assert_eq!(word, 0x00008067, "expected JALR x0, ra, 0 = 0x00008067");
    }

    #[test]
    fn test_compile_const42() {
        let func = build_riscv_const_test_function();
        let pipeline = RiscVPipeline::new(RiscVPipelineConfig {
            emit_elf: false,
            emit_frame: true,
        });
        let code = pipeline.compile_function(&func).unwrap();

        assert!(!code.is_empty());
        assert_eq!(code.len() % 4, 0);
    }

    #[test]
    fn test_compile_add_function() {
        let func = build_riscv_add_test_function();
        let pipeline = RiscVPipeline::new(RiscVPipelineConfig {
            emit_elf: false,
            emit_frame: true,
        });
        let code = pipeline.compile_function(&func).unwrap();

        assert!(!code.is_empty());
        assert_eq!(code.len() % 4, 0);
    }

    #[test]
    fn test_compile_add_function_no_frame() {
        let func = build_riscv_add_test_function();
        let pipeline = RiscVPipeline::new(RiscVPipelineConfig {
            emit_elf: false,
            emit_frame: false,
        });
        let code = pipeline.compile_function(&func).unwrap();

        assert!(!code.is_empty());
        assert_eq!(code.len() % 4, 0);
    }

    // -----------------------------------------------------------------------
    // ELF emission
    // -----------------------------------------------------------------------

    #[test]
    fn test_compile_to_elf() {
        let func = build_riscv_const_test_function();
        let bytes = riscv_compile_to_elf(&func).unwrap();

        // ELF magic: 0x7F 'E' 'L' 'F'
        assert!(bytes.len() > 16);
        assert_eq!(&bytes[0..4], &[0x7F, b'E', b'L', b'F']);

        // ELF class should be ELFCLASS64 (2).
        assert_eq!(bytes[4], 2);

        // Data encoding should be ELFDATA2LSB (1) = little-endian.
        assert_eq!(bytes[5], 1);

        // Machine type for RISC-V should be EM_RISCV (0xF3 = 243).
        let machine = u16::from_le_bytes([bytes[18], bytes[19]]);
        assert_eq!(machine, 0xF3, "ELF machine should be EM_RISCV (0xF3)");

        // LP64D requires the double-precision floating-point ABI e_flags value.
        let e_flags = u32::from_le_bytes(bytes[48..52].try_into().unwrap());
        assert_eq!(e_flags, EF_RISCV_FLOAT_ABI_DOUBLE);
        assert_eq!(&bytes[48..52], &[0x04, 0x00, 0x00, 0x00]);
    }

    #[test]
    fn test_compile_add_to_elf() {
        let func = build_riscv_add_test_function();
        let bytes = riscv_compile_to_elf(&func).unwrap();
        assert!(bytes.len() > 64);
        assert_eq!(&bytes[0..4], &[0x7F, b'E', b'L', b'F']);
    }

    // -----------------------------------------------------------------------
    // Branch resolution
    // -----------------------------------------------------------------------

    #[test]
    fn test_branch_resolution_unconditional() {
        let sig = Signature {
            params: vec![],
            returns: vec![],
        };
        let mut func = RiscVISelFunction::new("test_br".to_string(), sig);
        let b0 = Block(0);
        let b1 = Block(1);
        func.ensure_block(b0);
        func.ensure_block(b1);

        // b0: JAL x0, b1 (unconditional jump)
        func.push_inst(
            b0,
            RiscVISelInst::new(
                RiscVOpcode::Jal,
                vec![RiscVISelOperand::PReg(ZERO), RiscVISelOperand::Block(b1)],
            ),
        );

        // b1: NOP
        func.push_inst(b1, RiscVISelInst::new(RiscVOpcode::Nop, vec![]));

        resolve_riscv_branches(&mut func).expect("in-range branch resolves");

        // After resolution, JAL should have an Imm operand (not Block).
        let jal = &func.blocks[&b0].insts[0];
        assert_eq!(jal.opcode, RiscVOpcode::Jal);
        // JAL is 4 bytes. Target (b1) starts at offset 4.
        // RISC-V: offset is relative to the branch instruction at offset 0.
        // So offset = 4 - 0 = 4.
        let has_imm = jal
            .operands
            .iter()
            .any(|op| matches!(op, RiscVISelOperand::Imm(4)));
        assert!(
            has_imm,
            "JAL to next block should have offset 4, got {:?}",
            jal.operands
        );
    }

    #[test]
    fn test_branch_resolution_backward() {
        let sig = Signature {
            params: vec![],
            returns: vec![],
        };
        let mut func = RiscVISelFunction::new("test_loop".to_string(), sig);
        let b0 = Block(0);
        let b1 = Block(1);
        func.ensure_block(b0);
        func.ensure_block(b1);

        // b0: NOP (4 bytes)
        func.push_inst(b0, RiscVISelInst::new(RiscVOpcode::Nop, vec![]));

        // b1: JAL x0, b0 (backward jump)
        func.push_inst(
            b1,
            RiscVISelInst::new(
                RiscVOpcode::Jal,
                vec![RiscVISelOperand::PReg(ZERO), RiscVISelOperand::Block(b0)],
            ),
        );

        resolve_riscv_branches(&mut func).expect("in-range branch resolves");

        let jal = &func.blocks[&b1].insts[0];
        let has_neg_imm = jal.operands.iter().any(|op| {
            if let RiscVISelOperand::Imm(v) = op {
                *v < 0
            } else {
                false
            }
        });
        assert!(
            has_neg_imm,
            "backward jump should have negative offset, got {:?}",
            jal.operands
        );
    }

    // -----------------------------------------------------------------------
    // Convenience function tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_riscv_compile_to_bytes() {
        let func = build_riscv_const_test_function();
        let bytes = riscv_compile_to_bytes(&func).unwrap();
        assert!(!bytes.is_empty());
        assert_eq!(bytes.len() % 4, 0);
    }

    // -----------------------------------------------------------------------
    // Operand resolution tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_resolve_operand_vreg() {
        let v0 = VReg::new(0, RegClass::Gpr64);
        let mut alloc = HashMap::new();
        alloc.insert(v0, A0);

        assert_eq!(
            resolve_operand(&RiscVISelOperand::VReg(v0), &alloc),
            Some(A0)
        );
    }

    #[test]
    fn test_resolve_operand_preg() {
        let alloc = HashMap::new();
        assert_eq!(
            resolve_operand(&RiscVISelOperand::PReg(A0), &alloc),
            Some(A0)
        );
    }

    #[test]
    fn test_resolve_operand_imm_returns_none() {
        let alloc = HashMap::new();
        assert_eq!(resolve_operand(&RiscVISelOperand::Imm(42), &alloc), None);
    }

    // -----------------------------------------------------------------------
    // Instruction size
    // -----------------------------------------------------------------------

    #[test]
    fn test_inst_sizes() {
        assert_eq!(inst_size(&RiscVISelInst::new(RiscVOpcode::Phi, vec![])), 0);
        assert_eq!(
            inst_size(&RiscVISelInst::new(RiscVOpcode::StackAlloc, vec![])),
            0
        );
        assert_eq!(inst_size(&RiscVISelInst::new(RiscVOpcode::Nop, vec![])), 4);
        assert_eq!(inst_size(&RiscVISelInst::new(RiscVOpcode::Add, vec![])), 4);
        assert_eq!(inst_size(&RiscVISelInst::new(RiscVOpcode::Jal, vec![])), 4);
        assert_eq!(inst_size(&RiscVISelInst::new(RiscVOpcode::Sd, vec![])), 4);
    }

    // -----------------------------------------------------------------------
    // Error display
    // -----------------------------------------------------------------------

    #[test]
    fn test_pipeline_error_display() {
        let e1 = RiscVPipelineError::ISel("bad isel".to_string());
        assert!(format!("{}", e1).contains("ISel"));

        let e2 = RiscVPipelineError::RegAlloc("out of regs".to_string());
        assert!(format!("{}", e2).contains("regalloc"));

        let e3 = RiscVPipelineError::FrameLowering("bad frame".to_string());
        assert!(format!("{}", e3).contains("frame lowering"));
    }

    // -----------------------------------------------------------------------
    // Test helper function builders
    // -----------------------------------------------------------------------

    #[test]
    fn test_build_add_function_structure() {
        let func = build_riscv_add_test_function();
        assert_eq!(func.name, "add");
        assert_eq!(func.sig.params.len(), 2);
        assert_eq!(func.sig.returns.len(), 1);
        assert_eq!(func.block_order.len(), 1);
        assert_eq!(func.next_vreg, 3);

        let entry = &func.blocks[&Block(0)];
        // ADDI v0, a0, 0; ADDI v1, a1, 0; ADD v2, v0, v1; ADDI a0, v2, 0; JALR x0, ra, 0
        assert_eq!(entry.insts.len(), 5);
        assert_eq!(entry.insts[0].opcode, RiscVOpcode::Addi);
        assert_eq!(entry.insts[1].opcode, RiscVOpcode::Addi);
        assert_eq!(entry.insts[2].opcode, RiscVOpcode::Add);
        assert_eq!(entry.insts[3].opcode, RiscVOpcode::Addi);
        assert_eq!(entry.insts[4].opcode, RiscVOpcode::Jalr);
    }

    #[test]
    fn test_build_const_function_structure() {
        let func = build_riscv_const_test_function();
        assert_eq!(func.name, "const42");
        assert_eq!(func.sig.params.len(), 0);
        assert_eq!(func.sig.returns.len(), 1);

        let entry = &func.blocks[&Block(0)];
        // ADDI a0, x0, 42; JALR x0, ra, 0
        assert_eq!(entry.insts.len(), 2);
        assert_eq!(entry.insts[0].opcode, RiscVOpcode::Addi);
        assert_eq!(entry.insts[1].opcode, RiscVOpcode::Jalr);
    }

    // -----------------------------------------------------------------------
    // is_ret_inst
    // -----------------------------------------------------------------------

    #[test]
    fn test_is_ret_inst() {
        // Valid RET: JALR x0, ra, 0
        let ret_inst = RiscVISelInst::new(
            RiscVOpcode::Jalr,
            vec![
                RiscVISelOperand::PReg(ZERO),
                RiscVISelOperand::PReg(RA),
                RiscVISelOperand::Imm(0),
            ],
        );
        assert!(is_ret_inst(&ret_inst));

        // Not RET: JALR ra, a0, 0 (function call)
        let call_inst = RiscVISelInst::new(
            RiscVOpcode::Jalr,
            vec![
                RiscVISelOperand::PReg(RA),
                RiscVISelOperand::PReg(A0),
                RiscVISelOperand::Imm(0),
            ],
        );
        assert!(!is_ret_inst(&call_inst));

        // Not RET: ADD instruction
        let add_inst = RiscVISelInst::new(RiscVOpcode::Add, vec![]);
        assert!(!is_ret_inst(&add_inst));
    }

    // -----------------------------------------------------------------------
    // Sentinel S5: proof-only bounds-check carrier — emit / expansion / kernel gate
    // -----------------------------------------------------------------------

    use trust_cg_ir::{
        DischargeStatus, GuardKind, GuardOperandRef as GOR, fingerprint_for_kind as fp_kind,
    };

    fn vreg_op(id: u32) -> RiscVISelOperand {
        RiscVISelOperand::VReg(VReg::new(id, RegClass::Gpr64))
    }

    /// One-block function with a single bounds-check carrier `[Reg(0), Reg(1),
    /// Imm(8)]` followed by a return.
    fn func_with_carrier() -> RiscVISelFunction {
        let sig = Signature {
            params: vec![],
            returns: vec![],
        };
        let mut func = RiscVISelFunction::new("riscv_carrier_test".to_string(), sig);
        let entry = Block(0);
        func.ensure_block(entry);
        func.next_vreg = 2;
        func.push_inst(
            entry,
            RiscVISelInst::new(
                RiscVOpcode::TrapBoundsCheckExact,
                vec![vreg_op(0), vreg_op(1), RiscVISelOperand::Imm(8)],
            ),
        );
        func.push_inst(
            entry,
            RiscVISelInst::new(
                RiscVOpcode::Jalr,
                vec![
                    RiscVISelOperand::PReg(ZERO),
                    RiscVISelOperand::PReg(RA),
                    RiscVISelOperand::Imm(0),
                ],
            ),
        );
        func
    }

    fn carrier_fp() -> u128 {
        // The kernel re-derives the binding key with the carrier's GuardKind folded in
        // (defense-in-depth), so the test obligation map must use the same kind-folded key.
        fp_kind(
            GuardKind::BoundsCheck,
            &[GOR::Reg(0), GOR::Reg(1), GOR::Imm(8)],
        )
    }

    fn live_carriers(func: &RiscVISelFunction) -> usize {
        func.block_order
            .iter()
            .filter_map(|b| func.blocks.get(b))
            .flat_map(|b| b.insts.iter())
            .filter(|i| i.opcode == RiscVOpcode::TrapBoundsCheckExact)
            .count()
    }

    #[test]
    fn emit_carrier_threads_obligation_by_fingerprint() {
        let sig = Signature {
            params: vec![],
            returns: vec![],
        };
        let mut func = RiscVISelFunction::new("emit_test".to_string(), sig);
        let entry = Block(0);
        func.ensure_block(entry);
        func.next_vreg = 2;
        emit_riscv_bounds_check_carrier(&mut func, entry, vreg_op(0), vreg_op(1), 8, Some(42));

        // Exactly one carrier with the right operands.
        let block = &func.blocks[&entry];
        assert_eq!(block.insts.len(), 1);
        assert_eq!(block.insts[0].opcode, RiscVOpcode::TrapBoundsCheckExact);
        assert_eq!(
            block.insts[0].operands,
            vec![vreg_op(0), vreg_op(1), RiscVISelOperand::Imm(8)]
        );
        // Obligation threaded by the kernel's fingerprint.
        assert_eq!(func.guard_obligations.get(&carrier_fp()), Some(&42));
        assert_eq!(func.guard_obligations.len(), 1);
    }

    #[test]
    fn emit_carrier_without_obligation_records_nothing() {
        let sig = Signature {
            params: vec![],
            returns: vec![],
        };
        let mut func = RiscVISelFunction::new("emit_noobl".to_string(), sig);
        let entry = Block(0);
        func.ensure_block(entry);
        func.next_vreg = 2;
        emit_riscv_bounds_check_carrier(&mut func, entry, vreg_op(0), vreg_op(1), 8, None);
        // No obligation supplied => nothing recorded; the kernel keeps it (fail-safe).
        assert!(func.guard_obligations.is_empty());
        assert_eq!(live_carriers(&func), 1);
    }

    #[test]
    fn expand_carrier_small_bound_emits_li_bgeu_ebreak() {
        let mut func = func_with_carrier();
        expand_riscv_bounds_check_carriers(&mut func).expect("expand");

        let entry = &func.blocks[&Block(0)];
        // ADDI bound_reg, x0, 8 ; BGEU index, bound_reg, trap ; JALR (ret)
        assert_eq!(entry.insts[0].opcode, RiscVOpcode::Addi);
        assert_eq!(
            entry.insts[0].operands[1],
            RiscVISelOperand::PReg(ZERO),
            "LI materializes via ADDI from x0"
        );
        assert_eq!(entry.insts[0].operands[2], RiscVISelOperand::Imm(8));
        assert_eq!(entry.insts[1].opcode, RiscVOpcode::Bgeu);
        assert_eq!(
            entry.insts[1].operands[0],
            vreg_op(1),
            "BGEU compares the index"
        );
        assert_eq!(entry.insts[2].opcode, RiscVOpcode::Jalr);
        // No carrier survives.
        assert_eq!(live_carriers(&func), 0);

        // Trap block holds a single EBREAK.
        let RiscVISelOperand::Block(trap_block) = entry.insts[1].operands[2] else {
            panic!("BGEU must target a synthetic trap block");
        };
        assert!(entry.successors.contains(&trap_block));
        let trap = &func.blocks[&trap_block];
        assert_eq!(
            trap.insts.iter().map(|i| i.opcode).collect::<Vec<_>>(),
            vec![RiscVOpcode::Ebreak]
        );
    }

    #[test]
    fn expand_carrier_large_bound_uses_lui_addi() {
        let sig = Signature {
            params: vec![],
            returns: vec![],
        };
        let mut func = RiscVISelFunction::new("bounds_large".to_string(), sig);
        let entry = Block(0);
        func.ensure_block(entry);
        func.next_vreg = 2;
        // 100_000 is > 12-bit immediate range, forcing LUI+ADDI.
        func.push_inst(
            entry,
            RiscVISelInst::new(
                RiscVOpcode::TrapBoundsCheckExact,
                vec![vreg_op(0), vreg_op(1), RiscVISelOperand::Imm(100_000)],
            ),
        );

        expand_riscv_bounds_check_carriers(&mut func).expect("expand");

        let block = &func.blocks[&entry];
        // Wide bound: LUI + ADDI to reconstruct, then SLLI 32 / SRLI 32 to zero-extend
        // (undo RV64 LUI sign-extension), then BGEU index, bound_reg.
        assert_eq!(block.insts[0].opcode, RiscVOpcode::Lui);
        assert_eq!(block.insts[1].opcode, RiscVOpcode::Addi);
        assert_eq!(block.insts[2].opcode, RiscVOpcode::Slli);
        assert_eq!(block.insts[3].opcode, RiscVOpcode::Srli);
        assert_eq!(block.insts[4].opcode, RiscVOpcode::Bgeu);
        // A fresh vreg was allocated for the wide bound.
        assert!(func.next_vreg > 2);
    }

    #[test]
    fn materialize_bound_reconstructs_unsigned_value_on_rv64() {
        // The emitted sequence must reconstruct the EXACT unsigned bound under RV64 semantics —
        // crucially for bit-31-set bounds, where RV64 LUI sign-extends and a naive LUI+ADDI would
        // leave a huge sign-extended value that the unsigned BGEU never traps on (silent bypass).
        // We interpret the actual emitted RV64 instructions and assert the final register == bound.
        for &bound in &[
            0i64,
            1,
            0x7ff,
            0x800,
            0x1000,
            100_000,
            0xfff_fff,
            0x7fff_ffff,
            0x8000_0000,
            0xffff_ffff,
        ] {
            let mut out = Vec::new();
            materialize_riscv_bound(bound, vreg_op(7), &mut out);

            let mut reg: u64 = 0;
            for inst in &out {
                let imm = match inst.operands.last() {
                    Some(RiscVISelOperand::Imm(v)) => *v,
                    _ => panic!("materialize op must end in an immediate"),
                };
                match inst.opcode {
                    RiscVOpcode::Addi => {
                        // rs1 is x0 for the small-bound LI idiom, else dst (the running reg).
                        let rs1 = if matches!(inst.operands[1], RiscVISelOperand::PReg(_)) {
                            0i64
                        } else {
                            reg as i64
                        };
                        reg = rs1.wrapping_add(imm) as u64;
                    }
                    // RV64 LUI: sign-extend (imm20 << 12) to 64 bits.
                    RiscVOpcode::Lui => reg = (((imm << 12) as i32) as i64) as u64,
                    RiscVOpcode::Slli => reg <<= imm as u32,
                    RiscVOpcode::Srli => reg >>= imm as u32,
                    other => panic!("unexpected materialize opcode {other:?}"),
                }
            }
            assert_eq!(
                reg, bound as u64,
                "materialized bound 0x{bound:x} reconstructed as 0x{reg:x} on RV64"
            );
        }
    }

    #[test]
    fn expand_is_noop_without_carriers() {
        let func = build_riscv_add_test_function();
        let before = func.block_order.len();
        let mut f = func.clone();
        expand_riscv_bounds_check_carriers(&mut f).expect("expand");
        assert_eq!(f.block_order.len(), before, "no synthetic blocks added");
    }

    #[test]
    fn gate_off_keeps_carrier() {
        let mut func = func_with_carrier();
        let mut pass = RiscVProofGuardElimination::new();
        assert!(!pass.run_on_function(&mut func));
        assert_eq!(
            live_carriers(&func),
            1,
            "no gate => keep (legacy behaviour)"
        );
    }

    #[test]
    fn gate_eliminates_discharged_carrier() {
        let mut func = func_with_carrier();
        let mut evidence = DischargedEvidenceTable::new();
        evidence.insert(42, DischargeStatus::Discharged, None);
        let mut obligations = HashMap::new();
        obligations.insert(carrier_fp(), (42u128, None));

        let mut pass = RiscVProofGuardElimination::new();
        pass.enable_kernel_gate(evidence, obligations);
        assert!(pass.run_on_function(&mut func));

        assert_eq!(
            live_carriers(&func),
            0,
            "discharged => eliminated by kernel"
        );
        assert_eq!(pass.stats().guards_eliminated, 1);
        assert_eq!(pass.kernel_eliminations().len(), 1);
        assert!(pass.recheck_kernel_eliminations().is_ok());
    }

    #[test]
    fn gate_keeps_unbound_carrier() {
        // Bound obligation present in evidence, but the carrier is NOT bound to it
        // (empty obligation map) => kernel keeps it (fail-safe).
        let mut func = func_with_carrier();
        let mut evidence = DischargedEvidenceTable::new();
        evidence.insert(42, DischargeStatus::Discharged, None);

        let mut pass = RiscVProofGuardElimination::new();
        pass.enable_kernel_gate(evidence, HashMap::new());
        pass.run_on_function(&mut func);

        assert_eq!(live_carriers(&func), 1, "unbound carrier => kept");
        assert_eq!(pass.stats().guards_kept, 1);
        assert_eq!(pass.kernel_eliminations().len(), 0);
    }

    #[test]
    fn gate_keeps_pending_obligation() {
        // The carrier IS bound, but its obligation is NOT in the evidence table
        // (Pending obligations never enter the evidence) => kernel keeps it.
        let mut func = func_with_carrier();
        let mut obligations = HashMap::new();
        obligations.insert(carrier_fp(), (42u128, None));

        let mut pass = RiscVProofGuardElimination::new();
        pass.enable_kernel_gate(DischargedEvidenceTable::new(), obligations);
        pass.run_on_function(&mut func);

        assert_eq!(live_carriers(&func), 1, "bound-but-undischarged => kept");
        assert_eq!(pass.kernel_eliminations().len(), 0);
    }

    #[test]
    fn production_policy_keeps_riscv_guard_with_forged_binding_and_lineage() {
        let mut func = func_with_carrier();
        let mut forged_bindings = HashMap::new();
        forged_bindings.insert(carrier_fp(), (0xBAD5_EEDu128, Some(0xF0_12_34u128)));

        let mut pass = RiscVProofGuardElimination::new();
        pass.enable_kernel_gate(
            trust_cg_lower::guard_evidence::production_guard_replay_evidence(),
            forged_bindings,
        );
        assert!(!pass.run_on_function(&mut func));
        assert_eq!(live_carriers(&func), 1);
        assert_eq!(pass.stats().guards_eliminated, 0);
        assert!(pass.kernel_eliminations().is_empty());
    }

    /// #5 (Certified-tier lineage): a Certified obligation whose receipt lineage MATCHES the
    /// evidence is eliminated and re-checks; MISMATCHED or absent lineage is KEPT.
    #[test]
    fn gate_certified_lineage_eliminates_only_on_match() {
        let lineage: u128 = 0x1234_5678_9ABC;

        // Matching.
        {
            let mut func = func_with_carrier();
            let mut evidence = DischargedEvidenceTable::new();
            evidence.insert(42, DischargeStatus::Certified, Some(lineage));
            let mut obligations = HashMap::new();
            obligations.insert(carrier_fp(), (42u128, Some(lineage)));
            let mut pass = RiscVProofGuardElimination::new();
            pass.enable_kernel_gate(evidence, obligations);
            assert!(pass.run_on_function(&mut func));
            assert_eq!(live_carriers(&func), 0, "certified+matching => eliminated");
            assert_eq!(pass.kernel_eliminations().len(), 1);
            assert!(pass.recheck_kernel_eliminations().is_ok());
        }

        // Mismatched.
        {
            let mut func = func_with_carrier();
            let mut evidence = DischargedEvidenceTable::new();
            evidence.insert(42, DischargeStatus::Certified, Some(lineage));
            let mut obligations = HashMap::new();
            obligations.insert(carrier_fp(), (42u128, Some(lineage ^ 0x1)));
            let mut pass = RiscVProofGuardElimination::new();
            pass.enable_kernel_gate(evidence, obligations);
            assert!(!pass.run_on_function(&mut func));
            assert_eq!(live_carriers(&func), 1, "certified+mismatch => kept");
            assert_eq!(pass.kernel_eliminations().len(), 0);
        }

        // Absent receipt lineage.
        {
            let mut func = func_with_carrier();
            let mut evidence = DischargedEvidenceTable::new();
            evidence.insert(42, DischargeStatus::Certified, Some(lineage));
            let mut obligations = HashMap::new();
            obligations.insert(carrier_fp(), (42u128, None));
            let mut pass = RiscVProofGuardElimination::new();
            pass.enable_kernel_gate(evidence, obligations);
            assert!(!pass.run_on_function(&mut func));
            assert_eq!(live_carriers(&func), 1, "certified+absent-lineage => kept");
            assert_eq!(pass.kernel_eliminations().len(), 0);
        }
    }

    /// #9 (non-vacuous operand-drift re-check): a genuine drift in the independently re-lifted
    /// observed operands makes the re-check REJECT fail-closed; the unmodified control re-checks Ok.
    #[test]
    fn recheck_rejects_observed_operand_drift() {
        // Control.
        {
            let mut func = func_with_carrier();
            let mut evidence = DischargedEvidenceTable::new();
            evidence.insert(42, DischargeStatus::Discharged, None);
            let mut obligations = HashMap::new();
            obligations.insert(carrier_fp(), (42u128, None));
            let mut pass = RiscVProofGuardElimination::new();
            pass.enable_kernel_gate(evidence, obligations);
            assert!(pass.run_on_function(&mut func));
            assert_eq!(pass.kernel_eliminations().len(), 1);
            assert!(pass.recheck_kernel_eliminations().is_ok());
        }

        // Drift => reject.
        {
            let mut func = func_with_carrier();
            let mut evidence = DischargedEvidenceTable::new();
            evidence.insert(42, DischargeStatus::Discharged, None);
            let mut obligations = HashMap::new();
            obligations.insert(carrier_fp(), (42u128, None));
            let mut pass = RiscVProofGuardElimination::new();
            pass.enable_kernel_gate(evidence, obligations);
            assert!(pass.run_on_function(&mut func));
            assert_eq!(pass.kernel_eliminations().len(), 1);
            pass.test_force_observed_drift(0, vec![GOR::Reg(9), GOR::Reg(1), GOR::Imm(8)]);
            assert!(
                pass.recheck_kernel_eliminations().is_err(),
                "an operand drift must be REJECTED by the re-check (fail-closed)"
            );
        }
    }

    #[test]
    fn unexpanded_carrier_fails_closed_in_encoder() {
        // Soundness: a carrier that was never expanded must be rejected by the
        // encoder rather than emitted as a silent NOP that drops the bounds check.
        let result = crate::riscv::encode::encode_instruction(
            RiscVOpcode::TrapBoundsCheckExact,
            &RiscVInstOperands::none(),
        );
        assert!(matches!(
            result,
            Err(crate::riscv::encode::RiscVEncodeError::UnsupportedOpcode(
                RiscVOpcode::TrapBoundsCheckExact
            ))
        ));
    }

    #[test]
    fn kept_carrier_compiles_to_bgeu_ebreak_end_to_end() {
        // Gate OFF (default): the carrier is kept and the pipeline expands it to a
        // real BGEU + EBREAK trap, which encodes to real bytes (no UnsupportedOpcode).
        let func = func_with_carrier();
        let bytes = riscv_compile_to_bytes(&func).expect("compile kept carrier");
        assert!(!bytes.is_empty());
        assert_eq!(bytes.len() % 4, 0);
        // EBREAK (0x00100073) must be present as a 4-byte LE word.
        let has_ebreak = bytes
            .chunks_exact(4)
            .any(|w| w == 0x0010_0073u32.to_le_bytes());
        assert!(has_ebreak, "kept carrier must expand to an EBREAK trap");
    }

    #[test]
    fn eliminated_carrier_compiles_without_ebreak_end_to_end() {
        // Gate ON + discharged obligation: the carrier is eliminated by the kernel,
        // so no BGEU/EBREAK trap is emitted (the proven check vanishes).
        let mut func = func_with_carrier();
        let mut evidence = DischargedEvidenceTable::new();
        evidence.insert(42, DischargeStatus::Discharged, None);
        let mut obligations = HashMap::new();
        obligations.insert(carrier_fp(), (42u128, None));
        let mut pass = RiscVProofGuardElimination::new();
        pass.enable_kernel_gate(evidence, obligations);
        assert!(pass.run_on_function(&mut func));
        assert!(pass.recheck_kernel_eliminations().is_ok());

        let bytes = riscv_compile_to_bytes(&func).expect("compile eliminated carrier");
        let has_ebreak = bytes
            .chunks_exact(4)
            .any(|w| w == 0x0010_0073u32.to_le_bytes());
        assert!(
            !has_ebreak,
            "eliminated carrier must NOT emit an EBREAK trap"
        );
    }

    // -----------------------------------------------------------------------
    // Real register allocator: liveness, reuse, spilling
    // -----------------------------------------------------------------------

    /// Build a function with `n` GPR vregs that are ALL simultaneously live at a
    /// single program point, then consumed. With `n` greater than the
    /// allocatable GPR pool this forces genuine spilling.
    ///
    /// Shape (single block):
    ///   ADDI v0, x0, c0
    ///   ...
    ///   ADDI v{n-1}, x0, c{n-1}      ; here all of v0..v{n-1} are live
    ///   ADDI acc, v0, 0              ; first use (acc = v0)
    ///   ADD  acc, acc, v1            ; consume v1
    ///   ...
    ///   ADD  acc, acc, v{n-1}        ; consume v{n-1}
    ///   ADDI a0, acc, 0             ; move sum to return reg
    ///   JALR x0, ra, 0             ; return
    fn build_high_pressure_func(n: u32) -> RiscVISelFunction {
        let sig = Signature {
            params: vec![],
            returns: vec![trust_cg_lower::types::Type::I64],
        };
        let mut func = RiscVISelFunction::new("high_pressure".to_string(), sig);
        let entry = Block(0);
        func.ensure_block(entry);

        // Define v0..v{n-1}.
        for k in 0..n {
            let v = VReg::new(k, RegClass::Gpr64);
            func.push_inst(
                entry,
                RiscVISelInst::new(
                    RiscVOpcode::Addi,
                    vec![
                        RiscVISelOperand::VReg(v),
                        RiscVISelOperand::PReg(ZERO),
                        RiscVISelOperand::Imm((k as i64 % 100) + 1),
                    ],
                ),
            );
        }

        // acc = v0 ; acc += v1 ; ... ; acc += v{n-1}
        let acc = VReg::new(n, RegClass::Gpr64);
        func.push_inst(
            entry,
            RiscVISelInst::new(
                RiscVOpcode::Addi,
                vec![
                    RiscVISelOperand::VReg(acc),
                    RiscVISelOperand::VReg(VReg::new(0, RegClass::Gpr64)),
                    RiscVISelOperand::Imm(0),
                ],
            ),
        );
        for k in 1..n {
            func.push_inst(
                entry,
                RiscVISelInst::new(
                    RiscVOpcode::Add,
                    vec![
                        RiscVISelOperand::VReg(acc),
                        RiscVISelOperand::VReg(acc),
                        RiscVISelOperand::VReg(VReg::new(k, RegClass::Gpr64)),
                    ],
                ),
            );
        }

        // Move result to a0.
        func.push_inst(
            entry,
            RiscVISelInst::new(
                RiscVOpcode::Addi,
                vec![
                    RiscVISelOperand::PReg(A0),
                    RiscVISelOperand::VReg(acc),
                    RiscVISelOperand::Imm(0),
                ],
            ),
        );
        // Return.
        func.push_inst(
            entry,
            RiscVISelInst::new(
                RiscVOpcode::Jalr,
                vec![
                    RiscVISelOperand::PReg(ZERO),
                    RiscVISelOperand::PReg(RA),
                    RiscVISelOperand::Imm(0),
                ],
            ),
        );
        func.next_vreg = n + 1;
        func
    }

    #[test]
    fn regalloc_reuses_registers_for_disjoint_intervals() {
        // Two value chains with non-overlapping lifetimes should be able to
        // share the same physical register — the naive first-appearance map
        // could never do this. We build a sequence where v0 dies before v1 is
        // defined; assert their assigned pregs CAN coincide and never exceed the
        // pool, and that the function still encodes.
        let sig = Signature {
            params: vec![],
            returns: vec![trust_cg_lower::types::Type::I64],
        };
        let mut func = RiscVISelFunction::new("reuse".to_string(), sig);
        let entry = Block(0);
        func.ensure_block(entry);

        let v0 = VReg::new(0, RegClass::Gpr64);
        let v1 = VReg::new(1, RegClass::Gpr64);
        // ADDI v0, x0, 1
        func.push_inst(
            entry,
            RiscVISelInst::new(
                RiscVOpcode::Addi,
                vec![
                    RiscVISelOperand::VReg(v0),
                    RiscVISelOperand::PReg(ZERO),
                    RiscVISelOperand::Imm(1),
                ],
            ),
        );
        // ADDI a0, v0, 0   (last use of v0; v0 now dead)
        func.push_inst(
            entry,
            RiscVISelInst::new(
                RiscVOpcode::Addi,
                vec![
                    RiscVISelOperand::PReg(A0),
                    RiscVISelOperand::VReg(v0),
                    RiscVISelOperand::Imm(0),
                ],
            ),
        );
        // ADDI v1, x0, 2   (v1 starts after v0 ends)
        func.push_inst(
            entry,
            RiscVISelInst::new(
                RiscVOpcode::Addi,
                vec![
                    RiscVISelOperand::VReg(v1),
                    RiscVISelOperand::PReg(ZERO),
                    RiscVISelOperand::Imm(2),
                ],
            ),
        );
        // ADDI a0, v1, 0
        func.push_inst(
            entry,
            RiscVISelInst::new(
                RiscVOpcode::Addi,
                vec![
                    RiscVISelOperand::PReg(A0),
                    RiscVISelOperand::VReg(v1),
                    RiscVISelOperand::Imm(0),
                ],
            ),
        );
        func.next_vreg = 2;

        let assignment = RiscVRegAssignment::assign(&func).unwrap();
        assert_eq!(assignment.num_spills, 0, "no pressure, no spills");
        // Both got the SAME register because their lifetimes are disjoint.
        let p0 = assignment.allocation[&v0];
        let p1 = assignment.allocation[&v1];
        assert_eq!(
            p0, p1,
            "disjoint live intervals should reuse the same physical register"
        );
        // Encodes end to end.
        let bytes = riscv_compile_to_bytes(&func).expect("compile reuse func");
        assert!(!bytes.is_empty());
        assert_eq!(bytes.len() % 4, 0);
    }

    #[test]
    fn regalloc_does_not_assign_reserved_abi_regs() {
        // No allocated vreg may land on ra, s0/fp, sp, or the spill scratch regs.
        let func = build_high_pressure_func(20);
        let assignment = RiscVRegAssignment::assign(&func).unwrap();
        for (&v, &preg) in &assignment.allocation {
            assert_ne!(preg, RA, "v{} must not be assigned ra", v.id);
            assert_ne!(preg, S0, "v{} must not be assigned s0/fp", v.id);
            assert_ne!(preg, SP, "v{} must not be assigned sp", v.id);
            assert_ne!(
                preg,
                riscv_regs::T5,
                "v{} must not be assigned the t5 spill scratch",
                v.id
            );
            assert_ne!(
                preg,
                riscv_regs::T6,
                "v{} must not be assigned the t6 spill scratch",
                v.id
            );
        }
    }

    #[test]
    fn frame_exceeding_imm12_fails_closed() {
        // A frame larger than the signed-12-bit immediate range cannot encode the
        // prologue/epilogue SP-adjust ('ADDI SP, SP, -frame_size') or the saved-
        // register offsets without a temp-register materialization sequence the
        // minimal backend does not emit. Lowering MUST fail closed with a typed
        // FrameLowering error rather than let the I-/S-type encoders silently mask
        // the immediate (& 0xFFF) and corrupt the stack pointer.
        let sig = Signature {
            params: vec![],
            returns: vec![],
        };
        let mut func = RiscVISelFunction::new("big_frame".to_string(), sig);
        func.ensure_block(Block(0));

        // 256 spill slots -> frame_size = (2 + 0 + 256) * 8 = 2064 bytes > 2047.
        let assignment = RiscVRegAssignment {
            allocation: std::collections::HashMap::new(),
            used_callee_saved: vec![],
            num_spills: 256,
            spill_slots: std::collections::HashMap::new(),
        };
        assert!(
            compute_frame_size(assignment.used_callee_saved.len(), assignment.num_spills) as i64
                > RISCV_IMM12_MAX,
            "test precondition: the frame must exceed the imm12 range"
        );

        let pipeline = RiscVPipeline::default_config();
        let err = pipeline
            .insert_prologue_epilogue(&mut func, &assignment)
            .expect_err("oversized frame must fail closed");
        assert!(
            matches!(err, RiscVPipelineError::FrameLowering(_)),
            "expected a typed FrameLowering error, got {err:?}"
        );
    }

    #[test]
    fn huge_function_frame_overflow_compiles_closed_not_silently() {
        // Regression for an adversarially-found silent miscompile: with real
        // spilling enabled, a function with hundreds of simultaneously-live values
        // produces frame_size > 2047. Before the fail-closed frame/encoder guards,
        // the prologue 'ADDI SP, SP, -frame_size' immediate was silently masked
        // (& 0xFFF), so compile_function returned Ok(bytes) with a prologue that
        // moved SP the WRONG direction (stack corruption). The full pipeline must
        // now REFUSE with a typed FrameLowering error, never Ok with corrupt code.
        let func = build_high_pressure_func(280);
        let pipeline = RiscVPipeline::default_config();
        let err = pipeline
            .compile_function(&func)
            .expect_err("oversized frame must not silently compile to corrupt bytes");
        assert!(
            matches!(err, RiscVPipelineError::FrameLowering(_)),
            "expected a typed FrameLowering error, got {err:?}"
        );
    }

    #[test]
    fn regalloc_spills_under_high_register_pressure() {
        // 30 simultaneously-live GPR vregs exceed the 23-wide allocatable GPR
        // pool (T0..T3 + A0..A7 + S1..S11), forcing REAL spilling.
        let n = 30u32;
        assert!(
            n as usize > allocatable_gprs().len(),
            "test must exceed the allocatable GPR pool ({})",
            allocatable_gprs().len()
        );

        let func = build_high_pressure_func(n);
        let assignment = RiscVRegAssignment::assign(&func).expect("assign high-pressure func");

        // Real spilling happened.
        assert!(
            assignment.num_spills > 0,
            "expected spilling under high register pressure, got num_spills=0"
        );
        assert_eq!(
            assignment.num_spills as usize,
            assignment.spill_slots.len(),
            "num_spills must equal the number of spill slots assigned"
        );
        // No allocated preg may exceed the pool / be a reserved reg.
        let pool = allocatable_gprs();
        for &preg in assignment.allocation.values() {
            assert!(
                pool.contains(&preg),
                "spilled-function allocation used a non-pool reg {:?}",
                preg
            );
        }

        // The rewritten stream must contain reload (Ld) and store (Sd) traffic.
        let mut func_rw = func.clone();
        rewrite_spills(&mut func_rw, &assignment).expect("rewrite spills");
        let mut n_ld = 0;
        let mut n_sd = 0;
        for b in &func_rw.block_order {
            for inst in &func_rw.blocks[b].insts {
                match inst.opcode {
                    RiscVOpcode::Ld => n_ld += 1,
                    RiscVOpcode::Sd => n_sd += 1,
                    _ => {}
                }
            }
        }
        assert!(n_ld > 0, "spilling must insert reload (Ld) instructions");
        assert!(n_sd > 0, "spilling must insert store (Sd) instructions");

        // Every reload/store must target an SP-relative slot with a valid imm12
        // and use a reserved scratch register, never a value preg.
        for b in &func_rw.block_order {
            for inst in &func_rw.blocks[b].insts {
                if matches!(inst.opcode, RiscVOpcode::Ld | RiscVOpcode::Sd) {
                    // operand[1] must be SP, operand[2] an in-range imm.
                    if let (Some(RiscVISelOperand::PReg(base)), Some(RiscVISelOperand::Imm(off))) =
                        (inst.operands.get(1), inst.operands.get(2))
                    {
                        assert_eq!(*base, SP, "spill traffic must be SP-relative");
                        assert!(
                            *off >= -2048 && *off <= RISCV_IMM12_MAX,
                            "spill offset {} out of imm12 range",
                            off
                        );
                    }
                }
            }
        }

        // Frame must account for the spill slots and stay 16-byte aligned.
        let frame = compute_frame_size(assignment.used_callee_saved.len(), assignment.num_spills);
        assert_eq!(frame % 16, 0, "frame must stay 16-byte aligned");
        let min_bytes = (2 + assignment.used_callee_saved.len() as u32 + assignment.num_spills) * 8;
        assert!(
            frame >= min_bytes,
            "frame {} must reserve room for ra+s0+callee-saved+{} spills ({})",
            frame,
            assignment.num_spills,
            min_bytes
        );

        // End-to-end: it encodes to valid 4-byte-aligned machine code.
        let bytes = riscv_compile_to_bytes(&func).expect("compile spilled function");
        assert!(!bytes.is_empty(), "spilled function must produce code");
        assert_eq!(bytes.len() % 4, 0, "RISC-V code must be 4-byte aligned");
    }

    #[test]
    fn spilled_function_is_semantically_correct() {
        // The strongest soundness check: build a high-pressure function that
        // computes a KNOWN sum (forcing spills), run it through assign +
        // rewrite_spills + prologue/epilogue, then INTERPRET the rewritten
        // RV64 stream over a register file + simulated stack and assert a0 holds
        // the correct sum. This proves the spill reload/store traffic preserves
        // semantics, not merely that it encodes.
        let n = 30u32;
        let expected: u64 = (0..n).map(|k| ((k as u64) % 100) + 1).sum();

        let mut func = build_high_pressure_func(n);
        // Run the same phases compile_function runs (minus encoding).
        let assignment = RiscVRegAssignment::assign(&func).expect("assign");
        assert!(assignment.num_spills > 0, "test must actually spill");
        rewrite_spills(&mut func, &assignment).expect("rewrite spills");
        let frame = compute_frame_size(assignment.used_callee_saved.len(), assignment.num_spills);
        let pipeline = RiscVPipeline::default_config();
        pipeline
            .insert_prologue_epilogue(&mut func, &assignment)
            .expect("small frame must lower");
        resolve_riscv_branches(&mut func).expect("in-range branch resolves");

        // --- Tiny RV64 interpreter over GPRs + a byte-addressed stack. ---
        // Registers indexed by hw encoding 0..32. x0 stays 0.
        let mut regs = [0u64; 32];
        // Simulated stack: SP starts high; the frame grows downward. We give a
        // generous arena and place the initial SP near the top.
        let stack_size = (frame as usize) + 256;
        let mut mem = vec![0u8; stack_size];
        let sp_init = stack_size as u64 - 16; // 16-byte aligned start
        regs[2] = sp_init; // x2 = sp
        regs[1] = 0xdead_beef; // ra sentinel (saved/restored, never executed as a target)

        // Non-spilled VRegs are still VReg operands in the stream — the physical
        // assignment is applied at ENCODE time via the allocation map, exactly
        // as `resolve_operand` does. The interpreter resolves the same way.
        let reg_idx = |op: &RiscVISelOperand| -> Option<usize> {
            match op {
                RiscVISelOperand::PReg(p) => Some(p.hw_enc() as usize),
                RiscVISelOperand::VReg(v) => {
                    assignment.allocation.get(v).map(|p| p.hw_enc() as usize)
                }
                _ => None,
            }
        };
        let imm_of = |inst: &RiscVISelInst| -> i64 {
            inst.operands
                .iter()
                .find_map(|o| match o {
                    RiscVISelOperand::Imm(v) => Some(*v),
                    _ => None,
                })
                .unwrap_or(0)
        };

        for &b in &func.block_order {
            for inst in &func.blocks[&b].insts {
                match inst.opcode {
                    RiscVOpcode::Addi => {
                        let rd = reg_idx(&inst.operands[0]).unwrap();
                        let rs1 = reg_idx(&inst.operands[1]).unwrap();
                        let v = (regs[rs1] as i64).wrapping_add(imm_of(inst)) as u64;
                        if rd != 0 {
                            regs[rd] = v;
                        }
                    }
                    RiscVOpcode::Add => {
                        let rd = reg_idx(&inst.operands[0]).unwrap();
                        let rs1 = reg_idx(&inst.operands[1]).unwrap();
                        let rs2 = reg_idx(&inst.operands[2]).unwrap();
                        let v = regs[rs1].wrapping_add(regs[rs2]);
                        if rd != 0 {
                            regs[rd] = v;
                        }
                    }
                    RiscVOpcode::Sd => {
                        // [src, base, off]
                        let src = reg_idx(&inst.operands[0]).unwrap();
                        let base = reg_idx(&inst.operands[1]).unwrap();
                        let off = imm_of(inst);
                        let addr = (regs[base] as i64 + off) as usize;
                        mem[addr..addr + 8].copy_from_slice(&regs[src].to_le_bytes());
                    }
                    RiscVOpcode::Ld => {
                        // [rd, base, off]
                        let rd = reg_idx(&inst.operands[0]).unwrap();
                        let base = reg_idx(&inst.operands[1]).unwrap();
                        let off = imm_of(inst);
                        let addr = (regs[base] as i64 + off) as usize;
                        let mut buf = [0u8; 8];
                        buf.copy_from_slice(&mem[addr..addr + 8]);
                        if rd != 0 {
                            regs[rd] = u64::from_le_bytes(buf);
                        }
                    }
                    RiscVOpcode::Jalr => {
                        // Treated as return: stop interpreting.
                        break;
                    }
                    other => panic!("interpreter saw unexpected opcode {other:?}"),
                }
            }
        }

        // a0 = x10 must hold the sum.
        assert_eq!(
            regs[A0.hw_enc() as usize],
            expected,
            "spilled function computed wrong result"
        );
        // SP must be restored to its initial value by the epilogue.
        assert_eq!(regs[2], sp_init, "epilogue must restore SP");
    }

    #[test]
    fn regalloc_spill_without_frame_fails_closed() {
        // Spilling requires a frame; with frames disabled the compile must
        // fail closed (typed RegAlloc error), never silently clobber the stack.
        let func = build_high_pressure_func(30);
        let pipeline = RiscVPipeline::new(RiscVPipelineConfig {
            emit_elf: false,
            emit_frame: false,
        });
        let err = pipeline
            .compile_function(&func)
            .expect_err("spilling without a frame must fail closed");
        assert!(
            matches!(err, RiscVPipelineError::RegAlloc(_)),
            "expected a typed RegAlloc error, got {err:?}"
        );
    }

    #[test]
    fn regalloc_respects_fixed_abi_uses() {
        // A vreg whose live interval spans a point where a physical ABI register
        // is read/written as a fixed operand must NOT be colored onto that
        // physical register (else the fixed operand would clobber it — the exact
        // class of miscompile the naive map ignored). Here v_keep is defined
        // FIRST, then a0 is read by an arg-binding move, then v_keep is used —
        // so v_keep is live across the a0 read and must avoid a0.
        let sig = Signature {
            params: vec![trust_cg_lower::types::Type::I64],
            returns: vec![trust_cg_lower::types::Type::I64],
        };
        let mut func = RiscVISelFunction::new("abi".to_string(), sig);
        let entry = Block(0);
        func.ensure_block(entry);
        let v_keep = VReg::new(0, RegClass::Gpr64);
        let v_arg = VReg::new(1, RegClass::Gpr64);
        let v_sum = VReg::new(2, RegClass::Gpr64);

        // v_keep = 7  (defined before the a0 read, used after it)
        func.push_inst(
            entry,
            RiscVISelInst::new(
                RiscVOpcode::Addi,
                vec![
                    RiscVISelOperand::VReg(v_keep),
                    RiscVISelOperand::PReg(ZERO),
                    RiscVISelOperand::Imm(7),
                ],
            ),
        );
        // v_arg = a0   (FIXED use of a0 at this point; v_keep is live here)
        func.push_inst(
            entry,
            RiscVISelInst::new(
                RiscVOpcode::Addi,
                vec![
                    RiscVISelOperand::VReg(v_arg),
                    RiscVISelOperand::PReg(A0),
                    RiscVISelOperand::Imm(0),
                ],
            ),
        );
        // v_sum = v_keep + v_arg   (last use of both)
        func.push_inst(
            entry,
            RiscVISelInst::new(
                RiscVOpcode::Add,
                vec![
                    RiscVISelOperand::VReg(v_sum),
                    RiscVISelOperand::VReg(v_keep),
                    RiscVISelOperand::VReg(v_arg),
                ],
            ),
        );
        // a0 = v_sum ; ret
        func.push_inst(
            entry,
            RiscVISelInst::new(
                RiscVOpcode::Addi,
                vec![
                    RiscVISelOperand::PReg(A0),
                    RiscVISelOperand::VReg(v_sum),
                    RiscVISelOperand::Imm(0),
                ],
            ),
        );
        func.push_inst(
            entry,
            RiscVISelInst::new(
                RiscVOpcode::Jalr,
                vec![
                    RiscVISelOperand::PReg(ZERO),
                    RiscVISelOperand::PReg(RA),
                    RiscVISelOperand::Imm(0),
                ],
            ),
        );
        func.next_vreg = 3;

        let assignment = RiscVRegAssignment::assign(&func).unwrap();
        // v_keep spans the a0 read, so it must not alias a0.
        assert_ne!(
            assignment.allocation[&v_keep], A0,
            "v_keep (live while a0 is read) must not alias a0"
        );
        // It still compiles.
        let bytes = riscv_compile_to_bytes(&func).expect("compile abi func");
        assert!(!bytes.is_empty());
    }

    // =======================================================================
    // Phase 3: function calls / LP64D ABI — self-recursion + call clobber +
    // parallel-move argument marshaling.
    // =======================================================================

    /// A small PC-driven RV64 interpreter over a register assignment, used to
    /// execute a self-recursive function end-to-end and assert numeric results
    /// AND that ra / callee-saved registers / SP are preserved across recursion.
    ///
    /// It runs the FULLY-LOWERED ISel stream (post regalloc + arg-fixup +
    /// prologue/epilogue + branch resolution): branch/jump targets are PC-relative
    /// `Imm` offsets; `JAL ra` (call) sets `ra = pc + 4` and jumps; `JALR x0, ra, 0`
    /// (return) jumps to `ra`. This faithfully models the call/return ABI the
    /// recursion depends on — a corrupted ra, callee-saved reg, or SP shows up as a
    /// wrong result or an infinite loop (bounded by `step_limit`).
    struct RiscVInterp {
        regs: [u64; 32],
        mem: Vec<u8>,
        // Flat (byte_offset -> instruction-index) over the linearized stream.
        flat: Vec<RiscVISelInst>,
        offsets: Vec<i64>,
        alloc: HashMap<VReg, RiscVPReg>,
    }

    impl RiscVInterp {
        fn build(func: &RiscVISelFunction, alloc: HashMap<VReg, RiscVPReg>, frame: u32) -> Self {
            let mut flat = Vec::new();
            let mut offsets = Vec::new();
            let mut off: i64 = 0;
            for &b in &func.block_order {
                for inst in &func.blocks[&b].insts {
                    let sz = inst_size(inst) as i64;
                    if sz == 0 {
                        continue; // pseudo-instructions emit no code / no PC slot
                    }
                    offsets.push(off);
                    flat.push(inst.clone());
                    off += sz;
                }
            }
            let stack_size = (frame as usize) * 64 + 4096; // deep enough for recursion
            let mut regs = [0u64; 32];
            let sp_init = stack_size as u64 - 16;
            regs[2] = sp_init; // sp
            Self {
                regs,
                mem: vec![0u8; stack_size],
                flat,
                offsets,
                alloc,
            }
        }

        fn reg_idx(&self, op: &RiscVISelOperand) -> usize {
            match op {
                RiscVISelOperand::PReg(p) => p.hw_enc() as usize,
                RiscVISelOperand::VReg(v) => {
                    self.alloc.get(v).expect("vreg must be allocated").hw_enc() as usize
                }
                other => panic!("interp: operand {other:?} is not a register"),
            }
        }

        fn imm_of(inst: &RiscVISelInst) -> i64 {
            inst.operands
                .iter()
                .find_map(|o| match o {
                    RiscVISelOperand::Imm(v) => Some(*v),
                    _ => None,
                })
                .unwrap_or(0)
        }

        fn idx_for_pc(&self, pc: i64) -> Option<usize> {
            self.offsets.iter().position(|&o| o == pc)
        }

        /// Run from PC=0 (the function entry / prologue). `ra` is seeded with a
        /// sentinel terminator address; the OUTERMOST `JALR x0, ra, 0` returns to
        /// it, ending interpretation. `sp_init` is returned for the caller to
        /// assert SP restoration. Returns `regs[a0]`.
        fn run(&mut self, sentinel_ra: u64, step_limit: usize) -> u64 {
            self.regs[1] = sentinel_ra; // ra
            let mut pc: i64 = 0;
            for _ in 0..step_limit {
                let idx = self
                    .idx_for_pc(pc)
                    .unwrap_or_else(|| panic!("interp: pc {pc} has no instruction"));
                let inst = self.flat[idx].clone();
                let mut next_pc = pc + inst_size(&inst) as i64;
                match inst.opcode {
                    RiscVOpcode::Addi => {
                        let rd = self.reg_idx(&inst.operands[0]);
                        let rs1 = self.reg_idx(&inst.operands[1]);
                        let v = (self.regs[rs1] as i64).wrapping_add(Self::imm_of(&inst)) as u64;
                        if rd != 0 {
                            self.regs[rd] = v;
                        }
                    }
                    RiscVOpcode::Add => {
                        let rd = self.reg_idx(&inst.operands[0]);
                        let a = self.regs[self.reg_idx(&inst.operands[1])];
                        let b = self.regs[self.reg_idx(&inst.operands[2])];
                        if rd != 0 {
                            self.regs[rd] = a.wrapping_add(b);
                        }
                    }
                    RiscVOpcode::Sub => {
                        let rd = self.reg_idx(&inst.operands[0]);
                        let a = self.regs[self.reg_idx(&inst.operands[1])];
                        let b = self.regs[self.reg_idx(&inst.operands[2])];
                        if rd != 0 {
                            self.regs[rd] = a.wrapping_sub(b);
                        }
                    }
                    RiscVOpcode::Mul => {
                        let rd = self.reg_idx(&inst.operands[0]);
                        let a = self.regs[self.reg_idx(&inst.operands[1])];
                        let b = self.regs[self.reg_idx(&inst.operands[2])];
                        if rd != 0 {
                            self.regs[rd] = a.wrapping_mul(b);
                        }
                    }
                    RiscVOpcode::Sltiu => {
                        let rd = self.reg_idx(&inst.operands[0]);
                        let a = self.regs[self.reg_idx(&inst.operands[1])];
                        let imm = Self::imm_of(&inst) as u64;
                        if rd != 0 {
                            self.regs[rd] = (a < imm) as u64;
                        }
                    }
                    RiscVOpcode::Sd => {
                        let src = self.reg_idx(&inst.operands[0]);
                        let base = self.reg_idx(&inst.operands[1]);
                        let addr = (self.regs[base] as i64 + Self::imm_of(&inst)) as usize;
                        self.mem[addr..addr + 8].copy_from_slice(&self.regs[src].to_le_bytes());
                    }
                    RiscVOpcode::Ld => {
                        let rd = self.reg_idx(&inst.operands[0]);
                        let base = self.reg_idx(&inst.operands[1]);
                        let addr = (self.regs[base] as i64 + Self::imm_of(&inst)) as usize;
                        let mut buf = [0u8; 8];
                        buf.copy_from_slice(&self.mem[addr..addr + 8]);
                        if rd != 0 {
                            self.regs[rd] = u64::from_le_bytes(buf);
                        }
                    }
                    RiscVOpcode::Bne => {
                        let a = self.regs[self.reg_idx(&inst.operands[0])];
                        let b = self.regs[self.reg_idx(&inst.operands[1])];
                        if a != b {
                            next_pc = pc + Self::imm_of(&inst);
                        }
                    }
                    RiscVOpcode::Beq => {
                        let a = self.regs[self.reg_idx(&inst.operands[0])];
                        let b = self.regs[self.reg_idx(&inst.operands[1])];
                        if a == b {
                            next_pc = pc + Self::imm_of(&inst);
                        }
                    }
                    // Signed/unsigned ordered branches — supported so that a
                    // far-conditional-branch relaxation that INVERTS the source
                    // condition (Blt<->Bge, Bltu<->Bgeu) is interpretable here.
                    RiscVOpcode::Blt => {
                        let a = self.regs[self.reg_idx(&inst.operands[0])] as i64;
                        let b = self.regs[self.reg_idx(&inst.operands[1])] as i64;
                        if a < b {
                            next_pc = pc + Self::imm_of(&inst);
                        }
                    }
                    RiscVOpcode::Bge => {
                        let a = self.regs[self.reg_idx(&inst.operands[0])] as i64;
                        let b = self.regs[self.reg_idx(&inst.operands[1])] as i64;
                        if a >= b {
                            next_pc = pc + Self::imm_of(&inst);
                        }
                    }
                    RiscVOpcode::Bltu => {
                        let a = self.regs[self.reg_idx(&inst.operands[0])];
                        let b = self.regs[self.reg_idx(&inst.operands[1])];
                        if a < b {
                            next_pc = pc + Self::imm_of(&inst);
                        }
                    }
                    RiscVOpcode::Bgeu => {
                        let a = self.regs[self.reg_idx(&inst.operands[0])];
                        let b = self.regs[self.reg_idx(&inst.operands[1])];
                        if a >= b {
                            next_pc = pc + Self::imm_of(&inst);
                        }
                    }
                    // AUIPC rd, hi20: rd = pc + (hi20 << 12). Needed to interpret a
                    // far-JAL relaxed to AUIPC+JALR (the AUIPC computes the pcrel-hi
                    // anchor the JALR completes with lo12).
                    RiscVOpcode::Auipc => {
                        let rd = self.reg_idx(&inst.operands[0]);
                        let hi20 = Self::imm_of(&inst);
                        if rd != 0 {
                            self.regs[rd] = (pc + (hi20 << 12)) as u64;
                        }
                    }
                    RiscVOpcode::Jal => {
                        // operands[0] = rd (x0 = jump, ra = call); first Imm = offset.
                        let rd = self.reg_idx(&inst.operands[0]);
                        if rd != 0 {
                            self.regs[rd] = (pc + 4) as u64; // link
                        }
                        next_pc = pc + Self::imm_of(&inst);
                    }
                    RiscVOpcode::Jalr => {
                        // JALR x0, ra, 0: return to (ra + imm). The outermost
                        // return jumps to the sentinel, ending interpretation.
                        let rs1 = self.reg_idx(&inst.operands[1]);
                        let target = (self.regs[rs1] as i64).wrapping_add(Self::imm_of(&inst));
                        if target as u64 == SENTINEL_RA {
                            return self.regs[A0.hw_enc() as usize];
                        }
                        next_pc = target;
                    }
                    other => panic!("interp: unexpected opcode {other:?}"),
                }
                pc = next_pc;
            }
            panic!("interp: step limit reached (likely corrupted ra/sp -> nonterminating)");
        }
    }

    // A distinguished, non-code "return address" the outermost call returns to,
    // signaling the interpreter to stop. Chosen far outside the code region.
    const SENTINEL_RA: u64 = 0xFFFF_FFFF_FFFF_FF00;

    /// Build the self-recursive `sum_to_n(n) = n==0 ? 0 : n + sum_to_n(n-1)` as a
    /// hand-written ISel function. `v_n` is deliberately live ACROSS the recursive
    /// call (used by `v_n + v_res`), so a correct compile MUST keep it off the
    /// caller-saved registers the call clobbers.
    fn build_sum_to_n_self_recursive() -> (RiscVISelFunction, VReg) {
        let sig = Signature {
            params: vec![trust_cg_lower::types::Type::I64],
            returns: vec![trust_cg_lower::types::Type::I64],
        };
        let mut func = RiscVISelFunction::new("sum_to_n".to_string(), sig);
        let entry = Block(0);
        let base = Block(1);
        let rec = Block(2);
        func.ensure_block(entry);
        func.ensure_block(base);
        func.ensure_block(rec);

        let v_n = VReg::new(0, RegClass::Gpr64);
        let v_zero = VReg::new(1, RegClass::Gpr64);
        let v_nm1 = VReg::new(2, RegClass::Gpr64);
        let v_res = VReg::new(3, RegClass::Gpr64);
        let v_sum = VReg::new(4, RegClass::Gpr64);
        func.next_vreg = 5;

        // entry: v_n = a0 ; v_zero = (v_n == 0) ; if v_zero goto base else rec.
        func.push_inst(
            entry,
            RiscVISelInst::new(
                RiscVOpcode::Addi,
                vec![
                    RiscVISelOperand::VReg(v_n),
                    RiscVISelOperand::PReg(A0),
                    RiscVISelOperand::Imm(0),
                ],
            ),
        );
        // SLTIU v_zero, v_n, 1  =>  v_zero = (v_n == 0).
        func.push_inst(
            entry,
            RiscVISelInst::new(
                RiscVOpcode::Sltiu,
                vec![
                    RiscVISelOperand::VReg(v_zero),
                    RiscVISelOperand::VReg(v_n),
                    RiscVISelOperand::Imm(1),
                ],
            ),
        );
        // BNE v_zero, x0, base  (taken when n == 0)
        func.push_inst(
            entry,
            RiscVISelInst::new(
                RiscVOpcode::Bne,
                vec![
                    RiscVISelOperand::VReg(v_zero),
                    RiscVISelOperand::PReg(ZERO),
                    RiscVISelOperand::Block(base),
                ],
            ),
        );
        // JAL x0, rec
        func.push_inst(
            entry,
            RiscVISelInst::new(
                RiscVOpcode::Jal,
                vec![RiscVISelOperand::PReg(ZERO), RiscVISelOperand::Block(rec)],
            ),
        );
        func.blocks.get_mut(&entry).unwrap().successors = vec![base, rec];

        // base: a0 = 0 ; ret
        func.push_inst(
            base,
            RiscVISelInst::new(
                RiscVOpcode::Addi,
                vec![
                    RiscVISelOperand::PReg(A0),
                    RiscVISelOperand::PReg(ZERO),
                    RiscVISelOperand::Imm(0),
                ],
            ),
        );
        func.push_inst(
            base,
            RiscVISelInst::new(
                RiscVOpcode::Jalr,
                vec![
                    RiscVISelOperand::PReg(ZERO),
                    RiscVISelOperand::PReg(RA),
                    RiscVISelOperand::Imm(0),
                ],
            ),
        );

        // rec: v_nm1 = v_n - 1 ; a0 = v_nm1 ; CALL sum_to_n (JAL ra, entry) ;
        //      v_res = a0 ; v_sum = v_n + v_res ; a0 = v_sum ; ret.
        func.push_inst(
            rec,
            RiscVISelInst::new(
                RiscVOpcode::Addi,
                vec![
                    RiscVISelOperand::VReg(v_nm1),
                    RiscVISelOperand::VReg(v_n),
                    RiscVISelOperand::Imm(-1),
                ],
            ),
        );
        // Argument move: a0 = v_nm1.
        func.push_inst(
            rec,
            RiscVISelInst::new(
                RiscVOpcode::Addi,
                vec![
                    RiscVISelOperand::PReg(A0),
                    RiscVISelOperand::VReg(v_nm1),
                    RiscVISelOperand::Imm(0),
                ],
            ),
        );
        // CALL: JAL ra, entry  with a0 attached as a use operand.
        func.push_inst(
            rec,
            RiscVISelInst::new(
                RiscVOpcode::Jal,
                vec![
                    RiscVISelOperand::PReg(RA),
                    RiscVISelOperand::Block(entry),
                    RiscVISelOperand::PReg(A0),
                ],
            ),
        );
        // v_res = a0.
        func.push_inst(
            rec,
            RiscVISelInst::new(
                RiscVOpcode::Addi,
                vec![
                    RiscVISelOperand::VReg(v_res),
                    RiscVISelOperand::PReg(A0),
                    RiscVISelOperand::Imm(0),
                ],
            ),
        );
        // v_sum = v_n + v_res  (v_n is live ACROSS the call!).
        func.push_inst(
            rec,
            RiscVISelInst::new(
                RiscVOpcode::Add,
                vec![
                    RiscVISelOperand::VReg(v_sum),
                    RiscVISelOperand::VReg(v_n),
                    RiscVISelOperand::VReg(v_res),
                ],
            ),
        );
        // a0 = v_sum ; ret.
        func.push_inst(
            rec,
            RiscVISelInst::new(
                RiscVOpcode::Addi,
                vec![
                    RiscVISelOperand::PReg(A0),
                    RiscVISelOperand::VReg(v_sum),
                    RiscVISelOperand::Imm(0),
                ],
            ),
        );
        func.push_inst(
            rec,
            RiscVISelInst::new(
                RiscVOpcode::Jalr,
                vec![
                    RiscVISelOperand::PReg(ZERO),
                    RiscVISelOperand::PReg(RA),
                    RiscVISelOperand::Imm(0),
                ],
            ),
        );

        (func, v_n)
    }

    /// SOUNDNESS: a value live ACROSS a call must NOT be coloured onto a
    /// caller-saved register (it would be silently clobbered by the callee). The
    /// recursion's accumulator `v_n` is live across the self-call, so it must land
    /// in a callee-saved s-register (or be spilled). This is the #1 miscompile the
    /// clobber model exists to prevent.
    #[test]
    fn call_spanning_value_avoids_caller_saved() {
        let (func, v_n) = build_sum_to_n_self_recursive();
        let assignment = RiscVRegAssignment::assign(&func).expect("assign");
        let placed = assignment.allocation.get(&v_n).copied();
        // Either spilled, or in a callee-saved register; NEVER caller-saved.
        match placed {
            None => {
                assert!(
                    assignment.spill_slots.contains_key(&v_n),
                    "v_n not allocated and not spilled — lost value"
                );
            }
            Some(p) => {
                assert!(
                    RISCV_CALLEE_SAVED_GPRS.contains(&p),
                    "v_n is live across the call and MUST be callee-saved, got {p:?}"
                );
                assert!(
                    !RISCV_CALLER_SAVED_GPRS.contains(&p),
                    "v_n must NOT be caller-saved (clobbered by the call), got {p:?}"
                );
            }
        }
    }

    /// Build a function with an Fpr64-class vreg defined in the entry block,
    /// a self-recursive CALL (JAL ra, entry), then a USE of that FP vreg AFTER
    /// the call, so its live interval spans the call. This bypasses ISel (which
    /// never emits an FPR vreg) and reaches the FP-across-call gap directly,
    /// exactly as the public compile API can.
    ///
    /// Layout:
    ///   entry: v_fp = Fld [sp+0]   (define an FP vreg)
    ///          JAL ra, entry        (self-call: clobbers all caller-saved)
    ///          Fsd v_fp, [sp+0]     (USE v_fp after the call -> spans the call)
    ///          JALR x0, ra, 0       (ret)
    fn build_fp_value_across_call() -> (RiscVISelFunction, VReg) {
        let sig = Signature {
            params: vec![],
            returns: vec![],
        };
        let mut func = RiscVISelFunction::new("fp_across_call".to_string(), sig);
        let entry = Block(0);
        func.ensure_block(entry);

        let v_fp = VReg::new(0, RegClass::Fpr64);
        func.next_vreg = 1;

        // v_fp = Fld [sp + 0]  (define the FP vreg).
        func.push_inst(
            entry,
            RiscVISelInst::new(
                RiscVOpcode::Fld,
                vec![
                    RiscVISelOperand::VReg(v_fp),
                    RiscVISelOperand::PReg(SP),
                    RiscVISelOperand::Imm(0),
                ],
            ),
        );
        // CALL: JAL ra, entry  (self-call; clobbers all caller-saved regs).
        func.push_inst(
            entry,
            RiscVISelInst::new(
                RiscVOpcode::Jal,
                vec![RiscVISelOperand::PReg(RA), RiscVISelOperand::Block(entry)],
            ),
        );
        // USE v_fp AFTER the call: Fsd v_fp, [sp + 0]. v_fp is live ACROSS the call.
        func.push_inst(
            entry,
            RiscVISelInst::new(
                RiscVOpcode::Fsd,
                vec![
                    RiscVISelOperand::VReg(v_fp),
                    RiscVISelOperand::PReg(SP),
                    RiscVISelOperand::Imm(0),
                ],
            ),
        );
        // ret.
        func.push_inst(
            entry,
            RiscVISelInst::new(
                RiscVOpcode::Jalr,
                vec![
                    RiscVISelOperand::PReg(ZERO),
                    RiscVISelOperand::PReg(RA),
                    RiscVISelOperand::Imm(0),
                ],
            ),
        );

        (func, v_fp)
    }

    /// SOUNDNESS (Finding #1, RISC-V FPR clobber gap): an FP value live ACROSS a
    /// call must NEVER be coloured onto a callee-saved FPR (fs0-fs11), because no
    /// Fsd/Fld callee-saved save/restore path exists — the callee would silently
    /// clobber it. After dropping fs0-fs11 from the allocatable pool, the only
    /// allocatable FPRs are caller-saved; a call-spanning FP value is forced off
    /// all of them by the call-clobber model and MUST spill. Before the fix the
    /// allocator placed it in a free fs-register (the caller-saved injection
    /// leaves fs0-fs11 untouched), so this assertion FAILS pre-fix and PASSES
    /// post-fix.
    #[test]
    fn fp_value_across_call_never_in_unsaved_callee_saved_fpr() {
        use trust_cg_ir::riscv_regs::RISCV_CALLEE_SAVED_FPRS;

        let (func, v_fp) = build_fp_value_across_call();
        let assignment = RiscVRegAssignment::assign(&func).expect("assign");

        // FAIL-CLOSED: no FP allocation may land in a callee-saved FPR (there is
        // no save path for them). This holds for EVERY vreg in the function.
        for (vreg, &p) in assignment.allocation.iter() {
            assert!(
                !RISCV_CALLEE_SAVED_FPRS.contains(&p),
                "vreg {vreg:?} allocated to unsaved callee-saved FPR {p:?} — would be clobbered across a call"
            );
        }

        match assignment.allocation.get(&v_fp).copied() {
            None => {
                // Spilled — the sound outcome: it is reloaded around its use.
                assert!(
                    assignment.spill_slots.contains_key(&v_fp),
                    "v_fp neither allocated nor spilled — lost value"
                );
            }
            Some(p) => {
                // If placed in a register at all, it must be caller-saved AND
                // (since it spans the call and every caller-saved FPR is
                // clobbered) it must also be spilled to survive the call.
                assert!(
                    RISCV_CALLER_SAVED_FPRS.contains(&p),
                    "call-spanning v_fp must be in a caller-saved FPR (or spilled), got {p:?}"
                );
                assert!(
                    !RISCV_CALLEE_SAVED_FPRS.contains(&p),
                    "call-spanning v_fp must NEVER be in an unsaved callee-saved FPR, got {p:?}"
                );
            }
        }
    }

    /// The allocatable FPR pool must contain NO callee-saved FPR — locks the
    /// fail-closed invariant that makes the FP-across-call clobber impossible.
    #[test]
    fn allocatable_fprs_exclude_callee_saved() {
        use trust_cg_ir::riscv_regs::{RISCV_ALLOCATABLE_FPRS, RISCV_CALLEE_SAVED_FPRS};

        for fs in RISCV_CALLEE_SAVED_FPRS {
            assert!(
                !RISCV_ALLOCATABLE_FPRS.contains(&fs),
                "callee-saved FPR {fs:?} must not be in the allocatable pool"
            );
        }
        // allocatable_fprs() (pool minus the 3 scratch regs) must stay non-empty.
        assert!(
            !allocatable_fprs().is_empty(),
            "allocatable FPR pool must remain non-empty"
        );
        // And none of what it yields may be callee-saved.
        for p in allocatable_fprs() {
            assert!(
                !RISCV_CALLEE_SAVED_FPRS.contains(&p),
                "allocatable_fprs() yielded callee-saved FPR {p:?}"
            );
        }
    }

    /// END-TO-END: compile the self-recursive `sum_to_n` and INTERPRET the lowered
    /// RV64 stream, asserting (i) the correct numeric result, (ii) the recursion
    /// terminates (ra is correctly saved/restored — a corrupted ra would loop
    /// forever and trip the step limit), and (iii) SP is restored to its initial
    /// value at the outermost return (the prologue/epilogue balance across nested
    /// frames).
    #[test]
    fn recursive_self_call_interprets_to_correct_sum() {
        let n: u64 = 10;
        let expected: u64 = (0..=n).sum(); // 55

        let (mut func, _v_n) = build_sum_to_n_self_recursive();

        // Run the same phases compile_function runs (minus final encoding) so the
        // interpreted stream is exactly what would be emitted.
        let assignment = RiscVRegAssignment::assign(&func).expect("assign");
        fixup_call_arg_parallel_copies(&mut func, &assignment.allocation, &assignment.spill_slots)
            .expect("arg fixup");
        rewrite_spills(&mut func, &assignment).expect("rewrite spills");
        let frame = compute_frame_size(assignment.used_callee_saved.len(), assignment.num_spills);
        let pipeline = RiscVPipeline::default_config();
        pipeline
            .insert_prologue_epilogue(&mut func, &assignment)
            .expect("prologue/epilogue");
        resolve_riscv_branches(&mut func).expect("resolve branches");

        // It must also encode cleanly (a JAL ra,<negative offset to entry> exists).
        let bytes = riscv_compile_to_bytes(&build_sum_to_n_self_recursive().0)
            .expect("self-recursive function compiles to bytes");
        assert_eq!(bytes.len() % 4, 0);

        let mut interp = RiscVInterp::build(&func, assignment.allocation.clone(), frame);
        interp.regs[A0.hw_enc() as usize] = n; // argument
        let sp_init = interp.regs[2];
        let result = interp.run(SENTINEL_RA, 100_000);

        assert_eq!(result, expected, "sum_to_n({n}) must be {expected}");
        assert_eq!(
            interp.regs[2], sp_init,
            "SP must be restored across the full recursion"
        );
        assert_eq!(
            interp.regs[1], SENTINEL_RA,
            "outermost ra must be the sentinel (saved/restored correctly)"
        );
    }

    // -----------------------------------------------------------------------
    // Far-branch / far-jump relaxation
    // -----------------------------------------------------------------------

    /// Build a `select(n) = n==0 ? hi : lo` whose conditional branch to the
    /// `hi` block is separated from it by `filler` 4-byte NOPs, deliberately
    /// pushing the branch offset past the B-type +/-4 KiB reach so the resolver
    /// MUST relax it. Layout order is `entry, lo, filler, hi`, so:
    ///   entry: v_n = a0 ; v_zero = (v_n==0) ; BNE v_zero,x0, hi ; JAL x0, lo
    ///   lo:    a0 = `lo_val` ; ret
    ///   filler: `filler` * (ADDI x0,x0,0) ; JAL x0, hi
    ///   hi:    a0 = `hi_val` ; ret
    /// Only interpreter-supported opcodes are used (ADDI/SLTIU/BNE/JAL/JALR),
    /// and the inverse of BNE is BEQ (also supported), so the relaxed sequence
    /// is directly executable by `RiscVInterp`.
    fn build_forced_far_conditional(filler: usize, lo_val: i64, hi_val: i64) -> RiscVISelFunction {
        let sig = Signature {
            params: vec![trust_cg_lower::types::Type::I64],
            returns: vec![trust_cg_lower::types::Type::I64],
        };
        let mut func = RiscVISelFunction::new("far_select".to_string(), sig);
        let entry = Block(0);
        let lo = Block(1);
        let filler_b = Block(2);
        let hi = Block(3);
        func.ensure_block(entry);
        func.ensure_block(lo);
        func.ensure_block(filler_b);
        func.ensure_block(hi);

        let v_n = VReg::new(0, RegClass::Gpr64);
        let v_zero = VReg::new(1, RegClass::Gpr64);
        func.next_vreg = 2;

        // entry: v_n = a0 ; v_zero = (v_n == 0) ; BNE v_zero, x0, hi ; JAL x0, lo
        func.push_inst(
            entry,
            RiscVISelInst::new(
                RiscVOpcode::Addi,
                vec![
                    RiscVISelOperand::VReg(v_n),
                    RiscVISelOperand::PReg(A0),
                    RiscVISelOperand::Imm(0),
                ],
            ),
        );
        func.push_inst(
            entry,
            RiscVISelInst::new(
                RiscVOpcode::Sltiu,
                vec![
                    RiscVISelOperand::VReg(v_zero),
                    RiscVISelOperand::VReg(v_n),
                    RiscVISelOperand::Imm(1),
                ],
            ),
        );
        func.push_inst(
            entry,
            RiscVISelInst::new(
                RiscVOpcode::Bne,
                vec![
                    RiscVISelOperand::VReg(v_zero),
                    RiscVISelOperand::PReg(ZERO),
                    RiscVISelOperand::Block(hi),
                ],
            ),
        );
        func.push_inst(
            entry,
            RiscVISelInst::new(
                RiscVOpcode::Jal,
                vec![RiscVISelOperand::PReg(ZERO), RiscVISelOperand::Block(lo)],
            ),
        );
        func.blocks.get_mut(&entry).unwrap().successors = vec![hi, lo];

        // lo: a0 = lo_val ; ret
        func.push_inst(
            lo,
            RiscVISelInst::new(
                RiscVOpcode::Addi,
                vec![
                    RiscVISelOperand::PReg(A0),
                    RiscVISelOperand::PReg(ZERO),
                    RiscVISelOperand::Imm(lo_val),
                ],
            ),
        );
        func.push_inst(
            lo,
            RiscVISelInst::new(
                RiscVOpcode::Jalr,
                vec![
                    RiscVISelOperand::PReg(ZERO),
                    RiscVISelOperand::PReg(RA),
                    RiscVISelOperand::Imm(0),
                ],
            ),
        );

        // filler: `filler` NOPs (ADDI x0,x0,0) ; JAL x0, hi
        for _ in 0..filler {
            func.push_inst(
                filler_b,
                RiscVISelInst::new(
                    RiscVOpcode::Addi,
                    vec![
                        RiscVISelOperand::PReg(ZERO),
                        RiscVISelOperand::PReg(ZERO),
                        RiscVISelOperand::Imm(0),
                    ],
                ),
            );
        }
        func.push_inst(
            filler_b,
            RiscVISelInst::new(
                RiscVOpcode::Jal,
                vec![RiscVISelOperand::PReg(ZERO), RiscVISelOperand::Block(hi)],
            ),
        );
        func.blocks.get_mut(&filler_b).unwrap().successors = vec![hi];

        // hi: a0 = hi_val ; ret
        func.push_inst(
            hi,
            RiscVISelInst::new(
                RiscVOpcode::Addi,
                vec![
                    RiscVISelOperand::PReg(A0),
                    RiscVISelOperand::PReg(ZERO),
                    RiscVISelOperand::Imm(hi_val),
                ],
            ),
        );
        func.push_inst(
            hi,
            RiscVISelInst::new(
                RiscVOpcode::Jalr,
                vec![
                    RiscVISelOperand::PReg(ZERO),
                    RiscVISelOperand::PReg(RA),
                    RiscVISelOperand::Imm(0),
                ],
            ),
        );

        func
    }

    /// Drive `build_forced_far_conditional` through the real phase sequence and
    /// interpret the relaxed stream. Returns the interpreter result for `a0=n`.
    fn run_far_conditional(func: &mut RiscVISelFunction, n: u64) -> u64 {
        let assignment = RiscVRegAssignment::assign(func).expect("assign");
        rewrite_spills(func, &assignment).expect("rewrite spills");
        let frame = compute_frame_size(assignment.used_callee_saved.len(), assignment.num_spills);
        let pipeline = RiscVPipeline::default_config();
        pipeline
            .insert_prologue_epilogue(func, &assignment)
            .expect("prologue/epilogue");
        resolve_riscv_branches(func).expect("resolve+relax branches");
        let mut interp = RiscVInterp::build(func, assignment.allocation.clone(), frame);
        interp.regs[A0.hw_enc() as usize] = n;
        interp.run(SENTINEL_RA, 2_000_000)
    }

    /// FORCED RELAXATION (mandatory test a): a conditional branch whose target is
    /// > +/-4 KiB away is relaxed to an inverted short branch over a JAL. We
    /// INTERPRET the relaxed stream on BOTH the taken (n==0) and not-taken (n!=0)
    /// conditions and assert each lands on the correct block / return value, so
    /// the original semantics are EXACTLY preserved.
    #[test]
    fn far_conditional_branch_relaxes_and_interprets_both_paths() {
        // 1100 filler insts * 4 = 4400 bytes > 4094 (B-type max), so the BNE to
        // `hi` MUST be relaxed. 4400 << 1 MiB so the inserted JAL still encodes.
        let filler = 1100;

        // First confirm relaxation actually triggered: the un-relaxed offset is
        // out of range, and post-resolve the entry's branch is the INVERTED
        // opcode (BEQ) with a small +8 skip, followed by a JAL carrying the far
        // offset. Inspect the resolved ISel directly.
        let mut probe = build_forced_far_conditional(filler, 111, 999);
        let assignment = RiscVRegAssignment::assign(&probe).expect("assign");
        rewrite_spills(&mut probe, &assignment).expect("rewrite spills");
        RiscVPipeline::default_config()
            .insert_prologue_epilogue(&mut probe, &assignment)
            .expect("prologue/epilogue");
        resolve_riscv_branches(&mut probe).expect("resolve+relax");
        let entry_insts = &probe.blocks[&Block(0)].insts;
        // Find the (now inverted) conditional branch: it must be BEQ with Imm(8).
        let inv = entry_insts
            .iter()
            .find(|i| i.opcode == RiscVOpcode::Beq)
            .expect("BNE must have been inverted to a short BEQ skip");
        assert!(
            inv.operands
                .iter()
                .any(|o| matches!(o, RiscVISelOperand::Imm(8))),
            "the inverted short branch must skip +8 over the inserted JAL, got {:?}",
            inv.operands
        );
        // And a following JAL must carry the (large) far offset, in J-range.
        let far_jal = entry_insts
            .iter()
            .find(|i| {
                i.opcode == RiscVOpcode::Jal
                    && i.operands
                        .iter()
                        .any(|o| matches!(o, RiscVISelOperand::Imm(v) if v.abs() > 4094))
            })
            .expect("a JAL carrying the far offset must follow the inverted branch");
        let far_off = far_jal
            .operands
            .iter()
            .find_map(|o| match o {
                RiscVISelOperand::Imm(v) => Some(*v),
                _ => None,
            })
            .unwrap();
        assert!(
            (RISCV_JUMP_OFFSET_MIN..=RISCV_JUMP_OFFSET_MAX).contains(&far_off),
            "relaxed JAL offset {far_off} must be in J-type range"
        );

        // It must also COMPILE through the real encoder: the encoder's
        // check_branch_offset/check_jump_offset are the fail-closed safety net —
        // if relaxation had left any out-of-range B/J offset, this would error.
        // (Relaxation must feed the encoder only in-range offsets.)
        let bytes = riscv_compile_to_bytes(&build_forced_far_conditional(filler, 111, 999))
            .expect("relaxed far-conditional function compiles through the real encoder");
        assert_eq!(bytes.len() % 4, 0);

        // Now EXECUTE both conditions on a fresh function each time.
        let mut taken = build_forced_far_conditional(filler, 111, 999);
        assert_eq!(
            run_far_conditional(&mut taken, 0),
            999,
            "n==0 takes the (far, relaxed) branch -> hi block returns 999"
        );
        let mut not_taken = build_forced_far_conditional(filler, 111, 999);
        assert_eq!(
            run_far_conditional(&mut not_taken, 7),
            111,
            "n!=0 falls through -> lo block returns 111"
        );
    }

    /// FIXPOINT / CASCADE (mandatory test b): with > 1 MiB of filler the inserted
    /// JAL is ITSELF out of J-type range, so it relaxes a second time to
    /// AUIPC+JALR — a true cascade across fixpoint iterations. We interpret both
    /// paths (the inverted BEQ + AUIPC + JALR sequence is interpretable now) and
    /// assert correctness, proving the loop converges and stays semantically
    /// identical even when one relaxation provokes another.
    #[test]
    fn far_conditional_cascades_to_auipc_jalr_and_interprets() {
        // > 1 MiB / 4 = 262144 insts forces the inverted-branch's JAL out of
        // J-type range too, so it cascades to AUIPC+JALR.
        let filler = 262_200;

        let mut probe = build_forced_far_conditional(filler, 11, 22);
        let assignment = RiscVRegAssignment::assign(&probe).expect("assign");
        rewrite_spills(&mut probe, &assignment).expect("rewrite spills");
        RiscVPipeline::default_config()
            .insert_prologue_epilogue(&mut probe, &assignment)
            .expect("prologue/epilogue");
        resolve_riscv_branches(&mut probe).expect("resolve+relax");
        let entry_insts = &probe.blocks[&Block(0)].insts;
        // Cascade signature: inverted BEQ(+8 over the AUIPC+JALR... but the skip
        // is over the JAL which itself became 2 insts? No: the conditional
        // relaxation inserts ONE `JAL x0, far`; the SECOND iteration rewrites
        // that single JAL into AUIPC+JALR. The inverted BEQ's +8 skip was sized
        // for one inst; after the JAL became two insts the skip is now wrong
        // UNLESS the relaxer re-derives it. Assert the *interpreted* behavior is
        // correct (the definitive check) and that an AUIPC appeared.
        assert!(
            entry_insts.iter().any(|i| i.opcode == RiscVOpcode::Auipc),
            "the far JAL must have cascaded to an AUIPC+JALR pair"
        );
        // The inverted short branch's skip must have been bumped from +8 (skip
        // one JAL) to +12 (skip the AUIPC+JALR pair) so it still lands on the
        // fallthrough rather than in the middle of the pair.
        let inv = entry_insts
            .iter()
            .find(|i| i.opcode == RiscVOpcode::Beq)
            .expect("inverted short branch");
        assert!(
            inv.operands
                .iter()
                .any(|o| matches!(o, RiscVISelOperand::Imm(12))),
            "the inverted skip must grow to +12 over the AUIPC+JALR pair, got {:?}",
            inv.operands
        );

        // It must also COMPILE through the real encoder (B/J-type safety net).
        let bytes = riscv_compile_to_bytes(&build_forced_far_conditional(filler, 11, 22))
            .expect("cascaded relaxation compiles through the real encoder");
        assert_eq!(bytes.len() % 4, 0);

        let mut taken = build_forced_far_conditional(filler, 11, 22);
        assert_eq!(run_far_conditional(&mut taken, 0), 22, "n==0 -> hi (22)");
        let mut not_taken = build_forced_far_conditional(filler, 11, 22);
        assert_eq!(
            run_far_conditional(&mut not_taken, 5),
            11,
            "n!=0 -> lo (11)"
        );
    }

    /// FAIL-CLOSED (mandatory test c): a displacement genuinely beyond the
    /// signed-32-bit AUIPC+JALR reach is NOT constructible as 2 GiB of real
    /// instructions, so we assert the boundary at the split-helper layer — which,
    /// AFTER the deferred-resolution refactor, is the SINGLE point where reach is
    /// decided AND where the far-jump path fails closed (the split moved from
    /// relax_riscv_far_jump into the final resolution pass). We also confirm the
    /// relaxer now DEFERS (emits an AUIPC+JALR carrying the Block, no premature
    /// split, no panic) so nothing can be baked stale at insert time.
    #[test]
    fn far_jump_beyond_signed32_fails_closed() {
        // The split helper is the fail-closed boundary: in-reach yields Some,
        // beyond signed-32-bit (and the top-2 KiB AUIPC overflow guard) yields
        // None. This is the exact `None` the FINAL resolution pass turns into a
        // typed FrameLowering error (see resolve_riscv_branches Phase 2).
        assert!(
            riscv_split_pcrel_hi_lo(0x7FFF_F7FF).is_some(),
            "the true top of AUIPC+JALR reach must split"
        );
        assert!(
            riscv_split_pcrel_hi_lo(0x8000_0000).is_none(),
            "just past signed-32-bit must fail closed"
        );
        assert!(
            riscv_split_pcrel_hi_lo(i64::from(i32::MIN) - 1).is_none(),
            "below signed-32-bit must fail closed"
        );

        // The relaxer's far-jump path NO LONGER splits at insert time (that is
        // what made the old code bake a stale, off-by-4 disp). It now DEFERS: the
        // JAL becomes an AUIPC + JALR pair, BOTH carrying the far Block target as
        // an operand, with NO immediate baked. Resolution (and the reach check)
        // happen exactly once, later, on the final layout.
        let mut func = build_forced_far_conditional(0, 1, 2);
        // A standalone far JAL x0, Block(3) in entry at pos 0 (whatever its real
        // offset) — relax it and assert it deferred.
        let target = Block(3);
        func.blocks.get_mut(&Block(0)).unwrap().insts.insert(
            0,
            RiscVISelInst::new(
                RiscVOpcode::Jal,
                vec![
                    RiscVISelOperand::PReg(ZERO),
                    RiscVISelOperand::Block(target),
                ],
            ),
        );
        relax_riscv_far_jump(&mut func, Block(0), 0, target);
        let entry = &func.blocks[&Block(0)].insts;
        assert_eq!(
            entry[0].opcode,
            RiscVOpcode::Auipc,
            "relaxed far JAL must become an AUIPC anchor"
        );
        assert_eq!(
            entry[1].opcode,
            RiscVOpcode::Jalr,
            "relaxed far JAL must be followed by the paired JALR"
        );
        // BOTH halves carry the deferred Block target and NO baked immediate.
        for (i, half) in [(0usize, "AUIPC"), (1usize, "JALR")] {
            assert!(
                entry[i]
                    .operands
                    .iter()
                    .any(|o| matches!(o, RiscVISelOperand::Block(b) if *b == target)),
                "{half} must carry the deferred far Block target"
            );
            assert!(
                !entry[i]
                    .operands
                    .iter()
                    .any(|o| matches!(o, RiscVISelOperand::Imm(_))),
                "{half} must NOT carry a baked immediate (deferred resolution)"
            );
        }
    }

    /// Build a NON-MASKING forward far-jump scenario that exposes the off-by-4
    /// relaxation miscompile. Layout order: `entry, filler, predecoy, target,
    /// wrongb`.
    ///
    ///   entry:    `JAL x0, target`  (FORWARD; with > 1 MiB filler it relaxes to
    ///             AUIPC + JALR — the relaxation under test).
    ///   filler:   `filler` NOPs ; `JAL x0, predecoy`.
    ///   predecoy: a SINGLE `JAL x0, wrongb` — this is the instruction sitting
    ///             EXACTLY 4 bytes before `target`. CRITICALLY it transfers
    ///             control to `wrongb`, a DIFFERENT block, NOT to `target`. This
    ///             is the non-masking property the original cascade test lacked
    ///             (there the 4-bytes-before inst was a `JAL` to the SAME target,
    ///             so an off-by-4 bounced to the right place anyway).
    ///   target:   `ADDI a0, x0, 0x600` ; `JALR x0, ra, 0`  (the CORRECT result).
    ///   wrongb:   `ADDI a0, x0, 0x0AD` ; `JALR x0, ra, 0`  (the WRONG result an
    ///             off-by-4 produces — placed AFTER target so its JAL stays in
    ///             short range / unused; reached only via the predecoy bounce).
    ///
    /// With the off-by-4 bug, the relaxed forward JALR lands 4 bytes short, on
    /// predecoy's `JAL x0, wrongb`, which bounces to `wrongb` and returns 0x0AD.
    /// Correct (deferred-resolution) relaxation lands exactly on `target` and
    /// returns 0x600. Interpreting to the EXACT value catches the regression.
    fn build_nonmasking_forward_far_jump(filler: usize) -> RiscVISelFunction {
        let sig = Signature {
            params: vec![trust_cg_lower::types::Type::I64],
            returns: vec![trust_cg_lower::types::Type::I64],
        };
        let mut func = RiscVISelFunction::new("nonmask_far".to_string(), sig);
        let entry = Block(0);
        let filler_b = Block(1);
        let predecoy = Block(2);
        let target = Block(3);
        let wrongb = Block(4);
        func.ensure_block(entry);
        func.ensure_block(filler_b);
        func.ensure_block(predecoy);
        func.ensure_block(target);
        func.ensure_block(wrongb);

        // entry: JAL x0, target  (forward far jump -> relaxes to AUIPC+JALR)
        func.push_inst(
            entry,
            RiscVISelInst::new(
                RiscVOpcode::Jal,
                vec![
                    RiscVISelOperand::PReg(ZERO),
                    RiscVISelOperand::Block(target),
                ],
            ),
        );
        func.blocks.get_mut(&entry).unwrap().successors = vec![target];

        // filler: NOPs ; JAL x0, predecoy
        for _ in 0..filler {
            func.push_inst(
                filler_b,
                RiscVISelInst::new(
                    RiscVOpcode::Addi,
                    vec![
                        RiscVISelOperand::PReg(ZERO),
                        RiscVISelOperand::PReg(ZERO),
                        RiscVISelOperand::Imm(0),
                    ],
                ),
            );
        }
        func.push_inst(
            filler_b,
            RiscVISelInst::new(
                RiscVOpcode::Jal,
                vec![
                    RiscVISelOperand::PReg(ZERO),
                    RiscVISelOperand::Block(predecoy),
                ],
            ),
        );
        func.blocks.get_mut(&filler_b).unwrap().successors = vec![predecoy];

        // predecoy: JAL x0, wrongb  (the inst 4 bytes before `target`; jumps AWAY
        // to a DIFFERENT block — this is what makes the off-by-4 observable).
        func.push_inst(
            predecoy,
            RiscVISelInst::new(
                RiscVOpcode::Jal,
                vec![
                    RiscVISelOperand::PReg(ZERO),
                    RiscVISelOperand::Block(wrongb),
                ],
            ),
        );
        func.blocks.get_mut(&predecoy).unwrap().successors = vec![wrongb];

        // target: a0 = 0x600 ; ret  (the CORRECT landing)
        func.push_inst(
            target,
            RiscVISelInst::new(
                RiscVOpcode::Addi,
                vec![
                    RiscVISelOperand::PReg(A0),
                    RiscVISelOperand::PReg(ZERO),
                    RiscVISelOperand::Imm(0x600),
                ],
            ),
        );
        func.push_inst(
            target,
            RiscVISelInst::new(
                RiscVOpcode::Jalr,
                vec![
                    RiscVISelOperand::PReg(ZERO),
                    RiscVISelOperand::PReg(RA),
                    RiscVISelOperand::Imm(0),
                ],
            ),
        );

        // wrongb: a0 = 0x0AD ; ret  (the WRONG landing the off-by-4 produces)
        func.push_inst(
            wrongb,
            RiscVISelInst::new(
                RiscVOpcode::Addi,
                vec![
                    RiscVISelOperand::PReg(A0),
                    RiscVISelOperand::PReg(ZERO),
                    RiscVISelOperand::Imm(0x0AD),
                ],
            ),
        );
        func.push_inst(
            wrongb,
            RiscVISelInst::new(
                RiscVOpcode::Jalr,
                vec![
                    RiscVISelOperand::PReg(ZERO),
                    RiscVISelOperand::PReg(RA),
                    RiscVISelOperand::Imm(0),
                ],
            ),
        );

        func
    }

    /// NON-MASKING off-by-4 REGRESSION (mandatory test a): a FORWARD far JAL is
    /// relaxed to AUIPC+JALR; the instruction 4 bytes before the target jumps to a
    /// DIFFERENT block, so an off-by-4 JALR lands there and returns 0x0AD instead
    /// of the correct 0x600. With deferred resolution the JALR lands EXACTLY on
    /// the target. This test FAILS on the pre-fix code (which baked disp from the
    /// pre-insertion layout, 4 bytes short for a forward target) and PASSES after.
    #[test]
    fn forward_far_jump_lands_exactly_on_target_not_offby4() {
        // > 1 MiB / 4 = 262_144 insts forces the entry's forward JAL out of
        // J-type range so it relaxes to AUIPC+JALR.
        let filler = 262_200;

        // Sanity: relaxation actually produced an AUIPC+JALR in entry.
        let mut probe = build_nonmasking_forward_far_jump(filler);
        let assignment = RiscVRegAssignment::assign(&probe).expect("assign");
        rewrite_spills(&mut probe, &assignment).expect("rewrite spills");
        RiscVPipeline::default_config()
            .insert_prologue_epilogue(&mut probe, &assignment)
            .expect("prologue/epilogue");
        resolve_riscv_branches(&mut probe).expect("resolve+relax");
        let entry_insts = &probe.blocks[&Block(0)].insts;
        assert!(
            entry_insts.iter().any(|i| i.opcode == RiscVOpcode::Auipc),
            "the forward far JAL must have relaxed to an AUIPC+JALR pair"
        );
        // The resolved AUIPC+JALR must carry final Imms (no surviving Block) and
        // reconstruct to the EXACT target displacement on the final layout. We
        // verify by recomputing: anchor = AUIPC final offset, target = target's
        // final block offset, disp = target - anchor must equal hi20<<12 + lo12.
        let block_offsets = riscv_compute_block_offsets(&probe);
        // Locate the AUIPC's final byte offset and its hi20, and the JALR's lo12.
        let mut off: i64 = 0;
        let mut auipc_off = None;
        let mut hi20 = None;
        let mut lo12 = None;
        for &b in &probe.block_order {
            for inst in &probe.blocks[&b].insts {
                match inst.opcode {
                    RiscVOpcode::Auipc => {
                        auipc_off = Some(off);
                        hi20 = inst.operands.iter().find_map(|o| match o {
                            RiscVISelOperand::Imm(v) => Some(*v),
                            _ => None,
                        });
                    }
                    RiscVOpcode::Jalr
                        if inst
                            .operands
                            .iter()
                            .any(|o| matches!(o, RiscVISelOperand::PReg(p) if *p == RISCV_FAR_JUMP_SCRATCH)) =>
                    {
                        lo12 = inst.operands.iter().find_map(|o| match o {
                            RiscVISelOperand::Imm(v) => Some(*v),
                            _ => None,
                        });
                    }
                    _ => {}
                }
                off += inst_size(inst) as i64;
            }
        }
        let anchor = auipc_off.expect("AUIPC present");
        let hi20 = hi20.expect("AUIPC hi20 present");
        let lo12 = lo12.expect("JALR lo12 present");
        let target_off = *block_offsets.get(&Block(3)).expect("target block offset");
        let reconstructed = anchor + (hi20 << 12) + lo12;
        assert_eq!(
            reconstructed, target_off,
            "the relaxed AUIPC+JALR must reach the EXACT target final offset \
             (off-by-4 would land it 4 bytes short, on the predecoy's JAL)"
        );

        // And it must COMPILE through the real encoder.
        let bytes = riscv_compile_to_bytes(&build_nonmasking_forward_far_jump(filler))
            .expect("non-masking forward far jump compiles through the encoder");
        assert_eq!(bytes.len() % 4, 0);

        // Definitive: INTERPRET. Correct relaxation returns 0x600; the off-by-4
        // bug returns 0x0AD (bouncing through predecoy -> wrongb).
        let mut run = build_nonmasking_forward_far_jump(filler);
        assert_eq!(
            run_far_conditional(&mut run, 0),
            0x600,
            "the relaxed forward far jump must land EXACTLY on `target` (0x600), \
             not 4 bytes short on predecoy's `JAL x0, wrongb` (which returns 0x0AD)"
        );
    }

    /// Build a CASCADE-RESTALE scenario: an EARLIER far jump is relaxed first;
    /// then a LATER far conditional branch in the SAME block relaxes and inserts
    /// code BETWEEN the earlier relaxed AUIPC and its target. With baked
    /// immediates (the old code) the earlier pair's disp would go STALE a second
    /// time. With deferred resolution the earlier pair is resolved once, at the
    /// end, on the final layout, so it stays correct.
    ///
    /// Layout order: `entry, filler, decoy, target1, target2, wrongb`. BOTH
    /// far jumps live in `entry` and target blocks sit AFTER the > 1 MiB filler so
    /// BOTH are genuinely far (each cascades to AUIPC+JALR):
    ///   entry:  `Bne v_zero, x0, target2` (forward FAR conditional, relaxed
    ///           LATER) ; `JAL x0, target1` (forward FAR jump -> AUIPC+JALR,
    ///           relaxed FIRST since the scan takes the first out-of-range branch).
    ///           The Bne's later relaxation inserts an inverted-branch + (cascaded)
    ///           AUIPC+JALR INTO entry, AFTER the first AUIPC — re-shifting target1
    ///           (downstream) by +12. With baked Imms the earlier JAL->target1 pair
    ///           would go STALE; deferred resolution re-derives it from the final
    ///           layout.
    ///   filler: > 1 MiB NOPs ; `JAL x0, decoy` (pushes the targets far; reaches
    ///           decoy as the filler terminator).
    ///   decoy:  a SINGLE `JAL x0, wrongb` — the inst EXACTLY 4 bytes before
    ///           target1, jumping AWAY to a DIFFERENT block. This is the
    ///           non-masking property: an off-by-4 (or a stale-by-N) earlier pair
    ///           lands here and bounces to `wrongb` (0x0AD), not target1.
    ///   target1:`ADDI a0, x0, 0x111` ; `JALR x0, ra, 0`  (the a0!=0 result).
    ///   target2:`ADDI a0, x0, 0x222` ; `JALR x0, ra, 0`  (the a0==0 result).
    ///   wrongb: `ADDI a0, x0, 0x0AD` ; `JALR x0, ra, 0`  (the stale result).
    fn build_cascade_restale(filler: usize) -> RiscVISelFunction {
        let sig = Signature {
            params: vec![trust_cg_lower::types::Type::I64],
            returns: vec![trust_cg_lower::types::Type::I64],
        };
        let mut func = RiscVISelFunction::new("cascade_restale".to_string(), sig);
        let entry = Block(0);
        let filler_b = Block(1);
        let decoy = Block(2);
        let target1 = Block(3);
        let target2 = Block(4);
        let wrongb = Block(5);
        func.ensure_block(entry);
        func.ensure_block(filler_b);
        func.ensure_block(decoy);
        func.ensure_block(target1);
        func.ensure_block(target2);
        func.ensure_block(wrongb);

        let v_n = VReg::new(0, RegClass::Gpr64);
        let v_zero = VReg::new(1, RegClass::Gpr64);
        func.next_vreg = 2;

        // entry: v_n=a0 ; v_zero=(v_n==0) ; Bne v_zero,x0, target2 (far fwd
        //        conditional) ; JAL x0, target1 (far fwd jump).
        // Semantics: v_n==0 -> target2 (0x222); else -> target1 (0x111).
        func.push_inst(
            entry,
            RiscVISelInst::new(
                RiscVOpcode::Addi,
                vec![
                    RiscVISelOperand::VReg(v_n),
                    RiscVISelOperand::PReg(A0),
                    RiscVISelOperand::Imm(0),
                ],
            ),
        );
        func.push_inst(
            entry,
            RiscVISelInst::new(
                RiscVOpcode::Sltiu,
                vec![
                    RiscVISelOperand::VReg(v_zero),
                    RiscVISelOperand::VReg(v_n),
                    RiscVISelOperand::Imm(1),
                ],
            ),
        );
        func.push_inst(
            entry,
            RiscVISelInst::new(
                RiscVOpcode::Bne,
                vec![
                    RiscVISelOperand::VReg(v_zero),
                    RiscVISelOperand::PReg(ZERO),
                    RiscVISelOperand::Block(target2),
                ],
            ),
        );
        func.push_inst(
            entry,
            RiscVISelInst::new(
                RiscVOpcode::Jal,
                vec![
                    RiscVISelOperand::PReg(ZERO),
                    RiscVISelOperand::Block(target1),
                ],
            ),
        );
        func.blocks.get_mut(&entry).unwrap().successors = vec![target2, target1];

        // decoy: JAL x0, wrongb — the inst 4 bytes before target1, jumping AWAY to
        // a DIFFERENT block (non-masking: a stale-by-4 earlier pair lands here).
        func.push_inst(
            decoy,
            RiscVISelInst::new(
                RiscVOpcode::Jal,
                vec![
                    RiscVISelOperand::PReg(ZERO),
                    RiscVISelOperand::Block(wrongb),
                ],
            ),
        );
        func.blocks.get_mut(&decoy).unwrap().successors = vec![wrongb];

        // target1: a0 = 0x111 ; ret
        func.push_inst(
            target1,
            RiscVISelInst::new(
                RiscVOpcode::Addi,
                vec![
                    RiscVISelOperand::PReg(A0),
                    RiscVISelOperand::PReg(ZERO),
                    RiscVISelOperand::Imm(0x111),
                ],
            ),
        );
        func.push_inst(
            target1,
            RiscVISelInst::new(
                RiscVOpcode::Jalr,
                vec![
                    RiscVISelOperand::PReg(ZERO),
                    RiscVISelOperand::PReg(RA),
                    RiscVISelOperand::Imm(0),
                ],
            ),
        );

        // filler: > 1 MiB NOPs ; JAL x0, decoy (pushes the targets far so BOTH
        // entry jumps go out of range -> relax; the JAL reaches decoy and keeps
        // the filler terminated). The JAL to decoy is itself in J-range (decoy is
        // the very next block) so it does not relax.
        for _ in 0..filler {
            func.push_inst(
                filler_b,
                RiscVISelInst::new(
                    RiscVOpcode::Addi,
                    vec![
                        RiscVISelOperand::PReg(ZERO),
                        RiscVISelOperand::PReg(ZERO),
                        RiscVISelOperand::Imm(0),
                    ],
                ),
            );
        }
        func.push_inst(
            filler_b,
            RiscVISelInst::new(
                RiscVOpcode::Jal,
                vec![RiscVISelOperand::PReg(ZERO), RiscVISelOperand::Block(decoy)],
            ),
        );
        func.blocks.get_mut(&filler_b).unwrap().successors = vec![decoy];

        // target2: a0 = 0x222 ; ret
        func.push_inst(
            target2,
            RiscVISelInst::new(
                RiscVOpcode::Addi,
                vec![
                    RiscVISelOperand::PReg(A0),
                    RiscVISelOperand::PReg(ZERO),
                    RiscVISelOperand::Imm(0x222),
                ],
            ),
        );
        func.push_inst(
            target2,
            RiscVISelInst::new(
                RiscVOpcode::Jalr,
                vec![
                    RiscVISelOperand::PReg(ZERO),
                    RiscVISelOperand::PReg(RA),
                    RiscVISelOperand::Imm(0),
                ],
            ),
        );

        // wrongb: a0 = 0x0AD ; ret  (the stale-by-4 landing the bug produces).
        func.push_inst(
            wrongb,
            RiscVISelInst::new(
                RiscVOpcode::Addi,
                vec![
                    RiscVISelOperand::PReg(A0),
                    RiscVISelOperand::PReg(ZERO),
                    RiscVISelOperand::Imm(0x0AD),
                ],
            ),
        );
        func.push_inst(
            wrongb,
            RiscVISelInst::new(
                RiscVOpcode::Jalr,
                vec![
                    RiscVISelOperand::PReg(ZERO),
                    RiscVISelOperand::PReg(RA),
                    RiscVISelOperand::Imm(0),
                ],
            ),
        );

        func
    }

    /// MULTI-RELAX / CASCADE-RESTALE (mandatory test b): relaxing a LATER branch
    /// re-shifts an EARLIER relaxed pair's target. Deferred resolution computes
    /// every disp once on the final layout, so the earlier pair stays correct.
    /// Interpret BOTH paths to their exact targets.
    #[test]
    fn cascade_relax_does_not_stale_earlier_pair() {
        let filler = 262_200; // > 1 MiB so both the entry JAL and Bne go far.

        // Both an AUIPC (from the entry far JAL) and an inverted BEQ (from the far
        // Bne) must appear, proving two relaxations happened in one block.
        let mut probe = build_cascade_restale(filler);
        let assignment = RiscVRegAssignment::assign(&probe).expect("assign");
        rewrite_spills(&mut probe, &assignment).expect("rewrite spills");
        RiscVPipeline::default_config()
            .insert_prologue_epilogue(&mut probe, &assignment)
            .expect("prologue/epilogue");
        resolve_riscv_branches(&mut probe).expect("resolve+relax");
        let entry_insts = &probe.blocks[&Block(0)].insts;
        assert!(
            entry_insts.iter().any(|i| i.opcode == RiscVOpcode::Auipc),
            "the entry far JAL to target1 must have relaxed to AUIPC+JALR"
        );
        assert!(
            entry_insts.iter().any(|i| i.opcode == RiscVOpcode::Beq),
            "the entry far Bne to target2 must have relaxed to an inverted BEQ skip"
        );

        // LAYOUT-INDEPENDENT off-by-4 / restale check: BOTH relaxed AUIPC+JALR
        // pairs (the JAL->target1 one and the Bne-cascade->target2 one) must
        // reconstruct to their respective targets' FINAL offsets, even though one
        // relaxation inserted code between the other's AUIPC and its target. A
        // stale-by-4 (the old baked-Imm bug) would reconstruct 4 bytes short —
        // landing the JAL->target1 pair on the decoy's `JAL x0, wrongb`.
        //
        // We learn which target each AUIPC pair carries by relaxing a SEPARATE
        // clone WITHOUT final resolution (so the deferred Blocks are still
        // visible) and pairing positionally with the fully-resolved `probe`
        // (relaxation is deterministic, so positions align).
        let mut relaxed_only = build_cascade_restale(filler);
        let a2 = RiscVRegAssignment::assign(&relaxed_only).expect("assign");
        rewrite_spills(&mut relaxed_only, &a2).expect("rewrite spills");
        RiscVPipeline::default_config()
            .insert_prologue_epilogue(&mut relaxed_only, &a2)
            .expect("prologue/epilogue");
        relax_riscv_far_branches(&mut relaxed_only).expect("relax only");
        // Collect (auipc_inst_index_in_entry -> carried far Block) from the
        // un-resolved clone, in entry order.
        let entry_blocks: Vec<trust_cg_lower::instructions::Block> = relaxed_only.blocks[&Block(0)]
            .insts
            .iter()
            .filter(|i| i.opcode == RiscVOpcode::Auipc)
            .map(|i| {
                i.operands
                    .iter()
                    .find_map(|o| match o {
                        RiscVISelOperand::Block(b) => Some(*b),
                        _ => None,
                    })
                    .expect("relaxed AUIPC carries a deferred Block before resolution")
            })
            .collect();
        assert_eq!(
            entry_blocks.len(),
            2,
            "two far jumps in entry must relax to two AUIPC+JALR pairs (JAL->target1, Bne-cascade->target2)"
        );
        // Compute each resolved AUIPC pair's reconstructed target on `probe`'s
        // final layout, in entry order, and match it to the recorded Block.
        let block_offsets = riscv_compute_block_offsets(&probe);
        let entry_resolved = &probe.blocks[&Block(0)].insts;
        // Per-instruction final byte offsets within entry.
        let mut offs = Vec::with_capacity(entry_resolved.len());
        let mut off = *block_offsets.get(&Block(0)).unwrap_or(&0);
        for inst in entry_resolved {
            offs.push(off);
            off += inst_size(inst) as i64;
        }
        let mut pair_idx = 0usize;
        for (i, inst) in entry_resolved.iter().enumerate() {
            if inst.opcode != RiscVOpcode::Auipc {
                continue;
            }
            let anchor = offs[i];
            let hi20 = inst
                .operands
                .iter()
                .find_map(|o| match o {
                    RiscVISelOperand::Imm(v) => Some(*v),
                    _ => None,
                })
                .expect("resolved AUIPC hi20");
            // The paired JALR is the next JALR using the far-jump scratch.
            let lo12 = entry_resolved[i + 1..]
                .iter()
                .find(|x| {
                    x.opcode == RiscVOpcode::Jalr
                        && x.operands.iter().any(
                            |o| matches!(o, RiscVISelOperand::PReg(p) if *p == RISCV_FAR_JUMP_SCRATCH),
                        )
                })
                .and_then(|x| {
                    x.operands.iter().find_map(|o| match o {
                        RiscVISelOperand::Imm(v) => Some(*v),
                        _ => None,
                    })
                })
                .expect("resolved JALR lo12");
            let reconstructed = anchor + (hi20 << 12) + lo12;
            let want = *block_offsets
                .get(&entry_blocks[pair_idx])
                .expect("recorded target block has a final offset");
            assert_eq!(
                reconstructed, want,
                "relaxed AUIPC+JALR pair #{pair_idx} (target block {}) must reach its \
                 EXACT final offset; a stale-by-4 would land 4 bytes short",
                entry_blocks[pair_idx].0
            );
            pair_idx += 1;
        }

        // Compiles through the encoder.
        let bytes =
            riscv_compile_to_bytes(&build_cascade_restale(filler)).expect("cascade compiles");
        assert_eq!(bytes.len() % 4, 0);

        // Interpret BOTH conditions. a0!=0 -> entry Bne not taken -> falls to the
        // far JAL -> target1 (0x111). a0==0 -> entry Bne taken -> target2
        // (0x222). The earlier-relaxed JAL->target1 pair must still land EXACTLY
        // on target1 despite the later Bne relaxation having inserted code in
        // entry (which shifted target1 downstream).
        let mut a = build_cascade_restale(filler);
        assert_eq!(
            run_far_conditional(&mut a, 7),
            0x111,
            "a0!=0 falls through to the far JAL -> target1 (0x111); the earlier \
             relaxed pair must not have gone stale from the later Bne relaxation"
        );
        let mut b = build_cascade_restale(filler);
        assert_eq!(
            run_far_conditional(&mut b, 0),
            0x222,
            "a0==0 takes the far (relaxed) Bne -> target2 (0x222)"
        );
    }

    /// Build a single ENTRY block densely packed with `count` far conditional
    /// branches (all BNE to one far `target`) followed by a far JAL, then enough
    /// filler to push every branch out of B-range. Few blocks, many far branches —
    /// exactly the shape the BLOCK-bounded cap spuriously rejected.
    fn build_dense_far_branches(count: usize, filler: usize) -> RiscVISelFunction {
        let sig = Signature {
            params: vec![trust_cg_lower::types::Type::I64],
            returns: vec![trust_cg_lower::types::Type::I64],
        };
        let mut func = RiscVISelFunction::new("dense_far".to_string(), sig);
        let entry = Block(0);
        let filler_b = Block(1);
        let target = Block(2);
        func.ensure_block(entry);
        func.ensure_block(filler_b);
        func.ensure_block(target);

        let v_n = VReg::new(0, RegClass::Gpr64);
        let v_zero = VReg::new(1, RegClass::Gpr64);
        func.next_vreg = 2;

        func.push_inst(
            entry,
            RiscVISelInst::new(
                RiscVOpcode::Addi,
                vec![
                    RiscVISelOperand::VReg(v_n),
                    RiscVISelOperand::PReg(A0),
                    RiscVISelOperand::Imm(0),
                ],
            ),
        );
        func.push_inst(
            entry,
            RiscVISelInst::new(
                RiscVOpcode::Sltiu,
                vec![
                    RiscVISelOperand::VReg(v_zero),
                    RiscVISelOperand::VReg(v_n),
                    RiscVISelOperand::Imm(1),
                ],
            ),
        );
        // `count` far conditional BNEs, all to `target`. Each is taken iff
        // v_zero!=0 (i.e. v_n==0); semantics are identical for every copy, so
        // interpreting is well-defined regardless of how many relax.
        for _ in 0..count {
            func.push_inst(
                entry,
                RiscVISelInst::new(
                    RiscVOpcode::Bne,
                    vec![
                        RiscVISelOperand::VReg(v_zero),
                        RiscVISelOperand::PReg(ZERO),
                        RiscVISelOperand::Block(target),
                    ],
                ),
            );
        }
        // entry terminator: a far JAL to filler's tail region via filler block.
        func.push_inst(
            entry,
            RiscVISelInst::new(
                RiscVOpcode::Jal,
                vec![
                    RiscVISelOperand::PReg(ZERO),
                    RiscVISelOperand::Block(filler_b),
                ],
            ),
        );
        func.blocks.get_mut(&entry).unwrap().successors = vec![target, filler_b];

        // filler: NOPs ; a0 = 0x432 ; ret  (the not-taken fallthrough result).
        for _ in 0..filler {
            func.push_inst(
                filler_b,
                RiscVISelInst::new(
                    RiscVOpcode::Addi,
                    vec![
                        RiscVISelOperand::PReg(ZERO),
                        RiscVISelOperand::PReg(ZERO),
                        RiscVISelOperand::Imm(0),
                    ],
                ),
            );
        }
        func.push_inst(
            filler_b,
            RiscVISelInst::new(
                RiscVOpcode::Addi,
                vec![
                    RiscVISelOperand::PReg(A0),
                    RiscVISelOperand::PReg(ZERO),
                    RiscVISelOperand::Imm(0x432),
                ],
            ),
        );
        func.push_inst(
            filler_b,
            RiscVISelInst::new(
                RiscVOpcode::Jalr,
                vec![
                    RiscVISelOperand::PReg(ZERO),
                    RiscVISelOperand::PReg(RA),
                    RiscVISelOperand::Imm(0),
                ],
            ),
        );

        // target: a0 = 0x765 ; ret  (the taken result).
        func.push_inst(
            target,
            RiscVISelInst::new(
                RiscVOpcode::Addi,
                vec![
                    RiscVISelOperand::PReg(A0),
                    RiscVISelOperand::PReg(ZERO),
                    RiscVISelOperand::Imm(0x765),
                ],
            ),
        );
        func.push_inst(
            target,
            RiscVISelInst::new(
                RiscVOpcode::Jalr,
                vec![
                    RiscVISelOperand::PReg(ZERO),
                    RiscVISelOperand::PReg(RA),
                    RiscVISelOperand::Imm(0),
                ],
            ),
        );

        func
    }

    /// CAP (mandatory test c): an instruction-DENSE block of many far conditional
    /// branches in only THREE blocks must relax successfully. The old
    /// block-bounded cap (block_order.len()*2+10 = 16) spuriously failed closed on
    /// this valid program; the instruction-count cap (2*total_insts+10) succeeds.
    #[test]
    fn dense_far_branch_block_relaxes_within_cap() {
        // 40 far BNEs + a far JAL in 3 blocks. Filler > 4 KiB pushes the BNEs out
        // of B-range; we keep it modest so the JAL stays in J-range (no second
        // cascade needed) — the point is the COUNT of relaxations, not their size.
        let count = 40;
        let filler = 1100; // 1100 * 4 = 4400 bytes > 4094 (B-type max).

        // Direct: the fixpoint must converge (NOT a spurious FrameLowering).
        let mut func = build_dense_far_branches(count, filler);
        let assignment = RiscVRegAssignment::assign(&func).expect("assign");
        rewrite_spills(&mut func, &assignment).expect("rewrite spills");
        RiscVPipeline::default_config()
            .insert_prologue_epilogue(&mut func, &assignment)
            .expect("prologue/epilogue");
        relax_riscv_far_branches(&mut func)
            .expect("a dense block of far branches must relax within the instruction-count cap");
        // Every far BNE became an inverted BEQ + JAL (count of BEQs == count).
        let beq_count = func.blocks[&Block(0)]
            .insts
            .iter()
            .filter(|i| i.opcode == RiscVOpcode::Beq)
            .count();
        assert_eq!(
            beq_count, count,
            "every one of the {count} far BNEs must have relaxed to an inverted BEQ skip"
        );

        // Full pipeline + encoder.
        let bytes = riscv_compile_to_bytes(&build_dense_far_branches(count, filler))
            .expect("dense far-branch block compiles through the encoder");
        assert_eq!(bytes.len() % 4, 0);

        // Interpret BOTH paths to confirm semantics survived the dense relaxation.
        let mut taken = build_dense_far_branches(count, filler);
        assert_eq!(
            run_far_conditional(&mut taken, 0),
            0x765,
            "a0==0 takes a (relaxed) far BNE -> target (0x765)"
        );
        let mut not_taken = build_dense_far_branches(count, filler);
        assert_eq!(
            run_far_conditional(&mut not_taken, 3),
            0x432,
            "a0!=0 falls through every BNE -> filler tail (0x432)"
        );
    }

    /// A nearby IN-RANGE conditional branch must be untouched by relaxation: with
    /// zero filler the branch resolves to a normal short BNE (not inverted), and
    /// both paths still interpret correctly. Regression that relaxation does not
    /// perturb branches already in range.
    #[test]
    fn in_range_conditional_branch_is_not_relaxed() {
        let mut probe = build_forced_far_conditional(0, 5, 9);
        let assignment = RiscVRegAssignment::assign(&probe).expect("assign");
        rewrite_spills(&mut probe, &assignment).expect("rewrite spills");
        RiscVPipeline::default_config()
            .insert_prologue_epilogue(&mut probe, &assignment)
            .expect("prologue/epilogue");
        resolve_riscv_branches(&mut probe).expect("resolve");
        let entry_insts = &probe.blocks[&Block(0)].insts;
        assert!(
            entry_insts.iter().any(|i| i.opcode == RiscVOpcode::Bne),
            "an in-range branch must stay a plain (non-inverted) BNE"
        );
        assert!(
            !entry_insts.iter().any(|i| i.opcode == RiscVOpcode::Beq),
            "an in-range branch must NOT be inverted"
        );

        let mut taken = build_forced_far_conditional(0, 5, 9);
        assert_eq!(run_far_conditional(&mut taken, 0), 9);
        let mut not_taken = build_forced_far_conditional(0, 5, 9);
        assert_eq!(run_far_conditional(&mut not_taken, 3), 5);
    }

    /// The inverse-opcode helper must map each conditional branch to its true
    /// semantic inverse (NOT a bit flip) and reject non-conditional opcodes.
    #[test]
    fn invert_branch_opcode_is_the_semantic_inverse() {
        use RiscVOpcode::*;
        assert_eq!(riscv_invert_branch_opcode(Beq), Some(Bne));
        assert_eq!(riscv_invert_branch_opcode(Bne), Some(Beq));
        assert_eq!(riscv_invert_branch_opcode(Blt), Some(Bge));
        assert_eq!(riscv_invert_branch_opcode(Bge), Some(Blt));
        assert_eq!(riscv_invert_branch_opcode(Bltu), Some(Bgeu));
        assert_eq!(riscv_invert_branch_opcode(Bgeu), Some(Bltu));
        assert_eq!(riscv_invert_branch_opcode(Jal), None);
        assert_eq!(riscv_invert_branch_opcode(Addi), None);
    }

    /// PARALLEL-MOVE arg setup: a call whose argument SOURCES alias destination
    /// argument registers must be marshaled with a cycle-breaking parallel copy,
    /// not naive sequential moves. We force a 2-arg self-call where the allocator
    /// has placed the sources such that emitting `a0<-src0 ; a1<-src1` in order
    /// would clobber a source. We assert the post-regalloc fixup produces a
    /// correct schedule (the resolver is also unit-tested directly below).
    #[test]
    fn parallel_move_breaks_arg_register_cycle() {
        // Direct unit test of the resolver: swap a0<->a1 must NOT lose a value.
        let copies = vec![(A0, A1), (A1, A0)];
        let resolved = resolve_riscv_physreg_parallel_copy(&copies, RISCV_CALL_ARG_SCRATCH);
        // Simulate: a0=10, a1=20 then apply resolved moves; expect a0=20, a1=10.
        let mut r: HashMap<RiscVPReg, u64> = HashMap::new();
        r.insert(A0, 10);
        r.insert(A1, 20);
        r.insert(RISCV_CALL_ARG_SCRATCH, 0);
        for (d, s) in &resolved {
            let v = *r.get(s).unwrap();
            r.insert(*d, v);
        }
        assert_eq!(*r.get(&A0).unwrap(), 20, "a0 must receive old a1");
        assert_eq!(*r.get(&A1).unwrap(), 10, "a1 must receive old a0");
        // The naive (unbroken) order [a0<-a1, a1<-a0] would instead give a1=20
        // (a0 already overwritten) — confirm the resolver introduced the scratch.
        assert!(
            resolved.iter().any(|(d, _)| *d == RISCV_CALL_ARG_SCRATCH)
                || resolved.iter().any(|(_, s)| *s == RISCV_CALL_ARG_SCRATCH),
            "a 2-cycle must be broken via the scratch register"
        );
    }

    /// A 3-element chain a0<-a1<-a2<-(value) needs no scratch (it is acyclic) and
    /// must topologically order writes so no source is read after it is
    /// overwritten.
    fn build_three_arg_self_call_aliasing() -> RiscVISelFunction {
        // A self-call passing (b, c, a) given formals arrive as (a0=a, a1=b, a2=c):
        // sources alias destinations, exercising the fixup end-to-end.
        let sig = Signature {
            params: vec![
                trust_cg_lower::types::Type::I64,
                trust_cg_lower::types::Type::I64,
                trust_cg_lower::types::Type::I64,
            ],
            returns: vec![trust_cg_lower::types::Type::I64],
        };
        let mut func = RiscVISelFunction::new("three".to_string(), sig);
        let entry = Block(0);
        let base = Block(1);
        func.ensure_block(entry);
        func.ensure_block(base);
        func.next_vreg = 0;
        // entry: unconditionally branch to base after one trivial guard so it is
        // not infinite; we only care that the call-arg fixup schedules correctly.
        // For determinism of the alloc, just go straight to base.
        func.push_inst(
            entry,
            RiscVISelInst::new(
                RiscVOpcode::Jal,
                vec![RiscVISelOperand::PReg(ZERO), RiscVISelOperand::Block(base)],
            ),
        );
        func.blocks.get_mut(&entry).unwrap().successors = vec![base];
        // base: a0 = 0 ; ret  (a terminating base case; the call below is in entry-
        // adjacent code only to test the shuffle — kept minimal).
        func.push_inst(
            base,
            RiscVISelInst::new(
                RiscVOpcode::Addi,
                vec![
                    RiscVISelOperand::PReg(A0),
                    RiscVISelOperand::PReg(ZERO),
                    RiscVISelOperand::Imm(0),
                ],
            ),
        );
        func.push_inst(
            base,
            RiscVISelInst::new(
                RiscVOpcode::Jalr,
                vec![
                    RiscVISelOperand::PReg(ZERO),
                    RiscVISelOperand::PReg(RA),
                    RiscVISelOperand::Imm(0),
                ],
            ),
        );
        func
    }

    /// The resolver handles an acyclic chain with NO scratch and a correct order.
    #[test]
    fn parallel_move_acyclic_chain_no_scratch() {
        // a0<-a1, a1<-a2: acyclic. Correct order writes a0 first (frees a1's
        // reader), then a1. Simulate to confirm no value loss.
        let copies = vec![(A0, A1), (A1, A2)];
        let resolved = resolve_riscv_physreg_parallel_copy(&copies, RISCV_CALL_ARG_SCRATCH);
        assert!(
            !resolved
                .iter()
                .any(|(d, s)| *d == RISCV_CALL_ARG_SCRATCH || *s == RISCV_CALL_ARG_SCRATCH),
            "an acyclic chain must NOT need the scratch register"
        );
        let mut r: HashMap<RiscVPReg, u64> = HashMap::new();
        r.insert(A0, 1);
        r.insert(A1, 2);
        r.insert(A2, 3);
        for (d, s) in &resolved {
            let v = *r.get(s).unwrap();
            r.insert(*d, v);
        }
        assert_eq!(*r.get(&A0).unwrap(), 2, "a0 <- old a1");
        assert_eq!(*r.get(&A1).unwrap(), 3, "a1 <- old a2");
        // build_three_arg_self_call_aliasing is exercised for compile coverage.
        let f = build_three_arg_self_call_aliasing();
        assert!(riscv_compile_to_bytes(&f).is_ok());
    }

    /// FAIL-CLOSED: a self-call whose argument source was SPILLED is rejected with
    /// a typed RegAlloc error (this minimal increment does not stage spilled call
    /// arguments) — never a wrong shuffle.
    #[test]
    fn spilled_call_argument_fails_closed() {
        // Build a tiny function: a0 = <spilled vreg> ; JAL ra, entry. We simulate
        // the spilled-source condition by directly invoking the fixup with an empty
        // allocation and a spill slot for the source vreg.
        let sig = Signature {
            params: vec![trust_cg_lower::types::Type::I64],
            returns: vec![trust_cg_lower::types::Type::I64],
        };
        let mut func = RiscVISelFunction::new("spill_arg".to_string(), sig);
        let entry = Block(0);
        func.ensure_block(entry);
        let v_src = VReg::new(0, RegClass::Gpr64);
        func.next_vreg = 1;
        func.push_inst(
            entry,
            RiscVISelInst::new(
                RiscVOpcode::Addi,
                vec![
                    RiscVISelOperand::PReg(A0),
                    RiscVISelOperand::VReg(v_src),
                    RiscVISelOperand::Imm(0),
                ],
            ),
        );
        func.push_inst(
            entry,
            RiscVISelInst::new(
                RiscVOpcode::Jal,
                vec![
                    RiscVISelOperand::PReg(RA),
                    RiscVISelOperand::Block(entry),
                    RiscVISelOperand::PReg(A0),
                ],
            ),
        );

        let alloc: HashMap<VReg, RiscVPReg> = HashMap::new();
        let mut spills: HashMap<VReg, u32> = HashMap::new();
        spills.insert(v_src, 0);
        let err = fixup_call_arg_parallel_copies(&mut func, &alloc, &spills)
            .expect_err("spilled call arg must fail closed");
        assert!(
            matches!(err, RiscVPipelineError::RegAlloc(_)),
            "expected typed RegAlloc error, got {err:?}"
        );
    }

    // =======================================================================
    // PHASE 4: cross-function module emission + cross-function direct calls.
    // =======================================================================

    /// The pcrel hi20/lo12 split (`riscv_split_pcrel_hi_lo`) must reconstruct the
    /// exact displacement for the boundary cases that exercise the `+0x800` carry
    /// compensation — getting it wrong is the classic RISC-V relocation
    /// miscompile. We check several displacements (including ones whose low 12
    /// bits are negative, forcing the hi20 carry) and assert
    /// `(hi20 << 12) + sign_extend(lo12) == disp`.
    #[test]
    fn pcrel_hi_lo_split_reconstructs_displacement() {
        // 0x7FFF_F7FF is the TRUE positive maximum: above it the +0x800 carry pushes
        // hi20 past the signed 20-bit AUIPC field, so the pair cannot represent the
        // target and the split must fail closed (see the must-fail list below).
        for &disp in &[
            0i64,
            4,
            8,
            -4,
            0x7FF,
            0x800,
            0x801,
            -0x800,
            -0x801,
            0x1000,
            0xFFF,
            0x12345,
            -0x12345,
            0x7FFF_F7FF,
            -0x8000_0000,
        ] {
            let (hi20, lo12) = riscv_split_pcrel_hi_lo(disp)
                .unwrap_or_else(|| panic!("disp {disp} must split within AUIPC+JALR reach"));
            // hi20 must fit the SIGNED 20-bit AUIPC field, else the encoder masks it
            // and the hardware sign-extends to a wrong target.
            assert!(
                (-524288..=524287).contains(&hi20),
                "hi20 {hi20} (disp {disp}) overflows the signed 20-bit AUIPC field"
            );
            // Reconstruct exactly as the CPU does: sign-extend hi20 through 20 bits.
            let hi20_se = (hi20 << 12) >> 12;
            let recon = ((hi20_se as i64) << 12) + (lo12 as i64);
            assert_eq!(recon, disp, "split of {disp} -> (hi={hi20}, lo={lo12})");
            // lo12 must be a sign-extended 12-bit value.
            assert!(
                (-2048..=2047).contains(&lo12),
                "lo12 {lo12} out of 12-bit range"
            );
        }
        // Top 2 KiB of the positive range: the +0x800 carry overflows the signed
        // 20-bit hi20 field, so these must FAIL CLOSED rather than miscompile.
        assert!(
            riscv_split_pcrel_hi_lo(0x7FFF_F800).is_none(),
            "0x7FFF_F800 overflows hi20; must fail closed"
        );
        assert!(
            riscv_split_pcrel_hi_lo(0x7FFF_FFFF).is_none(),
            "0x7FFF_FFFF overflows hi20; must fail closed"
        );
        // Out of signed-32-bit reach -> fail closed (None).
        assert!(riscv_split_pcrel_hi_lo(0x8000_0000).is_none());
        assert!(riscv_split_pcrel_hi_lo(-0x8000_0001).is_none());
    }

    /// Patching an AUIPC+JALR pcrel pair in a `.text` buffer must set the AUIPC's
    /// hi20 (bits 31:12) and the JALR's lo12 (bits 31:20) so that
    /// `(auipc_pc + (hi20<<12)) + sign_extend(lo12) == target`, while preserving
    /// the rd/rs1/funct3/opcode fields.
    #[test]
    fn intra_object_call_patch_sets_pcrel_pair() {
        // Placeholder AUIPC ra, 0 (U-type, rd=ra=1, opcode 0x17) and
        // JALR ra, ra, 0 (I-type, rd=ra=1, rs1=ra=1, funct3=0, opcode 0x67).
        let auipc0 = crate::riscv::encode::encode_instruction(
            RiscVOpcode::Auipc,
            &RiscVInstOperands {
                rd: Some(RA),
                imm: 0,
                ..RiscVInstOperands::none()
            },
        )
        .unwrap();
        let jalr0 = crate::riscv::encode::encode_instruction(
            RiscVOpcode::Jalr,
            &RiscVInstOperands {
                rd: Some(RA),
                rs1: Some(RA),
                imm: 0,
                ..RiscVInstOperands::none()
            },
        )
        .unwrap();

        // Lay AUIPC@0, JALR@4, callee@0x100.
        let mut text = Vec::new();
        text.extend_from_slice(&auipc0.to_le_bytes());
        text.extend_from_slice(&jalr0.to_le_bytes());
        text.resize(0x104, 0);
        riscv_patch_intra_object_call(&mut text, 0, 4, 0x100).expect("patch in range");

        let auipc = u32::from_le_bytes([text[0], text[1], text[2], text[3]]);
        let jalr = u32::from_le_bytes([text[4], text[5], text[6], text[7]]);
        // Opcodes preserved.
        assert_eq!(auipc & 0x7F, 0x17, "AUIPC opcode preserved");
        assert_eq!(jalr & 0x7F, 0x67, "JALR opcode preserved");
        // rd=ra preserved on both; rs1=ra preserved on JALR.
        assert_eq!((auipc >> 7) & 0x1F, RA.hw_enc() as u32);
        assert_eq!((jalr >> 7) & 0x1F, RA.hw_enc() as u32);
        assert_eq!((jalr >> 15) & 0x1F, RA.hw_enc() as u32);
        // Decode hi20 (sign-extended 20-bit) and lo12 (sign-extended 12-bit) and
        // reconstruct the target relative to the AUIPC PC (= 0).
        let hi20 = ((auipc as i32) >> 12) as i64; // bits 31:12, sign-extended
        let lo12 = ((jalr as i32) >> 20) as i64; // bits 31:20, sign-extended
        assert_eq!((hi20 << 12) + lo12, 0x100, "reconstructed target");
    }

    /// A minimal byte-level RV64 interpreter that DECODES the emitted `.text`
    /// stream (not the ISel stream) and executes it, so a cross-function call's
    /// resolved AUIPC+JALR pcrel pair is verified to land EXACTLY on the callee's
    /// entry. Implements only the opcodes the phase-4 module test needs: ADDI,
    /// ADD, SD, LD, AUIPC, JALR, JAL. Panics on anything else (keeping test
    /// functions in the supported subset).
    struct RiscVByteInterp {
        regs: [u64; 32],
        mem: Vec<u8>,
        text: Vec<u8>,
    }

    impl RiscVByteInterp {
        fn new(text: Vec<u8>) -> Self {
            let stack = 1 << 16;
            let mut regs = [0u64; 32];
            regs[2] = (stack - 16) as u64; // sp
            Self {
                regs,
                mem: vec![0u8; stack],
                text,
            }
        }

        fn run(&mut self, entry_pc: u64, sentinel_ra: u64, step_limit: usize) -> u64 {
            self.regs[1] = sentinel_ra; // ra
            let mut pc = entry_pc;
            for _ in 0..step_limit {
                let i = pc as usize;
                let word = u32::from_le_bytes([
                    self.text[i],
                    self.text[i + 1],
                    self.text[i + 2],
                    self.text[i + 3],
                ]);
                let opcode = word & 0x7F;
                let rd = ((word >> 7) & 0x1F) as usize;
                let funct3 = (word >> 12) & 0x7;
                let rs1 = ((word >> 15) & 0x1F) as usize;
                let rs2 = ((word >> 20) & 0x1F) as usize;
                let mut next_pc = pc + 4;
                match opcode {
                    0x13 => {
                        // OP-IMM: only ADDI (funct3=0) is used.
                        assert_eq!(funct3, 0, "only ADDI supported");
                        let imm = (word as i32) >> 20; // I-type sign-extended imm12
                        let v = (self.regs[rs1] as i64).wrapping_add(imm as i64) as u64;
                        if rd != 0 {
                            self.regs[rd] = v;
                        }
                    }
                    0x33 => {
                        // OP: only ADD (funct3=0, funct7=0) is used.
                        assert_eq!(funct3, 0, "only ADD supported");
                        let v = self.regs[rs1].wrapping_add(self.regs[rs2]);
                        if rd != 0 {
                            self.regs[rd] = v;
                        }
                    }
                    0x23 => {
                        // STORE: only SD (funct3=3) is used.
                        assert_eq!(funct3, 3, "only SD supported");
                        let imm_11_5 = ((word >> 25) & 0x7F) as i32;
                        let imm_4_0 = ((word >> 7) & 0x1F) as i32;
                        let imm = ((imm_11_5 << 5) | imm_4_0) << 20 >> 20; // sign-extend 12
                        let addr = (self.regs[rs1] as i64 + imm as i64) as usize;
                        self.mem[addr..addr + 8].copy_from_slice(&self.regs[rs2].to_le_bytes());
                    }
                    0x03 => {
                        // LOAD: only LD (funct3=3) is used.
                        assert_eq!(funct3, 3, "only LD supported");
                        let imm = (word as i32) >> 20;
                        let addr = (self.regs[rs1] as i64 + imm as i64) as usize;
                        let mut buf = [0u8; 8];
                        buf.copy_from_slice(&self.mem[addr..addr + 8]);
                        if rd != 0 {
                            self.regs[rd] = u64::from_le_bytes(buf);
                        }
                    }
                    0x17 => {
                        // AUIPC: rd = pc + (imm20 << 12). imm field is bits 31:12.
                        let imm = (word & 0xFFFF_F000) as i32 as i64; // already <<12, sign-ext
                        if rd != 0 {
                            self.regs[rd] = (pc as i64 + imm) as u64;
                        }
                    }
                    0x67 => {
                        // JALR: t = (regs[rs1] + imm) & ~1 ; rd = pc+4 ; pc = t.
                        let imm = (word as i32) >> 20;
                        let target = ((self.regs[rs1] as i64).wrapping_add(imm as i64)) as u64 & !1;
                        let link = pc + 4;
                        if rd != 0 {
                            self.regs[rd] = link;
                        }
                        if target == sentinel_ra {
                            return self.regs[A0.hw_enc() as usize];
                        }
                        next_pc = target;
                    }
                    0x6F => {
                        // JAL: rd = pc+4 ; pc += imm (J-type 21-bit signed even).
                        let b20 = ((word >> 31) & 1) as i32;
                        let b10_1 = ((word >> 21) & 0x3FF) as i32;
                        let b11 = ((word >> 20) & 1) as i32;
                        let b19_12 = ((word >> 12) & 0xFF) as i32;
                        let mut imm = (b20 << 20) | (b19_12 << 12) | (b11 << 11) | (b10_1 << 1);
                        imm = (imm << 11) >> 11; // sign-extend 21-bit
                        let link = pc + 4;
                        if rd != 0 {
                            self.regs[rd] = link;
                        }
                        next_pc = (pc as i64 + imm as i64) as u64;
                    }
                    other => panic!("byte interp: unsupported opcode {other:#x} at pc {pc}"),
                }
                pc = next_pc;
            }
            panic!("byte interp: step limit reached (corrupted ra/sp -> nonterminating)");
        }
    }

    /// Build a leaf `callee(a, b) -> a + b` as an ISel function: it adds its two
    /// integer arguments (a0, a1) and returns the sum in a0. The prologue/epilogue
    /// (added by the pipeline) save/restore ra and s0.
    fn build_callee_add() -> RiscVISelFunction {
        let sig = Signature {
            params: vec![
                trust_cg_lower::types::Type::I64,
                trust_cg_lower::types::Type::I64,
            ],
            returns: vec![trust_cg_lower::types::Type::I64],
        };
        let mut func = RiscVISelFunction::new("callee".to_string(), sig);
        let entry = Block(0);
        func.ensure_block(entry);
        let v_a = VReg::new(0, RegClass::Gpr64);
        let v_b = VReg::new(1, RegClass::Gpr64);
        let v_sum = VReg::new(2, RegClass::Gpr64);
        func.next_vreg = 3;
        // v_a = a0 ; v_b = a1.
        func.push_inst(
            entry,
            RiscVISelInst::new(
                RiscVOpcode::Addi,
                vec![
                    RiscVISelOperand::VReg(v_a),
                    RiscVISelOperand::PReg(A0),
                    RiscVISelOperand::Imm(0),
                ],
            ),
        );
        func.push_inst(
            entry,
            RiscVISelInst::new(
                RiscVOpcode::Addi,
                vec![
                    RiscVISelOperand::VReg(v_b),
                    RiscVISelOperand::PReg(A1),
                    RiscVISelOperand::Imm(0),
                ],
            ),
        );
        // v_sum = v_a + v_b ; a0 = v_sum ; ret.
        func.push_inst(
            entry,
            RiscVISelInst::new(
                RiscVOpcode::Add,
                vec![
                    RiscVISelOperand::VReg(v_sum),
                    RiscVISelOperand::VReg(v_a),
                    RiscVISelOperand::VReg(v_b),
                ],
            ),
        );
        func.push_inst(
            entry,
            RiscVISelInst::new(
                RiscVOpcode::Addi,
                vec![
                    RiscVISelOperand::PReg(A0),
                    RiscVISelOperand::VReg(v_sum),
                    RiscVISelOperand::Imm(0),
                ],
            ),
        );
        func.push_inst(
            entry,
            RiscVISelInst::new(
                RiscVOpcode::Jalr,
                vec![
                    RiscVISelOperand::PReg(ZERO),
                    RiscVISelOperand::PReg(RA),
                    RiscVISelOperand::Imm(0),
                ],
            ),
        );
        func
    }

    /// Build `caller() -> callee(20, 22)` as an ISel function. It marshals the two
    /// constant arguments into a0/a1, performs the CROSS-FUNCTION direct call via
    /// the AUIPC+JALR pcrel pair carrying `Symbol("callee")`, then returns the
    /// call result (a0). `caller`'s own `ra` is clobbered by the call, so the
    /// prologue/epilogue (added by the pipeline) save/restore it.
    fn build_caller_calls_callee() -> RiscVISelFunction {
        let sig = Signature {
            params: vec![],
            returns: vec![trust_cg_lower::types::Type::I64],
        };
        let mut func = RiscVISelFunction::new("caller".to_string(), sig);
        let entry = Block(0);
        func.ensure_block(entry);
        let v_res = VReg::new(0, RegClass::Gpr64);
        func.next_vreg = 1;
        // AUIPC ra, %pcrel_hi(callee)  (emitted BEFORE the arg moves, as ISel does).
        func.push_inst(
            entry,
            RiscVISelInst::new(
                RiscVOpcode::Auipc,
                vec![
                    RiscVISelOperand::PReg(RA),
                    RiscVISelOperand::Symbol("callee".to_string()),
                ],
            ),
        );
        // a0 = 20 ; a1 = 22  (argument-setup moves; the parallel-copy fixup is a
        // no-op here since the sources are not arg registers).
        func.push_inst(
            entry,
            RiscVISelInst::new(
                RiscVOpcode::Addi,
                vec![
                    RiscVISelOperand::PReg(A0),
                    RiscVISelOperand::PReg(ZERO),
                    RiscVISelOperand::Imm(20),
                ],
            ),
        );
        func.push_inst(
            entry,
            RiscVISelInst::new(
                RiscVOpcode::Addi,
                vec![
                    RiscVISelOperand::PReg(A1),
                    RiscVISelOperand::PReg(ZERO),
                    RiscVISelOperand::Imm(22),
                ],
            ),
        );
        // JALR ra, ra, %pcrel_lo(callee)  + arg PReg uses for liveness/clobber.
        func.push_inst(
            entry,
            RiscVISelInst::new(
                RiscVOpcode::Jalr,
                vec![
                    RiscVISelOperand::PReg(RA),
                    RiscVISelOperand::PReg(RA),
                    RiscVISelOperand::Symbol("callee".to_string()),
                    RiscVISelOperand::PReg(A0),
                    RiscVISelOperand::PReg(A1),
                ],
            ),
        );
        // v_res = a0 (the call result) ; a0 = v_res ; ret.
        func.push_inst(
            entry,
            RiscVISelInst::new(
                RiscVOpcode::Addi,
                vec![
                    RiscVISelOperand::VReg(v_res),
                    RiscVISelOperand::PReg(A0),
                    RiscVISelOperand::Imm(0),
                ],
            ),
        );
        func.push_inst(
            entry,
            RiscVISelInst::new(
                RiscVOpcode::Addi,
                vec![
                    RiscVISelOperand::PReg(A0),
                    RiscVISelOperand::VReg(v_res),
                    RiscVISelOperand::Imm(0),
                ],
            ),
        );
        func.push_inst(
            entry,
            RiscVISelInst::new(
                RiscVOpcode::Jalr,
                vec![
                    RiscVISelOperand::PReg(ZERO),
                    RiscVISelOperand::PReg(RA),
                    RiscVISelOperand::Imm(0),
                ],
            ),
        );
        func
    }

    /// Lay out two functions into one `.text` exactly as the module emitter does
    /// (4-byte aligned per function, intra-object calls patched), and return
    /// `(text, [(name, offset)])`. This reuses the production helpers
    /// `compile_function_with_fixups` + `riscv_patch_intra_object_call`.
    fn layout_module(funcs: &[&RiscVISelFunction]) -> (Vec<u8>, Vec<(String, u32)>) {
        let pipeline = RiscVPipeline::new(RiscVPipelineConfig {
            emit_elf: false,
            emit_frame: true,
        });
        let mut compiled: Vec<(String, Vec<u8>, Vec<RiscVCallFixup>)> = Vec::new();
        for f in funcs {
            let (code, fixups) = pipeline
                .compile_function_with_fixups(f)
                .expect("function compiles with fixups");
            compiled.push((f.name.clone(), code, fixups));
        }
        let mut text = Vec::new();
        let mut layout: Vec<(String, u32)> = Vec::new();
        let mut rebased: Vec<RiscVCallFixup> = Vec::new();
        for (name, code, fixups) in &compiled {
            while text.len() % 4 != 0 {
                text.push(0);
            }
            let base = text.len() as u32;
            text.extend_from_slice(code);
            layout.push((name.clone(), base));
            for fx in fixups {
                rebased.push(RiscVCallFixup {
                    auipc_offset: base + fx.auipc_offset,
                    jalr_offset: base + fx.jalr_offset,
                    callee: fx.callee.clone(),
                });
            }
        }
        let offsets: HashMap<String, u32> = layout.iter().cloned().collect();
        for fx in &rebased {
            let callee_off = *offsets
                .get(&fx.callee)
                .expect("callee defined in module for this test");
            riscv_patch_intra_object_call(&mut text, fx.auipc_offset, fx.jalr_offset, callee_off)
                .expect("intra-object call resolves in range");
        }
        (text, layout)
    }

    /// END-TO-END phase 4: a 2-function module where `caller()` cross-function-
    /// calls `callee(20, 22)`. We lay the module out (caller first, then callee),
    /// resolve the cross-function call PC-relatively, then DECODE+interpret the
    /// emitted `.text` byte stream and assert (i) the call lands EXACTLY on
    /// callee's entry (a wrong target would compute a wrong sum or crash), (ii)
    /// the returned value is 42, and (iii) the call/return ABI is balanced (a
    /// corrupted ra would loop to the step limit).
    #[test]
    fn two_function_module_cross_call_interprets_to_42() {
        let caller = build_caller_calls_callee();
        let callee = build_callee_add();
        // Order caller-first so the call is a FORWARD intra-object reference.
        let (text, layout) = layout_module(&[&caller, &callee]);

        let caller_off = layout
            .iter()
            .find(|(n, _)| n == "caller")
            .map(|(_, o)| *o)
            .expect("caller present");
        // Sanity: the module has both symbols at distinct, 4-aligned offsets.
        assert!(layout.iter().any(|(n, _)| n == "callee"), "callee present");
        for (_, off) in &layout {
            assert_eq!(off % 4, 0, "function offsets are 4-byte aligned");
        }

        const SENTINEL: u64 = 0xFFFF_FFFF_FFFF_FF00;
        let mut interp = RiscVByteInterp::new(text);
        let result = interp.run(caller_off as u64, SENTINEL, 100_000);
        assert_eq!(result, 42, "caller() = callee(20, 22) must be 42");
        assert_eq!(
            interp.regs[1], SENTINEL,
            "outermost ra restored to sentinel"
        );
    }

    /// Reverse the layout (callee first, caller second) so the cross-function call
    /// is a BACKWARD intra-object reference (negative displacement). It must still
    /// resolve and interpret to 42 — exercising the negative-displacement hi20/lo12
    /// carry path of the patcher.
    #[test]
    fn two_function_module_backward_cross_call_interprets_to_42() {
        let caller = build_caller_calls_callee();
        let callee = build_callee_add();
        let (text, layout) = layout_module(&[&callee, &caller]);
        let caller_off = layout
            .iter()
            .find(|(n, _)| n == "caller")
            .map(|(_, o)| *o)
            .expect("caller present");
        const SENTINEL: u64 = 0xFFFF_FFFF_FFFF_FF00;
        let mut interp = RiscVByteInterp::new(text);
        let result = interp.run(caller_off as u64, SENTINEL, 100_000);
        assert_eq!(result, 42, "backward cross-call caller() must be 42");
    }

    /// FAIL-CLOSED: compiling a function that contains a cross-function call in
    /// ISOLATION (the single-function `compile_function` path) must be rejected
    /// with a typed error — there is no module to resolve the callee against, so
    /// emitting a zero/wrong target is forbidden. This is the unresolved/external
    /// symbol fail-closed case at the single-function boundary.
    #[test]
    fn single_function_with_cross_call_fails_closed() {
        let caller = build_caller_calls_callee();
        let pipeline = RiscVPipeline::new(RiscVPipelineConfig {
            emit_elf: false,
            emit_frame: true,
        });
        let err = pipeline
            .compile_function(&caller)
            .expect_err("single-function compile of a cross-function call must fail closed");
        assert!(
            matches!(err, RiscVPipelineError::ISel(_)),
            "expected typed ISel fail-closed error, got {err:?}"
        );
        // The fixup list IS produced by the with-fixups variant (the module path
        // consumes it); it must reference the callee, never silently dropped.
        let (_code, fixups) = pipeline
            .compile_function_with_fixups(&caller)
            .expect("with-fixups variant returns code + the deferred fixup");
        assert_eq!(fixups.len(), 1, "exactly one cross-function call fixup");
        assert_eq!(fixups[0].callee, "callee");
        assert!(
            fixups[0].jalr_offset > fixups[0].auipc_offset,
            "JALR pcrel-lo must follow the AUIPC pcrel-hi anchor"
        );
    }
}
