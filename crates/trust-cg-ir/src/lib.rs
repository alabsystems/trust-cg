// trust-cg-ir - Shared machine IR model
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! trust-cg (Code Generation) — Shared machine IR model
//!
//! trust-cg is a proof-oriented compiler backend for the Trust stack. The **cg**
//! suffix stands for **Code Generation**, the process of translating
//! intermediate representation into executable machine code.
//!
//! Shared machine IR types for trust-cg.
//!
//! Trust Codegen consumes trust_ir (the upstream IR) via the `trust-cg-lower` adapter; see
//! the *trust_ir GEP stride contract* section below for the ABI-critical pointer
//! arithmetic convention shared with external consumers (ay, ty).
//!
//! # Architecture
//!
//! ```text
//! trust-cg-lower ──┐
//!               v
//!           trust-cg-ir (this crate)
//!               │
//!       ┌───────┼───────┬─────────────┐
//!       v       v       v             v
//!  trust-cg-opt  regalloc  trust-cg-codegen  trust-cg-verify
//! ```
//!
//! # Type Authority
//!
//! This crate is the SINGLE SOURCE OF TRUTH for all machine IR types.
//! Other crates (trust-cg-lower, trust-cg-regalloc, trust-cg-opt, trust-cg-codegen)
//! must import types from here rather than defining their own.
//!
//! | Type | Module |
//! |------|--------|
//! | PReg, RegClass, VReg | `regs` (delegates to `aarch64_regs`) |
//! | CondCode, ShiftType, ExtendType | `regs` (delegates to `aarch64_regs`) |
//! | MachInst, AArch64Opcode, InstFlags | `inst` |
//! | MachOperand | `operand` |
//! | MachBlock, MachFunction, Signature, StackSlot, Type | `function` |
//! | BlockId, InstId, VRegId, StackSlotId, FrameIdx | `types` |
//! | AArch64CC, OperandSize, FloatSize | `cc` |
//!
//! # trust_ir GEP stride contract
//!
//! `trust_ir::Inst::GEP { pointee_ty, base, indices }` computes
//! `base + sum_i (indices[i] * stride_i)` where the stride for the leading
//! index is `sizeof(pointee_ty)` and strides for trailing indices follow the
//! pointee type's layout. Indices are signed `I64`; negative indices are
//! well-defined and produce pointer arithmetic wrap-around following C's
//! `intptr_t` semantics. A zero-length `indices` list is the identity
//! operation.
//!
//! This contract is load-bearing for external consumers (`ay`, `ty`) that
//! emit trust_ir and consume symbol pointers via `mem::transmute`. Changing the
//! stride convention is a **P0 ABI break**.
//!
//! The Trust Codegen consumer of this contract is
//! `crates/trust-cg-lower/src/adapter.rs` (the `Inst::GEP` match arm), which
//! computes `elem_size = Type::bytes(translate_ty(pointee_ty))` and emits
//! `dst = base + index * elem_size` (skipping the multiply when
//! `elem_size == 1`). Multi-index GEP is currently unsupported and returns
//! `AdapterError::UnsupportedInstruction`.
//!
//! Unit test: `test_gep_stride_contract_i64` in
//! `crates/trust-cg-lower/tests/trust_ir_integration.rs` pins `GEP { pointee_ty:
//! I64, base, indices: [idx] }` to `base + idx * 8`.
//!
//! Cross-references: issue #475 (this contract), issue #431 (sibling
//! calling-convention ABI doc).

pub mod aarch64_regs;
pub mod cc;
pub mod cost_model;
pub mod function;
pub mod guard;
pub mod guard_target;
pub mod inst;
pub mod operand;
pub mod overflow_tag;
pub mod provenance;
pub mod regs;
pub mod riscv_ops;
pub mod riscv_regs;
pub mod target_info;
pub mod tls;
pub mod trace;
pub mod type_hierarchy;
pub mod types;
pub mod wasm_ops;
pub mod x86_64_ops;
pub mod x86_64_regs;

// Re-export the most commonly used types at crate root.
pub use cc::{AArch64CC, FloatSize, OperandSize};
pub use function::{
    EhCallSiteEntry, EnumTagWidth, ExceptionHandlingMetadata, FunctionDebugMeta, LandingPadEntry,
    MachBlock, MachFunction, Signature, StackProtectorMode, StackSlot, Type,
};
pub use guard::{
    ConservationReport, ConservationViolation, DischargeStatus, DischargedEvidenceTable,
    EliminationCertificate, EliminationVerdict, GuardKind, GuardObligationReceipt,
    GuardOperandIdentity, GuardOperandRef, GuardSite, GuardSiteLedger, GuardState, RecheckOutcome,
    decide, fingerprint_for_kind, fingerprint_operands, recheck_elimination,
};
pub use guard_target::{
    AArch64GuardTarget, GuardTarget, RiscvGuardTarget, X86GuardTarget, aarch64_guard_operands,
    classify_riscv_carrier, classify_x86_carrier, riscv_guard_operands, x86_guard_operands,
};
pub use inst::{
    AArch64Opcode, InstFlags, MachInst, ProofAnnotation, ProofDivergence, ProofFact, SourceLoc,
};
pub use operand::MachOperand;
pub use overflow_tag::{OverflowOp, pack_overflow_tag, unpack_overflow_tag};
pub use provenance::{
    LoweringProvenance, LoweringProvenanceCoverage, OpcodeProvenanceCount, PassId, ProvenanceEntry,
    ProvenanceMap, ProvenanceStats, ProvenanceStatus, SourceInstDigest, SourceInstId,
    SyntheticReason, TransformKind, TransformRecord, TrustIrInstId,
};
pub use regs::{CondCode, PReg, RegClass, SpecialReg, VReg};
pub use riscv_ops::RiscVOpcode;
pub use riscv_regs::{RiscVPReg, RiscVRegClass};
pub use target_info::{AArch64Target, OpcodeCategory, TargetInfo, X86_64Target};
pub use tls::TlsModel;
pub use trace::{CompilationEvent, CompilationTrace, EventKind, Justification, RuleId, TraceLevel};
pub use types::{BlockId, FrameIdx, InstId, StackSlotId, VRegId};
pub use wasm_ops::WasmOpcode;
pub use x86_64_ops::{X86CondCode, X86Opcode};
pub use x86_64_regs::{X86PReg, X86RegClass};
