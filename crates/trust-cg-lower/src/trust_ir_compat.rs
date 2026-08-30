// trust-cg-lower/trust_ir_compat.rs - Compatibility layer for trust_ir API
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// This module provides re-exports and compatibility types that bridge the
// unified trust_ir crate API with Trust Codegen-internal types. The old 4-crate trust_ir
// stubs (trust_ir-types, trust_ir-instrs, trust_ir-func, trust_ir-semantics) have been
// replaced by the real trust_ir crate. This module preserves backward-compatible
// types (CmpOp, Operand, CallingConv, etc.) that are Trust Codegen-internal and
// don't exist in the real trust_ir crate.

#![allow(dead_code)]

// ---------------------------------------------------------------------------
// Direct re-exports from trust_ir (types that are identical or very similar)
// ---------------------------------------------------------------------------

// Core ID types (same API: .new(u32), .index(), .0 field)
pub use trust_ir::FuncTyId;
pub use trust_ir::TyId;
pub use trust_ir::{BlockId, FuncId, StructId, ValueId};

// Type system
pub use trust_ir::{FieldDef, FuncTy, StructDef, Ty};

// Instructions
pub use trust_ir::FCmpOp;
pub use trust_ir::ICmpOp;
pub use trust_ir::OverflowOp;
pub use trust_ir::SwitchCase;
pub use trust_ir::{BinOp, CastOp, Constant, Inst, InstrNode, UnOp};

// Atomics (renamed for compat)
pub use trust_ir::AtomicRMWOp as AtomicRmwOp;
pub use trust_ir::Ordering as MemoryOrdering;

// Proof system (renamed for compat with old TrustIrProof name)
pub use trust_ir::ProofAnnotation;
pub use trust_ir::{ObligationKind, ProofObligation, ProofStatus, ProofSummary};
pub use trust_ir::{ProofCertificate, ProofEvidence};
pub use trust_ir::{ProofId, ProofTag};

// Module/Function/Block structures
pub use trust_ir::{Block, Function, Global, Module};

// ---------------------------------------------------------------------------
// CmpOp compatibility enum
// ---------------------------------------------------------------------------

/// Unified comparison operation (Trust Codegen extension).
///
/// The real trust_ir crate splits comparisons into `ICmpOp` (integer) and `FCmpOp`
/// (float). This unified enum is used by the Trust Codegen ISel and adapter layers
/// where a single comparison type is more convenient.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CmpOp {
    // Integer comparisons
    Eq,
    Ne,
    Slt,
    Sle,
    Sgt,
    Sge,
    Ult,
    Ule,
    Ugt,
    Uge,
    // Float comparisons (ordered)
    FOeq,
    FOne,
    FOlt,
    FOle,
    FOgt,
    FOge,
    // Float comparisons (unordered)
    FUeq,
    FUne,
    FUlt,
    FUle,
    FUgt,
    FUge,
}

impl CmpOp {
    /// Returns true if this is a float comparison.
    pub fn is_float(&self) -> bool {
        matches!(
            self,
            CmpOp::FOeq
                | CmpOp::FOne
                | CmpOp::FOlt
                | CmpOp::FOle
                | CmpOp::FOgt
                | CmpOp::FOge
                | CmpOp::FUeq
                | CmpOp::FUne
                | CmpOp::FUlt
                | CmpOp::FUle
                | CmpOp::FUgt
                | CmpOp::FUge
        )
    }
}

// ---------------------------------------------------------------------------
// Operand compatibility type
// ---------------------------------------------------------------------------

/// Trust Codegen-internal operand type.
///
/// The real trust_ir crate uses bare `ValueId` for instruction operands.
/// This `Operand` type (Value | Constant) is an Trust Codegen extension used
/// by the adapter layer and test code.
#[derive(Debug, Clone, PartialEq)]
pub enum Operand {
    /// Reference to an SSA value.
    Value(ValueId),
    /// Inline constant value.
    Constant(OperandConstant),
}

/// Constant value carried in an Operand (backward compat).
#[derive(Debug, Clone, PartialEq)]
pub enum OperandConstant {
    Int { value: i128, ty: Ty },
    Float { value: f64, ty: Ty },
    Bool(bool),
    Unit,
}

impl Operand {
    pub fn value(vid: ValueId) -> Self {
        Operand::Value(vid)
    }

    pub fn int(value: i128, ty: Ty) -> Self {
        Operand::Constant(OperandConstant::Int { value, ty })
    }

    pub fn float(value: f64, ty: Ty) -> Self {
        Operand::Constant(OperandConstant::Float { value, ty })
    }

    pub fn bool_const(value: bool) -> Self {
        Operand::Constant(OperandConstant::Bool(value))
    }
}

impl From<ValueId> for Operand {
    fn from(vid: ValueId) -> Self {
        Operand::Value(vid)
    }
}

// ---------------------------------------------------------------------------
// Trust Codegen-internal types not present in the trust_ir crate
// ---------------------------------------------------------------------------

/// Calling convention (Trust Codegen extension, not in real trust_ir).
///
/// The real trust_ir crate does not include calling conventions. This is kept
/// as an Trust Codegen-internal type for the adapter/ABI layer.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub enum CallingConv {
    #[default]
    C,
    Fast,
    Swift,
    Cold,
    PreserveMost,
}

/// Symbol visibility (Trust Codegen extension, not in real trust_ir).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub enum Visibility {
    #[default]
    Default,
    Hidden,
    Protected,
}

impl Visibility {
    pub fn macho_flags(&self) -> u8 {
        match self {
            Visibility::Default | Visibility::Protected => 0x01,
            Visibility::Hidden => 0x01 | 0x10,
        }
    }
}

/// Data layout (Trust Codegen extension, not in real trust_ir).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DataLayout {
    pub pointer_size: u32,
    pub pointer_align: u32,
    pub stack_align: u32,
    pub big_endian: bool,
    pub int_align: Vec<(u16, u32)>,
}

impl DataLayout {
    pub fn aarch64() -> Self {
        Self {
            pointer_size: 8,
            pointer_align: 8,
            stack_align: 16,
            big_endian: false,
            int_align: vec![(8, 1), (16, 2), (32, 4), (64, 8), (128, 16)],
        }
    }

    pub fn x86_64() -> Self {
        Self {
            pointer_size: 8,
            pointer_align: 8,
            stack_align: 16,
            big_endian: false,
            int_align: vec![(8, 1), (16, 2), (32, 4), (64, 8), (128, 16)],
        }
    }
}

/// Linkage type (Trust Codegen extension, not in real trust_ir).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub enum Linkage {
    #[default]
    External,
    Internal,
    Weak,
    AvailableExternally,
}

/// Global variable definition (Trust Codegen extension wrapping trust_ir::Global).
///
/// The real trust_ir crate has a simpler `Global` struct. This extends it
/// with Trust Codegen-specific fields like linkage and visibility.
#[derive(Debug, Clone, PartialEq)]
pub struct GlobalDef {
    pub name: String,
    pub ty: Ty,
    pub is_const: bool,
    pub linkage: Linkage,
    pub visibility: Visibility,
    pub initializer: Option<Vec<u8>>,
    pub align: Option<u32>,
}
