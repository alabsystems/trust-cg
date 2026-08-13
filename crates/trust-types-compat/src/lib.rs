// trust-types-compat - minimal trust_types API surface used by Trust Codegen
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Minimal `trust_types` compatibility types consumed by Trust Codegen's optional
//! translation-validation bridge.
//!
//! The full tRust compiler workspace is too large and workspace-coupled to be
//! resolved by every Trust Codegen build. Trust Codegen only needs this scalar formula and
//! refinement-VC surface for bridge conversion tests.

/// Formula sort vocabulary used by the trust/Trust Codegen SMT bridge.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Sort {
    Bool,
    Int,
    BitVec(u32),
    Array(Box<Sort>, Box<Sort>),
    Opaque,
}

/// Trust-style verification formula.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Formula {
    Bool(bool),
    Int(i128),
    UInt(u128),
    BitVec {
        value: i128,
        width: u32,
    },
    Var(String, Sort),
    SymVar(String, Sort),
    Not(Box<Formula>),
    And(Vec<Formula>),
    Or(Vec<Formula>),
    Implies(Box<Formula>, Box<Formula>),
    Eq(Box<Formula>, Box<Formula>),
    Lt(Box<Formula>, Box<Formula>),
    Le(Box<Formula>, Box<Formula>),
    Gt(Box<Formula>, Box<Formula>),
    Ge(Box<Formula>, Box<Formula>),
    Add(Box<Formula>, Box<Formula>),
    Sub(Box<Formula>, Box<Formula>),
    Mul(Box<Formula>, Box<Formula>),
    Div(Box<Formula>, Box<Formula>),
    Rem(Box<Formula>, Box<Formula>),
    Neg(Box<Formula>),
    BvAdd(Box<Formula>, Box<Formula>, u32),
    BvSub(Box<Formula>, Box<Formula>, u32),
    BvMul(Box<Formula>, Box<Formula>, u32),
    BvUDiv(Box<Formula>, Box<Formula>, u32),
    BvSDiv(Box<Formula>, Box<Formula>, u32),
    BvURem(Box<Formula>, Box<Formula>, u32),
    BvSRem(Box<Formula>, Box<Formula>, u32),
    BvAnd(Box<Formula>, Box<Formula>, u32),
    BvOr(Box<Formula>, Box<Formula>, u32),
    BvXor(Box<Formula>, Box<Formula>, u32),
    BvNot(Box<Formula>, u32),
    BvShl(Box<Formula>, Box<Formula>, u32),
    BvLShr(Box<Formula>, Box<Formula>, u32),
    BvAShr(Box<Formula>, Box<Formula>, u32),
    BvULt(Box<Formula>, Box<Formula>, u32),
    BvULe(Box<Formula>, Box<Formula>, u32),
    BvSLt(Box<Formula>, Box<Formula>, u32),
    BvSLe(Box<Formula>, Box<Formula>, u32),
    BvExtract {
        inner: Box<Formula>,
        high: u32,
        low: u32,
    },
    BvConcat(Box<Formula>, Box<Formula>),
    BvZeroExt(Box<Formula>, u32),
    BvSignExt(Box<Formula>, u32),
    Ite(Box<Formula>, Box<Formula>, Box<Formula>),
    BvToInt(Box<Formula>),
    IntToBv(Box<Formula>, u32),
    Select(Box<Formula>, Box<Formula>),
    Store(Box<Formula>, Box<Formula>, Box<Formula>),
    Forall(Vec<(String, Sort)>, Box<Formula>),
    Exists(Vec<(String, Sort)>, Box<Formula>),
    Opaque,
}

/// Basic block point in a source or target translation-validation graph.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BlockId(pub u32);

/// Trust translation-validation check taxonomy.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CheckKind {
    DataFlow,
    ControlFlow,
    ReturnValue,
    Termination,
}

/// One trust translation-validation check.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TranslationCheck {
    pub source_point: BlockId,
    pub target_point: BlockId,
    pub kind: CheckKind,
    pub formula: Formula,
    pub description: String,
}

/// Refinement VC pairing a translation check with source/target function IDs.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RefinementVc {
    pub check: TranslationCheck,
    pub source_function: String,
    pub target_function: String,
}
