// trust-cg-verify/smt/trust_formula_adapter.rs - tRust Formula compatibility
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Fallible adapter between tRust `trust_types::Formula` and Trust Codegen [`super::SmtExpr`].
//!
//! This is the scalar bridge called out by #260 and
//! `designs/2026-04-16-transval-alignment.md`: tRust trust-transval VCs use
//! `Formula`, while Trust Codegen lowering proofs use `SmtExpr`. The adapter requires
//! an explicit [`FormulaAdapterContext`] for every variable, including the
//! fixed bit width used when a tRust `Sort::Int` is interpreted as machine
//! arithmetic. Unsupported or ambiguous constructs return an error.
//!
//! Supported Formula subset:
//! - bool, integer, unsigned integer, and bitvector literals;
//! - declared bool, integer, and bitvector variables;
//! - `not`, `and`, `or`, `=>`;
//! - equality and integer comparisons with signedness from the context;
//! - `Add`, `Sub`, `Mul`, `Div`, `Neg` over context-width integers;
//! - core bitvector arithmetic, bitwise ops, shifts, signed/unsigned compares,
//!   extract, concat, zero-extend, sign-extend, and bitvector ITE.
//!
//! Arrays, quantifiers, floating-point expressions, uninterpreted functions,
//! and integer/bitvector conversions that cannot be represented by `SmtExpr`
//! are rejected.

use super::{SmtExpr, mask};
use std::collections::HashMap;
use thiserror::Error;
use trust_ir::{Module as TrustIrModule, Ty as TrustIrTy, TypedValueMetadata, ValueId};
use trust_types::{Formula, Sort};

/// Variable sort supplied by the compatibility layer.
///
/// tRust `Sort::Int` is mathematical and carries no width or signedness. Trust Codegen
/// lowering proofs are fixed-width bitvector proofs, so integer variables must
/// be declared with the machine width and comparison/division signedness here.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FormulaAdapterVarSort {
    Bool,
    BitVec(u32),
    SignedInt { width: u32 },
    UnsignedInt { width: u32 },
}

impl FormulaAdapterVarSort {
    pub fn width(self) -> Option<u32> {
        match self {
            FormulaAdapterVarSort::Bool => None,
            FormulaAdapterVarSort::BitVec(width)
            | FormulaAdapterVarSort::SignedInt { width }
            | FormulaAdapterVarSort::UnsignedInt { width } => Some(width),
        }
    }

    fn value_sort(self) -> Result<ValueSort, FormulaAdapterError> {
        match self {
            FormulaAdapterVarSort::Bool => Ok(ValueSort::Bool),
            FormulaAdapterVarSort::BitVec(width) => ValueSort::bitvec(width),
            FormulaAdapterVarSort::SignedInt { width } => ValueSort::int(width, Signedness::Signed),
            FormulaAdapterVarSort::UnsignedInt { width } => {
                ValueSort::int(width, Signedness::Unsigned)
            }
        }
    }

    fn trust_sort(self) -> Sort {
        match self {
            FormulaAdapterVarSort::Bool => Sort::Bool,
            FormulaAdapterVarSort::BitVec(width) => Sort::BitVec(width),
            FormulaAdapterVarSort::SignedInt { .. } | FormulaAdapterVarSort::UnsignedInt { .. } => {
                Sort::Int
            }
        }
    }
}

/// Explicit variable context for Formula/SmtExpr conversion.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct FormulaAdapterContext {
    variables: HashMap<String, FormulaAdapterVarSort>,
}

impl FormulaAdapterContext {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn with_bool_var(mut self, name: impl Into<String>) -> Self {
        self.declare_var(name, FormulaAdapterVarSort::Bool);
        self
    }

    pub fn with_bv_var(mut self, name: impl Into<String>, width: u32) -> Self {
        self.declare_var(name, FormulaAdapterVarSort::BitVec(width));
        self
    }

    pub fn with_signed_int_var(mut self, name: impl Into<String>, width: u32) -> Self {
        self.declare_var(name, FormulaAdapterVarSort::SignedInt { width });
        self
    }

    pub fn with_unsigned_int_var(mut self, name: impl Into<String>, width: u32) -> Self {
        self.declare_var(name, FormulaAdapterVarSort::UnsignedInt { width });
        self
    }

    pub fn declare_var(&mut self, name: impl Into<String>, sort: FormulaAdapterVarSort) {
        self.variables.insert(name.into(), sort);
    }

    pub fn var_sort(&self, name: &str) -> Result<FormulaAdapterVarSort, FormulaAdapterError> {
        self.variables
            .get(name)
            .copied()
            .ok_or_else(|| FormulaAdapterError::UndeclaredVariable(name.to_string()))
    }

    fn bool_var_name(&self, expr: &SmtExpr) -> Option<String> {
        let SmtExpr::Eq { lhs, rhs } = expr else {
            return None;
        };

        let name = match (&**lhs, &**rhs) {
            (SmtExpr::Var { name, width: 1 }, SmtExpr::BvConst { value: 1, width: 1 })
            | (SmtExpr::BvConst { value: 1, width: 1 }, SmtExpr::Var { name, width: 1 }) => name,
            _ => return None,
        };

        matches!(
            self.variables.get(name.as_str()),
            Some(FormulaAdapterVarSort::Bool)
        )
        .then(|| name.clone())
    }
}

/// Errors are intentionally precise so callers can keep the bridge fail-closed.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum FormulaAdapterError {
    #[error("unsupported Formula construct: {0}")]
    UnsupportedFormula(&'static str),

    #[error("unsupported SmtExpr construct: {0}")]
    UnsupportedSmtExpr(&'static str),

    #[error("unsupported Formula sort: {0}")]
    UnsupportedSort(String),

    #[error("undeclared variable '{0}'")]
    UndeclaredVariable(String),

    #[error("sort mismatch in {context}: expected {expected}, got {actual}")]
    SortMismatch {
        context: &'static str,
        expected: String,
        actual: String,
    },

    #[error("width mismatch in {context}: expected {expected}, got {actual}")]
    WidthMismatch {
        context: &'static str,
        expected: u32,
        actual: u32,
    },

    #[error("invalid bitvector width {0}")]
    InvalidWidth(u32),

    #[error("ambiguous literal requires an expected bitvector/integer width: {0}")]
    AmbiguousLiteral(&'static str),

    #[error("literal {value} is out of range for {width}-bit encoding")]
    LiteralOutOfRange { value: String, width: u32 },

    #[error("ambiguous integer semantics for {0}; declare an Int variable with signedness")]
    AmbiguousIntegerSemantics(&'static str),

    #[error("missing trust_ir function {0}")]
    MissingTrustIrFunction(u32),
}

/// Convert a tRust formula into an Trust Codegen SMT expression.
pub fn formula_to_smt(
    formula: &Formula,
    ctx: &FormulaAdapterContext,
) -> Result<SmtExpr, FormulaAdapterError> {
    Ok(formula_to_typed_smt(formula, ctx, None)?.expr)
}

/// Convert an Trust Codegen SMT expression into a tRust formula.
pub fn smt_to_formula(
    expr: &SmtExpr,
    ctx: &FormulaAdapterContext,
) -> Result<Formula, FormulaAdapterError> {
    Ok(smt_to_typed_formula(expr, ctx, None)?.formula)
}

/// Stable variable name Trust Codegen uses for a trust_ir SSA value in trust formulas.
pub fn trust_ir_value_var_name(value: ValueId) -> String {
    format!("v{}", value.index())
}

/// Build a formula adapter context from trust_ir typed SSA metadata.
///
/// This is the verifier-facing bridge for tRust/trust_ir consumers that already
/// have a canonical in-memory `trust_ir::Module`: typed SSA facts flow directly
/// into the fixed-width formula adapter instead of being reconstructed from
/// text or from Trust Codegen lowering side tables.
pub fn formula_context_from_trust_ir_function(
    module: &TrustIrModule,
    function: trust_ir::FuncId,
) -> Result<FormulaAdapterContext, FormulaAdapterError> {
    let metadata = module
        .typed_values_for_function(function)
        .ok_or_else(|| FormulaAdapterError::MissingTrustIrFunction(function.index()))?;
    let pointer_width = trust_ir_module_pointer_width(module)?;
    formula_context_from_trust_ir_values(&metadata, pointer_width)
}

/// Build a formula adapter context from a precomputed trust_ir metadata slice.
pub fn formula_context_from_trust_ir_values(
    values: &[TypedValueMetadata],
    pointer_width: u32,
) -> Result<FormulaAdapterContext, FormulaAdapterError> {
    let mut ctx = FormulaAdapterContext::new();
    for value in values {
        ctx.declare_var(
            trust_ir_value_var_name(value.value),
            trust_ir_ty_to_formula_var_sort(&value.ty, pointer_width)?,
        );
    }
    Ok(ctx)
}

/// Map a trust_ir type into the scalar sorts understood by the trust formula bridge.
pub fn trust_ir_ty_to_formula_var_sort(
    ty: &TrustIrTy,
    pointer_width: u32,
) -> Result<FormulaAdapterVarSort, FormulaAdapterError> {
    match ty {
        TrustIrTy::Bool => Ok(FormulaAdapterVarSort::Bool),
        TrustIrTy::I8 => Ok(FormulaAdapterVarSort::SignedInt { width: 8 }),
        TrustIrTy::I16 => Ok(FormulaAdapterVarSort::SignedInt { width: 16 }),
        TrustIrTy::I32 => Ok(FormulaAdapterVarSort::SignedInt { width: 32 }),
        TrustIrTy::I64 => Ok(FormulaAdapterVarSort::SignedInt { width: 64 }),
        TrustIrTy::I128 => Ok(FormulaAdapterVarSort::SignedInt { width: 128 }),
        TrustIrTy::U8 => Ok(FormulaAdapterVarSort::UnsignedInt { width: 8 }),
        TrustIrTy::U16 => Ok(FormulaAdapterVarSort::UnsignedInt { width: 16 }),
        TrustIrTy::U32 => Ok(FormulaAdapterVarSort::UnsignedInt { width: 32 }),
        TrustIrTy::U64 => Ok(FormulaAdapterVarSort::UnsignedInt { width: 64 }),
        TrustIrTy::U128 => Ok(FormulaAdapterVarSort::UnsignedInt { width: 128 }),
        TrustIrTy::Ptr
        | TrustIrTy::Ref(_)
        | TrustIrTy::RefMut(_)
        | TrustIrTy::PtrConst(_)
        | TrustIrTy::PtrMut(_)
        | TrustIrTy::Rc(_) => {
            validate_width(pointer_width)?;
            Ok(FormulaAdapterVarSort::BitVec(pointer_width))
        }
        unsupported => Err(FormulaAdapterError::UnsupportedSort(format!(
            "trust_ir type {unsupported}"
        ))),
    }
}

fn trust_ir_module_pointer_width(module: &TrustIrModule) -> Result<u32, FormulaAdapterError> {
    match &module.target_info {
        Some(target) => {
            let width = target
                .pointer_size
                .checked_mul(8)
                .ok_or(FormulaAdapterError::InvalidWidth(u32::MAX))?;
            validate_width(width)?;
            Ok(width)
        }
        None => Ok(64),
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Signedness {
    Signed,
    Unsigned,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum NumericKind {
    BitVec,
    Int(Signedness),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ValueSort {
    Bool,
    BitVec { width: u32, kind: NumericKind },
}

impl ValueSort {
    fn bitvec(width: u32) -> Result<Self, FormulaAdapterError> {
        validate_width(width)?;
        Ok(ValueSort::BitVec {
            width,
            kind: NumericKind::BitVec,
        })
    }

    fn int(width: u32, signedness: Signedness) -> Result<Self, FormulaAdapterError> {
        validate_width(width)?;
        Ok(ValueSort::BitVec {
            width,
            kind: NumericKind::Int(signedness),
        })
    }

    fn width(self) -> Option<u32> {
        match self {
            ValueSort::Bool => None,
            ValueSort::BitVec { width, .. } => Some(width),
        }
    }

    fn label(self) -> String {
        match self {
            ValueSort::Bool => "Bool".to_string(),
            ValueSort::BitVec {
                width,
                kind: NumericKind::BitVec,
            } => format!("BitVec({width})"),
            ValueSort::BitVec {
                width,
                kind: NumericKind::Int(Signedness::Signed),
            } => format!("SignedInt({width})"),
            ValueSort::BitVec {
                width,
                kind: NumericKind::Int(Signedness::Unsigned),
            } => format!("UnsignedInt({width})"),
        }
    }

    fn same_width_with_kind(
        self,
        other: ValueSort,
        context: &'static str,
    ) -> Result<Self, FormulaAdapterError> {
        match (self, other) {
            (ValueSort::Bool, ValueSort::Bool) => Ok(ValueSort::Bool),
            (
                ValueSort::BitVec {
                    width: lhs_width,
                    kind: lhs_kind,
                },
                ValueSort::BitVec {
                    width: rhs_width,
                    kind: rhs_kind,
                },
            ) if lhs_width == rhs_width => {
                let kind = if lhs_kind == rhs_kind {
                    lhs_kind
                } else {
                    NumericKind::BitVec
                };
                Ok(ValueSort::BitVec {
                    width: lhs_width,
                    kind,
                })
            }
            (
                ValueSort::BitVec {
                    width: lhs_width, ..
                },
                ValueSort::BitVec {
                    width: rhs_width, ..
                },
            ) => Err(FormulaAdapterError::WidthMismatch {
                context,
                expected: lhs_width,
                actual: rhs_width,
            }),
            (expected, actual) => Err(FormulaAdapterError::SortMismatch {
                context,
                expected: expected.label(),
                actual: actual.label(),
            }),
        }
    }

    fn require_bool(self, context: &'static str) -> Result<(), FormulaAdapterError> {
        if self == ValueSort::Bool {
            Ok(())
        } else {
            Err(FormulaAdapterError::SortMismatch {
                context,
                expected: "Bool".to_string(),
                actual: self.label(),
            })
        }
    }

    fn require_bitvec(
        self,
        context: &'static str,
    ) -> Result<(u32, NumericKind), FormulaAdapterError> {
        match self {
            ValueSort::BitVec { width, kind } => Ok((width, kind)),
            ValueSort::Bool => Err(FormulaAdapterError::SortMismatch {
                context,
                expected: "BitVec".to_string(),
                actual: "Bool".to_string(),
            }),
        }
    }

    fn require_int(self, context: &'static str) -> Result<(u32, Signedness), FormulaAdapterError> {
        match self {
            ValueSort::BitVec {
                width,
                kind: NumericKind::Int(signedness),
            } => Ok((width, signedness)),
            ValueSort::BitVec { .. } => {
                Err(FormulaAdapterError::AmbiguousIntegerSemantics(context))
            }
            ValueSort::Bool => Err(FormulaAdapterError::SortMismatch {
                context,
                expected: "Int".to_string(),
                actual: "Bool".to_string(),
            }),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct TypedSmt {
    expr: SmtExpr,
    sort: ValueSort,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct TypedFormula {
    formula: Formula,
    sort: ValueSort,
}

fn formula_to_typed_smt(
    formula: &Formula,
    ctx: &FormulaAdapterContext,
    expected: Option<ValueSort>,
) -> Result<TypedSmt, FormulaAdapterError> {
    match formula {
        Formula::Bool(value) => Ok(TypedSmt {
            expr: SmtExpr::bool_const(*value),
            sort: ValueSort::Bool,
        }),
        Formula::Int(value) => literal_i128_to_smt(*value, "Int", expected),
        Formula::UInt(value) => literal_u128_to_smt(*value, "UInt", expected),
        Formula::BitVec { value, width } => {
            validate_width(*width)?;
            let sort = ValueSort::bitvec(*width)?;
            if let Some(expected) = expected {
                sort.same_width_with_kind(expected, "BitVec literal")?;
            }
            Ok(TypedSmt {
                expr: SmtExpr::bv_const(i128_to_bv_bits(*value, *width)?, *width),
                sort,
            })
        }
        Formula::Var(name, sort) => formula_var_to_smt(name, sort, ctx),
        Formula::SymVar(sym, sort) => formula_var_to_smt(sym.as_str(), sort, ctx),
        Formula::Not(inner) => {
            let inner = formula_to_typed_smt(inner, ctx, Some(ValueSort::Bool))?;
            inner.sort.require_bool("Not")?;
            Ok(TypedSmt {
                expr: inner.expr.not_expr(),
                sort: ValueSort::Bool,
            })
        }
        Formula::And(terms) => formula_bool_fold_to_smt(terms, ctx, true),
        Formula::Or(terms) => formula_bool_fold_to_smt(terms, ctx, false),
        Formula::Implies(lhs, rhs) => {
            let lhs = formula_to_typed_smt(lhs, ctx, Some(ValueSort::Bool))?;
            let rhs = formula_to_typed_smt(rhs, ctx, Some(ValueSort::Bool))?;
            lhs.sort.require_bool("Implies lhs")?;
            rhs.sort.require_bool("Implies rhs")?;
            Ok(TypedSmt {
                expr: lhs.expr.not_expr().or_expr(rhs.expr),
                sort: ValueSort::Bool,
            })
        }
        Formula::Eq(lhs, rhs) => {
            let (lhs, rhs, _) = formula_pair_same_sort(lhs, rhs, ctx, expected, "Eq")?;
            Ok(TypedSmt {
                expr: lhs.expr.eq_expr(rhs.expr),
                sort: ValueSort::Bool,
            })
        }
        Formula::Lt(lhs, rhs) => formula_int_cmp_to_smt(lhs, rhs, ctx, "Lt"),
        Formula::Le(lhs, rhs) => formula_int_cmp_to_smt(lhs, rhs, ctx, "Le"),
        Formula::Gt(lhs, rhs) => formula_int_cmp_to_smt(lhs, rhs, ctx, "Gt"),
        Formula::Ge(lhs, rhs) => formula_int_cmp_to_smt(lhs, rhs, ctx, "Ge"),
        Formula::Add(lhs, rhs) => formula_int_arith_to_smt(lhs, rhs, ctx, expected, "Add"),
        Formula::Sub(lhs, rhs) => formula_int_arith_to_smt(lhs, rhs, ctx, expected, "Sub"),
        Formula::Mul(lhs, rhs) => formula_int_arith_to_smt(lhs, rhs, ctx, expected, "Mul"),
        Formula::Div(lhs, rhs) => formula_int_arith_to_smt(lhs, rhs, ctx, expected, "Div"),
        Formula::Rem(..) => Err(FormulaAdapterError::UnsupportedFormula("Rem")),
        Formula::Neg(inner) => {
            let inner = formula_to_typed_smt(inner, ctx, expected)?;
            let (_, _) = inner.sort.require_int("Neg")?;
            Ok(TypedSmt {
                expr: inner.expr.bvneg(),
                sort: inner.sort,
            })
        }
        Formula::BvAdd(lhs, rhs, width) => formula_bv_binary_to_smt(lhs, rhs, ctx, *width, "BvAdd"),
        Formula::BvSub(lhs, rhs, width) => formula_bv_binary_to_smt(lhs, rhs, ctx, *width, "BvSub"),
        Formula::BvMul(lhs, rhs, width) => formula_bv_binary_to_smt(lhs, rhs, ctx, *width, "BvMul"),
        Formula::BvUDiv(lhs, rhs, width) => {
            formula_bv_binary_to_smt(lhs, rhs, ctx, *width, "BvUDiv")
        }
        Formula::BvSDiv(lhs, rhs, width) => {
            formula_bv_binary_to_smt(lhs, rhs, ctx, *width, "BvSDiv")
        }
        Formula::BvURem(..) => Err(FormulaAdapterError::UnsupportedFormula("BvURem")),
        Formula::BvSRem(..) => Err(FormulaAdapterError::UnsupportedFormula("BvSRem")),
        Formula::BvAnd(lhs, rhs, width) => formula_bv_binary_to_smt(lhs, rhs, ctx, *width, "BvAnd"),
        Formula::BvOr(lhs, rhs, width) => formula_bv_binary_to_smt(lhs, rhs, ctx, *width, "BvOr"),
        Formula::BvXor(lhs, rhs, width) => formula_bv_binary_to_smt(lhs, rhs, ctx, *width, "BvXor"),
        Formula::BvNot(inner, width) => {
            validate_width(*width)?;
            if *width > 64 {
                return Err(FormulaAdapterError::UnsupportedFormula("BvNot width > 64"));
            }
            let expected = ValueSort::bitvec(*width)?;
            let inner = formula_to_typed_smt(inner, ctx, Some(expected))?;
            require_exact_sort(inner.sort, expected, "BvNot")?;
            Ok(TypedSmt {
                expr: inner
                    .expr
                    .bvxor(SmtExpr::bv_const(mask(u64::MAX, *width), *width)),
                sort: expected,
            })
        }
        Formula::BvShl(lhs, rhs, width) => formula_bv_binary_to_smt(lhs, rhs, ctx, *width, "BvShl"),
        Formula::BvLShr(lhs, rhs, width) => {
            formula_bv_binary_to_smt(lhs, rhs, ctx, *width, "BvLShr")
        }
        Formula::BvAShr(lhs, rhs, width) => {
            formula_bv_binary_to_smt(lhs, rhs, ctx, *width, "BvAShr")
        }
        Formula::BvULt(lhs, rhs, width) => formula_bv_cmp_to_smt(lhs, rhs, ctx, *width, "BvULt"),
        Formula::BvULe(lhs, rhs, width) => formula_bv_cmp_to_smt(lhs, rhs, ctx, *width, "BvULe"),
        Formula::BvSLt(lhs, rhs, width) => formula_bv_cmp_to_smt(lhs, rhs, ctx, *width, "BvSLt"),
        Formula::BvSLe(lhs, rhs, width) => formula_bv_cmp_to_smt(lhs, rhs, ctx, *width, "BvSLe"),
        Formula::BvExtract { inner, high, low } => {
            if high < low {
                return Err(FormulaAdapterError::UnsupportedFormula(
                    "BvExtract high < low",
                ));
            }
            let inner = formula_to_typed_smt(inner, ctx, None)?;
            let (inner_width, _) = inner.sort.require_bitvec("BvExtract")?;
            if *high >= inner_width {
                return Err(FormulaAdapterError::WidthMismatch {
                    context: "BvExtract",
                    expected: inner_width - 1,
                    actual: *high,
                });
            }
            Ok(TypedSmt {
                expr: inner.expr.extract(*high, *low),
                sort: ValueSort::bitvec(high - low + 1)?,
            })
        }
        Formula::BvConcat(lhs, rhs) => {
            let lhs = formula_to_typed_smt(lhs, ctx, None)?;
            let rhs = formula_to_typed_smt(rhs, ctx, None)?;
            let (lhs_width, _) = lhs.sort.require_bitvec("BvConcat lhs")?;
            let (rhs_width, _) = rhs.sort.require_bitvec("BvConcat rhs")?;
            let width = lhs_width
                .checked_add(rhs_width)
                .ok_or(FormulaAdapterError::InvalidWidth(u32::MAX))?;
            validate_width(width)?;
            Ok(TypedSmt {
                expr: lhs.expr.concat(rhs.expr),
                sort: ValueSort::bitvec(width)?,
            })
        }
        Formula::BvZeroExt(inner, extra_bits) => {
            formula_bv_ext_to_smt(inner, ctx, *extra_bits, false)
        }
        Formula::BvSignExt(inner, extra_bits) => {
            formula_bv_ext_to_smt(inner, ctx, *extra_bits, true)
        }
        Formula::Ite(cond, then_expr, else_expr) => {
            let cond = formula_to_typed_smt(cond, ctx, Some(ValueSort::Bool))?;
            cond.sort.require_bool("Ite condition")?;
            let (then_expr, else_expr, sort) =
                formula_pair_same_sort(then_expr, else_expr, ctx, expected, "Ite branches")?;
            if sort == ValueSort::Bool {
                return Err(FormulaAdapterError::UnsupportedFormula("Bool Ite"));
            }
            Ok(TypedSmt {
                expr: SmtExpr::ite(cond.expr, then_expr.expr, else_expr.expr),
                sort,
            })
        }
        Formula::BvToInt(..) => Err(FormulaAdapterError::UnsupportedFormula("BvToInt")),
        Formula::IntToBv(..) => Err(FormulaAdapterError::UnsupportedFormula("IntToBv")),
        Formula::Select(..) => Err(FormulaAdapterError::UnsupportedFormula("Select")),
        Formula::Store(..) => Err(FormulaAdapterError::UnsupportedFormula("Store")),
        Formula::Forall(..) => Err(FormulaAdapterError::UnsupportedFormula("Forall")),
        Formula::Exists(..) => Err(FormulaAdapterError::UnsupportedFormula("Exists")),
        _ => Err(FormulaAdapterError::UnsupportedFormula("unknown")),
    }
}

fn formula_var_to_smt(
    name: &str,
    formula_sort: &Sort,
    ctx: &FormulaAdapterContext,
) -> Result<TypedSmt, FormulaAdapterError> {
    let declared = ctx.var_sort(name)?;
    validate_formula_var_sort(name, formula_sort, declared)?;
    let value_sort = declared.value_sort()?;
    let expr = match declared {
        FormulaAdapterVarSort::Bool => SmtExpr::var(name, 1).eq_expr(SmtExpr::bv_const(1, 1)),
        FormulaAdapterVarSort::BitVec(width)
        | FormulaAdapterVarSort::SignedInt { width }
        | FormulaAdapterVarSort::UnsignedInt { width } => SmtExpr::var(name, width),
    };
    Ok(TypedSmt {
        expr,
        sort: value_sort,
    })
}

fn validate_formula_var_sort(
    name: &str,
    formula_sort: &Sort,
    declared: FormulaAdapterVarSort,
) -> Result<(), FormulaAdapterError> {
    match (formula_sort, declared) {
        (Sort::Bool, FormulaAdapterVarSort::Bool) => Ok(()),
        (Sort::Int, FormulaAdapterVarSort::SignedInt { .. })
        | (Sort::Int, FormulaAdapterVarSort::UnsignedInt { .. }) => Ok(()),
        (Sort::BitVec(expected), FormulaAdapterVarSort::BitVec(actual)) if *expected == actual => {
            Ok(())
        }
        (Sort::Array(_, _), _) => Err(FormulaAdapterError::UnsupportedSort(format!(
            "variable '{name}' has array sort"
        ))),
        (actual, expected) => Err(FormulaAdapterError::SortMismatch {
            context: "variable",
            expected: format!("{expected:?}"),
            actual: formula_sort_label(actual),
        }),
    }
}

fn formula_bool_fold_to_smt(
    terms: &[Formula],
    ctx: &FormulaAdapterContext,
    is_and: bool,
) -> Result<TypedSmt, FormulaAdapterError> {
    let mut expr = SmtExpr::bool_const(is_and);
    for term in terms {
        let term = formula_to_typed_smt(term, ctx, Some(ValueSort::Bool))?;
        term.sort.require_bool(if is_and { "And" } else { "Or" })?;
        expr = if is_and {
            expr.and_expr(term.expr)
        } else {
            expr.or_expr(term.expr)
        };
    }
    Ok(TypedSmt {
        expr,
        sort: ValueSort::Bool,
    })
}

fn formula_pair_same_sort(
    lhs: &Formula,
    rhs: &Formula,
    ctx: &FormulaAdapterContext,
    expected: Option<ValueSort>,
    context: &'static str,
) -> Result<(TypedSmt, TypedSmt, ValueSort), FormulaAdapterError> {
    match formula_to_typed_smt(lhs, ctx, expected) {
        Ok(lhs_typed) => {
            let rhs_typed = formula_to_typed_smt(rhs, ctx, Some(lhs_typed.sort))?;
            let sort = lhs_typed
                .sort
                .same_width_with_kind(rhs_typed.sort, context)?;
            Ok((lhs_typed, rhs_typed, sort))
        }
        Err(FormulaAdapterError::AmbiguousLiteral(_)) if expected.is_none() => {
            let rhs_typed = formula_to_typed_smt(rhs, ctx, None)?;
            let lhs_typed = formula_to_typed_smt(lhs, ctx, Some(rhs_typed.sort))?;
            let sort = lhs_typed
                .sort
                .same_width_with_kind(rhs_typed.sort, context)?;
            Ok((lhs_typed, rhs_typed, sort))
        }
        Err(err) => Err(err),
    }
}

fn formula_int_arith_to_smt(
    lhs: &Formula,
    rhs: &Formula,
    ctx: &FormulaAdapterContext,
    expected: Option<ValueSort>,
    op: &'static str,
) -> Result<TypedSmt, FormulaAdapterError> {
    let (lhs, rhs, sort) = formula_pair_same_sort(lhs, rhs, ctx, expected, op)?;
    let (_, signedness) = sort.require_int(op)?;
    let expr = match op {
        "Add" => lhs.expr.bvadd(rhs.expr),
        "Sub" => lhs.expr.bvsub(rhs.expr),
        "Mul" => lhs.expr.bvmul(rhs.expr),
        "Div" => match signedness {
            Signedness::Signed => lhs.expr.bvsdiv(rhs.expr),
            Signedness::Unsigned => lhs.expr.bvudiv(rhs.expr),
        },
        _ => unreachable!("unknown integer arithmetic op"),
    };
    Ok(TypedSmt { expr, sort })
}

fn formula_int_cmp_to_smt(
    lhs: &Formula,
    rhs: &Formula,
    ctx: &FormulaAdapterContext,
    op: &'static str,
) -> Result<TypedSmt, FormulaAdapterError> {
    let (lhs, rhs, sort) = formula_pair_same_sort(lhs, rhs, ctx, None, op)?;
    let (_, signedness) = sort.require_int(op)?;
    let expr = match (op, signedness) {
        ("Lt", Signedness::Signed) => lhs.expr.bvslt(rhs.expr),
        ("Le", Signedness::Signed) => lhs.expr.bvsle(rhs.expr),
        ("Gt", Signedness::Signed) => lhs.expr.bvsgt(rhs.expr),
        ("Ge", Signedness::Signed) => lhs.expr.bvsge(rhs.expr),
        ("Lt", Signedness::Unsigned) => lhs.expr.bvult(rhs.expr),
        ("Le", Signedness::Unsigned) => lhs.expr.bvule(rhs.expr),
        ("Gt", Signedness::Unsigned) => lhs.expr.bvugt(rhs.expr),
        ("Ge", Signedness::Unsigned) => lhs.expr.bvuge(rhs.expr),
        _ => unreachable!("unknown integer comparison op"),
    };
    Ok(TypedSmt {
        expr,
        sort: ValueSort::Bool,
    })
}

fn formula_bv_binary_to_smt(
    lhs: &Formula,
    rhs: &Formula,
    ctx: &FormulaAdapterContext,
    width: u32,
    op: &'static str,
) -> Result<TypedSmt, FormulaAdapterError> {
    let expected = ValueSort::bitvec(width)?;
    let lhs = formula_to_typed_smt(lhs, ctx, Some(expected))?;
    let rhs = formula_to_typed_smt(rhs, ctx, Some(expected))?;
    require_exact_sort(lhs.sort, expected, op)?;
    require_exact_sort(rhs.sort, expected, op)?;
    let expr = match op {
        "BvAdd" => lhs.expr.bvadd(rhs.expr),
        "BvSub" => lhs.expr.bvsub(rhs.expr),
        "BvMul" => lhs.expr.bvmul(rhs.expr),
        "BvUDiv" => lhs.expr.bvudiv(rhs.expr),
        "BvSDiv" => lhs.expr.bvsdiv(rhs.expr),
        "BvAnd" => lhs.expr.bvand(rhs.expr),
        "BvOr" => lhs.expr.bvor(rhs.expr),
        "BvXor" => lhs.expr.bvxor(rhs.expr),
        "BvShl" => lhs.expr.bvshl(rhs.expr),
        "BvLShr" => lhs.expr.bvlshr(rhs.expr),
        "BvAShr" => lhs.expr.bvashr(rhs.expr),
        _ => unreachable!("unknown bitvector binary op"),
    };
    Ok(TypedSmt {
        expr,
        sort: expected,
    })
}

fn formula_bv_cmp_to_smt(
    lhs: &Formula,
    rhs: &Formula,
    ctx: &FormulaAdapterContext,
    width: u32,
    op: &'static str,
) -> Result<TypedSmt, FormulaAdapterError> {
    let expected = ValueSort::bitvec(width)?;
    let lhs = formula_to_typed_smt(lhs, ctx, Some(expected))?;
    let rhs = formula_to_typed_smt(rhs, ctx, Some(expected))?;
    require_exact_sort(lhs.sort, expected, op)?;
    require_exact_sort(rhs.sort, expected, op)?;
    let expr = match op {
        "BvULt" => lhs.expr.bvult(rhs.expr),
        "BvULe" => lhs.expr.bvule(rhs.expr),
        "BvSLt" => lhs.expr.bvslt(rhs.expr),
        "BvSLe" => lhs.expr.bvsle(rhs.expr),
        _ => unreachable!("unknown bitvector comparison op"),
    };
    Ok(TypedSmt {
        expr,
        sort: ValueSort::Bool,
    })
}

fn formula_bv_ext_to_smt(
    inner: &Formula,
    ctx: &FormulaAdapterContext,
    extra_bits: u32,
    signed: bool,
) -> Result<TypedSmt, FormulaAdapterError> {
    let inner = formula_to_typed_smt(inner, ctx, None)?;
    let (inner_width, _) = inner.sort.require_bitvec("BvExt")?;
    let width = inner_width
        .checked_add(extra_bits)
        .ok_or(FormulaAdapterError::InvalidWidth(u32::MAX))?;
    validate_width(width)?;
    Ok(TypedSmt {
        expr: if signed {
            inner.expr.sign_ext(extra_bits)
        } else {
            inner.expr.zero_ext(extra_bits)
        },
        sort: ValueSort::bitvec(width)?,
    })
}

fn literal_i128_to_smt(
    value: i128,
    label: &'static str,
    expected: Option<ValueSort>,
) -> Result<TypedSmt, FormulaAdapterError> {
    let Some(sort) = expected else {
        return Err(FormulaAdapterError::AmbiguousLiteral(label));
    };
    let (width, _) = sort.require_bitvec(label)?;
    Ok(TypedSmt {
        expr: SmtExpr::bv_const(i128_to_bv_bits_for_sort(value, sort)?, width),
        sort,
    })
}

fn literal_u128_to_smt(
    value: u128,
    label: &'static str,
    expected: Option<ValueSort>,
) -> Result<TypedSmt, FormulaAdapterError> {
    let Some(sort) = expected else {
        return Err(FormulaAdapterError::AmbiguousLiteral(label));
    };
    let (width, kind) = sort.require_bitvec(label)?;
    if matches!(kind, NumericKind::Int(Signedness::Signed)) && value > signed_max(width) as u128 {
        return Err(FormulaAdapterError::LiteralOutOfRange {
            value: value.to_string(),
            width,
        });
    }
    Ok(TypedSmt {
        expr: SmtExpr::bv_const(u128_to_bv_bits(value, width)?, width),
        sort,
    })
}

fn require_exact_sort(
    actual: ValueSort,
    expected: ValueSort,
    context: &'static str,
) -> Result<(), FormulaAdapterError> {
    if actual == expected {
        Ok(())
    } else if actual.width() != expected.width() {
        Err(FormulaAdapterError::WidthMismatch {
            context,
            expected: expected.width().unwrap_or(0),
            actual: actual.width().unwrap_or(0),
        })
    } else {
        Err(FormulaAdapterError::SortMismatch {
            context,
            expected: expected.label(),
            actual: actual.label(),
        })
    }
}

fn smt_to_typed_formula(
    expr: &SmtExpr,
    ctx: &FormulaAdapterContext,
    expected: Option<ValueSort>,
) -> Result<TypedFormula, FormulaAdapterError> {
    if let Some(name) = ctx.bool_var_name(expr) {
        return Ok(TypedFormula {
            formula: Formula::Var(name, Sort::Bool),
            sort: ValueSort::Bool,
        });
    }

    match expr {
        SmtExpr::Var { name, width } => smt_var_to_formula(name, *width, ctx),
        SmtExpr::BvConst { value, width } => smt_const_to_formula(*value, *width, expected),
        SmtExpr::BoolConst(value) => Ok(TypedFormula {
            formula: Formula::Bool(*value),
            sort: ValueSort::Bool,
        }),
        SmtExpr::Eq { lhs, rhs } => {
            let (lhs, rhs, _) = smt_pair_same_sort(lhs, rhs, ctx, expected, "Eq")?;
            Ok(TypedFormula {
                formula: Formula::Eq(Box::new(lhs.formula), Box::new(rhs.formula)),
                sort: ValueSort::Bool,
            })
        }
        SmtExpr::Not { operand } => {
            let operand = smt_to_typed_formula(operand, ctx, Some(ValueSort::Bool))?;
            operand.sort.require_bool("Not")?;
            Ok(TypedFormula {
                formula: Formula::Not(Box::new(operand.formula)),
                sort: ValueSort::Bool,
            })
        }
        SmtExpr::And { lhs, rhs } => {
            let lhs = smt_to_typed_formula(lhs, ctx, Some(ValueSort::Bool))?;
            let rhs = smt_to_typed_formula(rhs, ctx, Some(ValueSort::Bool))?;
            lhs.sort.require_bool("And lhs")?;
            rhs.sort.require_bool("And rhs")?;
            let mut terms = Vec::new();
            flatten_formula_and(lhs.formula, &mut terms);
            flatten_formula_and(rhs.formula, &mut terms);
            Ok(TypedFormula {
                formula: Formula::And(terms),
                sort: ValueSort::Bool,
            })
        }
        SmtExpr::Or { lhs, rhs } => {
            let lhs = smt_to_typed_formula(lhs, ctx, Some(ValueSort::Bool))?;
            let rhs = smt_to_typed_formula(rhs, ctx, Some(ValueSort::Bool))?;
            lhs.sort.require_bool("Or lhs")?;
            rhs.sort.require_bool("Or rhs")?;
            let mut terms = Vec::new();
            flatten_formula_or(lhs.formula, &mut terms);
            flatten_formula_or(rhs.formula, &mut terms);
            Ok(TypedFormula {
                formula: Formula::Or(terms),
                sort: ValueSort::Bool,
            })
        }
        SmtExpr::BvAdd { lhs, rhs, width } => {
            smt_binary_to_formula(lhs, rhs, ctx, *width, expected, "BvAdd")
        }
        SmtExpr::BvSub { lhs, rhs, width } => {
            smt_binary_to_formula(lhs, rhs, ctx, *width, expected, "BvSub")
        }
        SmtExpr::BvMul { lhs, rhs, width } => {
            smt_binary_to_formula(lhs, rhs, ctx, *width, expected, "BvMul")
        }
        SmtExpr::BvSDiv { lhs, rhs, width } => {
            smt_binary_to_formula(lhs, rhs, ctx, *width, expected, "BvSDiv")
        }
        SmtExpr::BvUDiv { lhs, rhs, width } => {
            smt_binary_to_formula(lhs, rhs, ctx, *width, expected, "BvUDiv")
        }
        SmtExpr::BvURem { .. } => Err(FormulaAdapterError::UnsupportedFormula("BvURem")),
        // The hardware-trap (x86 IDIV/DIV #DE) poison model has no faithful image
        // in the trust `Formula` algebra (which has no poison/undef value), so this
        // adapter fails CLOSED rather than dropping the trap semantics. The trap is
        // modeled in the native evaluator and the ay-API/SMT-LIB lanes instead.
        SmtExpr::TrapIfZero { .. } => Err(FormulaAdapterError::UnsupportedSmtExpr("TrapIfZero")),
        SmtExpr::BvNeg { operand, width } => {
            let expected = expected.unwrap_or(ValueSort::bitvec(*width)?);
            let operand = smt_to_typed_formula(operand, ctx, Some(expected))?;
            require_exact_sort(operand.sort, expected, "BvNeg")?;
            let formula = match expected {
                ValueSort::BitVec {
                    kind: NumericKind::Int(_),
                    ..
                } => Formula::Neg(Box::new(operand.formula)),
                ValueSort::BitVec { width, .. } => Formula::BvSub(
                    Box::new(Formula::BitVec { value: 0, width }),
                    Box::new(operand.formula),
                    width,
                ),
                ValueSort::Bool => unreachable!("BvNeg expected bitvector sort"),
            };
            Ok(TypedFormula {
                formula,
                sort: expected,
            })
        }
        SmtExpr::BvSlt { lhs, rhs, width } => smt_cmp_to_formula(lhs, rhs, ctx, *width, "BvSlt"),
        SmtExpr::BvSge { lhs, rhs, width } => smt_cmp_to_formula(lhs, rhs, ctx, *width, "BvSge"),
        SmtExpr::BvSgt { lhs, rhs, width } => smt_cmp_to_formula(lhs, rhs, ctx, *width, "BvSgt"),
        SmtExpr::BvSle { lhs, rhs, width } => smt_cmp_to_formula(lhs, rhs, ctx, *width, "BvSle"),
        SmtExpr::BvUlt { lhs, rhs, width } => smt_cmp_to_formula(lhs, rhs, ctx, *width, "BvUlt"),
        SmtExpr::BvUge { lhs, rhs, width } => smt_cmp_to_formula(lhs, rhs, ctx, *width, "BvUge"),
        SmtExpr::BvUgt { lhs, rhs, width } => smt_cmp_to_formula(lhs, rhs, ctx, *width, "BvUgt"),
        SmtExpr::BvUle { lhs, rhs, width } => smt_cmp_to_formula(lhs, rhs, ctx, *width, "BvUle"),
        SmtExpr::BvAnd { lhs, rhs, width } => {
            smt_binary_to_formula(lhs, rhs, ctx, *width, expected, "BvAnd")
        }
        SmtExpr::BvOr { lhs, rhs, width } => {
            smt_binary_to_formula(lhs, rhs, ctx, *width, expected, "BvOr")
        }
        SmtExpr::BvXor { lhs, rhs, width } => {
            smt_binary_to_formula(lhs, rhs, ctx, *width, expected, "BvXor")
        }
        SmtExpr::BvShl { lhs, rhs, width } => {
            smt_binary_to_formula(lhs, rhs, ctx, *width, expected, "BvShl")
        }
        SmtExpr::BvLshr { lhs, rhs, width } => {
            smt_binary_to_formula(lhs, rhs, ctx, *width, expected, "BvLshr")
        }
        SmtExpr::BvAshr { lhs, rhs, width } => {
            smt_binary_to_formula(lhs, rhs, ctx, *width, expected, "BvAshr")
        }
        SmtExpr::Ite {
            cond,
            then_expr,
            else_expr,
        } => {
            let cond = smt_to_typed_formula(cond, ctx, Some(ValueSort::Bool))?;
            cond.sort.require_bool("Ite condition")?;
            let (then_expr, else_expr, sort) =
                smt_pair_same_sort(then_expr, else_expr, ctx, expected, "Ite branches")?;
            Ok(TypedFormula {
                formula: Formula::Ite(
                    Box::new(cond.formula),
                    Box::new(then_expr.formula),
                    Box::new(else_expr.formula),
                ),
                sort,
            })
        }
        SmtExpr::Extract {
            high,
            low,
            operand,
            width,
        } => {
            let operand = smt_to_typed_formula(operand, ctx, None)?;
            Ok(TypedFormula {
                formula: Formula::BvExtract {
                    inner: Box::new(operand.formula),
                    high: *high,
                    low: *low,
                },
                sort: ValueSort::bitvec(*width)?,
            })
        }
        SmtExpr::Concat { hi, lo, width } => {
            let hi = smt_to_typed_formula(hi, ctx, None)?;
            let lo = smt_to_typed_formula(lo, ctx, None)?;
            Ok(TypedFormula {
                formula: Formula::BvConcat(Box::new(hi.formula), Box::new(lo.formula)),
                sort: ValueSort::bitvec(*width)?,
            })
        }
        SmtExpr::ZeroExtend {
            operand,
            extra_bits,
            width,
        } => {
            let operand = smt_to_typed_formula(operand, ctx, None)?;
            Ok(TypedFormula {
                formula: Formula::BvZeroExt(Box::new(operand.formula), *extra_bits),
                sort: ValueSort::bitvec(*width)?,
            })
        }
        SmtExpr::SignExtend {
            operand,
            extra_bits,
            width,
        } => {
            let operand = smt_to_typed_formula(operand, ctx, None)?;
            Ok(TypedFormula {
                formula: Formula::BvSignExt(Box::new(operand.formula), *extra_bits),
                sort: ValueSort::bitvec(*width)?,
            })
        }
        SmtExpr::Select { .. } => Err(FormulaAdapterError::UnsupportedSmtExpr("Select")),
        SmtExpr::Store { .. } => Err(FormulaAdapterError::UnsupportedSmtExpr("Store")),
        SmtExpr::ConstArray { .. } => Err(FormulaAdapterError::UnsupportedSmtExpr("ConstArray")),
        // The trust Formula algebra has no memory-load node. Do not erase the
        // address-dependent memory semantics by translating it as an opaque
        // scalar expression.
        SmtExpr::MemLoad { .. } => Err(FormulaAdapterError::UnsupportedSmtExpr("MemLoad")),
        SmtExpr::FPAdd { .. }
        | SmtExpr::FPMul { .. }
        | SmtExpr::FPSub { .. }
        | SmtExpr::FPDiv { .. }
        | SmtExpr::FPNeg { .. }
        | SmtExpr::FPEq { .. }
        | SmtExpr::FPLt { .. }
        | SmtExpr::FPGt { .. }
        | SmtExpr::FPGe { .. }
        | SmtExpr::FPLe { .. }
        | SmtExpr::FPConst { .. }
        | SmtExpr::FPSqrt { .. }
        | SmtExpr::FPRoundToIntegral { .. }
        | SmtExpr::FPAbs { .. }
        | SmtExpr::FPFma { .. }
        | SmtExpr::FPIsNaN { .. }
        | SmtExpr::FPIsInf { .. }
        | SmtExpr::FPIsZero { .. }
        | SmtExpr::FPIsNormal { .. }
        | SmtExpr::FPToSBv { .. }
        | SmtExpr::FPToUBv { .. }
        | SmtExpr::BvToFP { .. }
        | SmtExpr::FPToFP { .. }
        | SmtExpr::BvBitsToFP { .. } => {
            Err(FormulaAdapterError::UnsupportedSmtExpr("FloatingPoint"))
        }
        SmtExpr::UF { .. } => Err(FormulaAdapterError::UnsupportedSmtExpr("UF")),
        SmtExpr::UFDecl { .. } => Err(FormulaAdapterError::UnsupportedSmtExpr("UFDecl")),
        SmtExpr::ForAll { .. } => Err(FormulaAdapterError::UnsupportedSmtExpr("ForAll")),
        SmtExpr::Exists { .. } => Err(FormulaAdapterError::UnsupportedSmtExpr("Exists")),
    }
}

fn smt_var_to_formula(
    name: &str,
    width: u32,
    ctx: &FormulaAdapterContext,
) -> Result<TypedFormula, FormulaAdapterError> {
    let declared = ctx.var_sort(name)?;
    let Some(expected_width) = declared.width() else {
        return Err(FormulaAdapterError::SortMismatch {
            context: "SmtExpr variable",
            expected: "Bool encoding".to_string(),
            actual: format!("BitVec({width})"),
        });
    };
    if expected_width != width {
        return Err(FormulaAdapterError::WidthMismatch {
            context: "SmtExpr variable",
            expected: expected_width,
            actual: width,
        });
    }
    Ok(TypedFormula {
        formula: Formula::Var(name.to_string(), declared.trust_sort()),
        sort: declared.value_sort()?,
    })
}

fn smt_const_to_formula(
    value: u64,
    width: u32,
    expected: Option<ValueSort>,
) -> Result<TypedFormula, FormulaAdapterError> {
    validate_width(width)?;
    let sort = expected.unwrap_or(ValueSort::bitvec(width)?);
    let (expected_width, kind) = sort.require_bitvec("BvConst")?;
    if expected_width != width {
        return Err(FormulaAdapterError::WidthMismatch {
            context: "BvConst",
            expected: expected_width,
            actual: width,
        });
    }
    let formula = match kind {
        NumericKind::BitVec => Formula::BitVec {
            value: i128::from(value),
            width,
        },
        NumericKind::Int(Signedness::Signed) => Formula::Int(bv_bits_to_signed_i128(value, width)),
        NumericKind::Int(Signedness::Unsigned) => Formula::UInt(u128::from(value)),
    };
    Ok(TypedFormula { formula, sort })
}

fn smt_pair_same_sort(
    lhs: &SmtExpr,
    rhs: &SmtExpr,
    ctx: &FormulaAdapterContext,
    expected: Option<ValueSort>,
    context: &'static str,
) -> Result<(TypedFormula, TypedFormula, ValueSort), FormulaAdapterError> {
    let lhs_typed = smt_to_typed_formula(lhs, ctx, expected)?;
    let rhs_typed = smt_to_typed_formula(rhs, ctx, Some(lhs_typed.sort))?;
    let sort = lhs_typed
        .sort
        .same_width_with_kind(rhs_typed.sort, context)?;
    Ok((lhs_typed, rhs_typed, sort))
}

fn smt_binary_to_formula(
    lhs: &SmtExpr,
    rhs: &SmtExpr,
    ctx: &FormulaAdapterContext,
    width: u32,
    expected: Option<ValueSort>,
    op: &'static str,
) -> Result<TypedFormula, FormulaAdapterError> {
    let (lhs, rhs, sort) = smt_pair_same_sort(lhs, rhs, ctx, expected, op)?;
    let (actual_width, _) = sort.require_bitvec(op)?;
    if actual_width != width {
        return Err(FormulaAdapterError::WidthMismatch {
            context: op,
            expected: width,
            actual: actual_width,
        });
    }
    let formula = match (op, sort) {
        (
            "BvAdd",
            ValueSort::BitVec {
                kind: NumericKind::Int(_),
                ..
            },
        ) => Formula::Add(Box::new(lhs.formula), Box::new(rhs.formula)),
        (
            "BvSub",
            ValueSort::BitVec {
                kind: NumericKind::Int(_),
                ..
            },
        ) => Formula::Sub(Box::new(lhs.formula), Box::new(rhs.formula)),
        (
            "BvMul",
            ValueSort::BitVec {
                kind: NumericKind::Int(_),
                ..
            },
        ) => Formula::Mul(Box::new(lhs.formula), Box::new(rhs.formula)),
        (
            "BvSDiv",
            ValueSort::BitVec {
                kind: NumericKind::Int(Signedness::Signed),
                ..
            },
        )
        | (
            "BvUDiv",
            ValueSort::BitVec {
                kind: NumericKind::Int(Signedness::Unsigned),
                ..
            },
        ) => Formula::Div(Box::new(lhs.formula), Box::new(rhs.formula)),
        ("BvAdd", _) => Formula::BvAdd(Box::new(lhs.formula), Box::new(rhs.formula), width),
        ("BvSub", _) => Formula::BvSub(Box::new(lhs.formula), Box::new(rhs.formula), width),
        ("BvMul", _) => Formula::BvMul(Box::new(lhs.formula), Box::new(rhs.formula), width),
        ("BvSDiv", _) => Formula::BvSDiv(Box::new(lhs.formula), Box::new(rhs.formula), width),
        ("BvUDiv", _) => Formula::BvUDiv(Box::new(lhs.formula), Box::new(rhs.formula), width),
        ("BvAnd", _) => Formula::BvAnd(Box::new(lhs.formula), Box::new(rhs.formula), width),
        ("BvOr", _) => Formula::BvOr(Box::new(lhs.formula), Box::new(rhs.formula), width),
        ("BvXor", _) => Formula::BvXor(Box::new(lhs.formula), Box::new(rhs.formula), width),
        ("BvShl", _) => Formula::BvShl(Box::new(lhs.formula), Box::new(rhs.formula), width),
        ("BvLshr", _) => Formula::BvLShr(Box::new(lhs.formula), Box::new(rhs.formula), width),
        ("BvAshr", _) => Formula::BvAShr(Box::new(lhs.formula), Box::new(rhs.formula), width),
        _ => unreachable!("unknown SmtExpr binary op"),
    };
    Ok(TypedFormula { formula, sort })
}

fn smt_cmp_to_formula(
    lhs: &SmtExpr,
    rhs: &SmtExpr,
    ctx: &FormulaAdapterContext,
    width: u32,
    op: &'static str,
) -> Result<TypedFormula, FormulaAdapterError> {
    let (lhs, rhs, sort) = smt_pair_same_sort(lhs, rhs, ctx, None, op)?;
    let (actual_width, _) = sort.require_bitvec(op)?;
    if actual_width != width {
        return Err(FormulaAdapterError::WidthMismatch {
            context: op,
            expected: width,
            actual: actual_width,
        });
    }
    let formula = match (op, sort) {
        (
            "BvSlt",
            ValueSort::BitVec {
                kind: NumericKind::Int(Signedness::Signed),
                ..
            },
        )
        | (
            "BvUlt",
            ValueSort::BitVec {
                kind: NumericKind::Int(Signedness::Unsigned),
                ..
            },
        ) => Formula::Lt(Box::new(lhs.formula), Box::new(rhs.formula)),
        (
            "BvSle",
            ValueSort::BitVec {
                kind: NumericKind::Int(Signedness::Signed),
                ..
            },
        )
        | (
            "BvUle",
            ValueSort::BitVec {
                kind: NumericKind::Int(Signedness::Unsigned),
                ..
            },
        ) => Formula::Le(Box::new(lhs.formula), Box::new(rhs.formula)),
        (
            "BvSgt",
            ValueSort::BitVec {
                kind: NumericKind::Int(Signedness::Signed),
                ..
            },
        )
        | (
            "BvUgt",
            ValueSort::BitVec {
                kind: NumericKind::Int(Signedness::Unsigned),
                ..
            },
        ) => Formula::Gt(Box::new(lhs.formula), Box::new(rhs.formula)),
        (
            "BvSge",
            ValueSort::BitVec {
                kind: NumericKind::Int(Signedness::Signed),
                ..
            },
        )
        | (
            "BvUge",
            ValueSort::BitVec {
                kind: NumericKind::Int(Signedness::Unsigned),
                ..
            },
        ) => Formula::Ge(Box::new(lhs.formula), Box::new(rhs.formula)),
        ("BvSlt", _) => Formula::BvSLt(Box::new(lhs.formula), Box::new(rhs.formula), width),
        ("BvSle", _) => Formula::BvSLe(Box::new(lhs.formula), Box::new(rhs.formula), width),
        ("BvSgt", _) => Formula::BvSLt(Box::new(rhs.formula), Box::new(lhs.formula), width),
        ("BvSge", _) => Formula::BvSLe(Box::new(rhs.formula), Box::new(lhs.formula), width),
        ("BvUlt", _) => Formula::BvULt(Box::new(lhs.formula), Box::new(rhs.formula), width),
        ("BvUle", _) => Formula::BvULe(Box::new(lhs.formula), Box::new(rhs.formula), width),
        ("BvUgt", _) => Formula::BvULt(Box::new(rhs.formula), Box::new(lhs.formula), width),
        ("BvUge", _) => Formula::BvULe(Box::new(rhs.formula), Box::new(lhs.formula), width),
        _ => unreachable!("unknown SmtExpr comparison op"),
    };
    Ok(TypedFormula {
        formula,
        sort: ValueSort::Bool,
    })
}

fn flatten_formula_and(formula: Formula, out: &mut Vec<Formula>) {
    match formula {
        Formula::And(terms) => out.extend(terms),
        Formula::Bool(true) => {}
        other => out.push(other),
    }
}

fn flatten_formula_or(formula: Formula, out: &mut Vec<Formula>) {
    match formula {
        Formula::Or(terms) => out.extend(terms),
        Formula::Bool(false) => {}
        other => out.push(other),
    }
}

fn i128_to_bv_bits_for_sort(value: i128, sort: ValueSort) -> Result<u64, FormulaAdapterError> {
    let (width, kind) = sort.require_bitvec("literal")?;
    match kind {
        NumericKind::Int(Signedness::Signed) => {
            if value < signed_min(width) || value > signed_max(width) {
                return Err(FormulaAdapterError::LiteralOutOfRange {
                    value: value.to_string(),
                    width,
                });
            }
        }
        NumericKind::Int(Signedness::Unsigned) if value < 0 => {
            return Err(FormulaAdapterError::LiteralOutOfRange {
                value: value.to_string(),
                width,
            });
        }
        _ => {}
    }
    i128_to_bv_bits(value, width)
}

fn i128_to_bv_bits(value: i128, width: u32) -> Result<u64, FormulaAdapterError> {
    validate_width(width)?;
    let bits = if value >= 0 {
        value as u128
    } else {
        let min = signed_min(width);
        if value < min {
            return Err(FormulaAdapterError::LiteralOutOfRange {
                value: value.to_string(),
                width,
            });
        }
        twos_complement_bits(value, width)
    };
    u128_to_bv_bits(bits, width)
}

fn u128_to_bv_bits(value: u128, width: u32) -> Result<u64, FormulaAdapterError> {
    validate_width(width)?;
    if !fits_unsigned_width(value, width) || value > u128::from(u64::MAX) {
        return Err(FormulaAdapterError::LiteralOutOfRange {
            value: value.to_string(),
            width,
        });
    }
    Ok(value as u64)
}

fn bv_bits_to_signed_i128(value: u64, width: u32) -> i128 {
    debug_assert!((1..=128).contains(&width));
    if width > 64 {
        return i128::from(value);
    }
    if width == 64 {
        return (value as i64) as i128;
    }
    let sign_bit = 1u64 << (width - 1);
    if value & sign_bit == 0 {
        i128::from(value)
    } else {
        i128::from(value) - (1i128 << width)
    }
}

fn twos_complement_bits(value: i128, width: u32) -> u128 {
    if width == 128 {
        value as u128
    } else {
        ((1i128 << width) + value) as u128
    }
}

fn signed_min(width: u32) -> i128 {
    if width == 128 {
        i128::MIN
    } else {
        -(1i128 << (width - 1))
    }
}

fn signed_max(width: u32) -> i128 {
    if width == 128 {
        i128::MAX
    } else {
        (1i128 << (width - 1)) - 1
    }
}

fn fits_unsigned_width(value: u128, width: u32) -> bool {
    width == 128 || value < (1u128 << width)
}

fn validate_width(width: u32) -> Result<(), FormulaAdapterError> {
    if (1..=128).contains(&width) {
        Ok(())
    } else {
        Err(FormulaAdapterError::InvalidWidth(width))
    }
}

fn formula_sort_label(sort: &Sort) -> String {
    match sort {
        Sort::Bool => "Bool".to_string(),
        Sort::Int => "Int".to_string(),
        Sort::BitVec(width) => format!("BitVec({width})"),
        Sort::Array(_, _) => "Array".to_string(),
        _ => "unknown".to_string(),
    }
}
