// trust-cg-eqsat-check/src/types.rs - scalar graph types and operator descriptors
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The scalar graph types (`IT` plus `Bool`, docs/eqsat-tier-e.md section
//! 2.1) and the operator descriptors of section 2.2, with their byte codes
//! (section 7.2) and their admission rules.
//!
//! Admission is stated once here and used by every consumer: the body reader
//! (which instruction is a graph instruction), the term table (which term is
//! well typed), the rule registry (which operator a rule may name at which
//! domain type) and proof replay. A type whose width is not established
//! (`isize`/`usize` when `Module::pointer_bits()` is neither 32 nor 64) is not
//! a graph type at all.

use trust_ir::Ty;

/// A scalar graph type. `Isize`/`Usize` are graph types only under a
/// [`Ctx`] whose pointer width is 32 or 64.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum Sty {
    Bool,
    I8,
    I16,
    I32,
    I64,
    I128,
    Isize,
    U8,
    U16,
    U32,
    U64,
    U128,
    Usize,
}

/// Every scalar type, in registry spelling order.
pub(crate) const ALL_STY: [Sty; 13] = [
    Sty::I8,
    Sty::I16,
    Sty::I32,
    Sty::I64,
    Sty::I128,
    Sty::Isize,
    Sty::U8,
    Sty::U16,
    Sty::U32,
    Sty::U64,
    Sty::U128,
    Sty::Usize,
    Sty::Bool,
];

impl Sty {
    /// The section 7.2 type code.
    pub(crate) const fn code(self) -> u8 {
        match self {
            Sty::Bool => 0x01,
            Sty::I8 => 0x10,
            Sty::I16 => 0x11,
            Sty::I32 => 0x12,
            Sty::I64 => 0x13,
            Sty::I128 => 0x14,
            Sty::Isize => 0x15,
            Sty::U8 => 0x20,
            Sty::U16 => 0x21,
            Sty::U32 => 0x22,
            Sty::U64 => 0x23,
            Sty::U128 => 0x24,
            Sty::Usize => 0x25,
        }
    }

    /// Decodes a section 7.2 type code; any other byte is `None`.
    pub(crate) fn from_code(code: u8) -> Option<Sty> {
        ALL_STY.iter().copied().find(|s| s.code() == code)
    }

    /// The rule-file spelling (section 5.1 `TYPE`).
    pub(crate) const fn name(self) -> &'static str {
        match self {
            Sty::Bool => "bool",
            Sty::I8 => "i8",
            Sty::I16 => "i16",
            Sty::I32 => "i32",
            Sty::I64 => "i64",
            Sty::I128 => "i128",
            Sty::Isize => "isize",
            Sty::U8 => "u8",
            Sty::U16 => "u16",
            Sty::U32 => "u32",
            Sty::U64 => "u64",
            Sty::U128 => "u128",
            Sty::Usize => "usize",
        }
    }

    /// Parses a rule-file `TYPE`.
    pub(crate) fn from_name(name: &str) -> Option<Sty> {
        ALL_STY.iter().copied().find(|s| s.name() == name)
    }

    pub(crate) const fn is_bool(self) -> bool {
        matches!(self, Sty::Bool)
    }

    /// Whether a trust-ir constant of this type reads its value as signed.
    pub(crate) const fn is_signed(self) -> bool {
        matches!(
            self,
            Sty::I8 | Sty::I16 | Sty::I32 | Sty::I64 | Sty::I128 | Sty::Isize
        )
    }

    /// The trust-ir type this scalar type denotes.
    pub(crate) fn to_ir(self) -> Ty {
        match self {
            Sty::Bool => Ty::Bool,
            Sty::I8 => Ty::I8,
            Sty::I16 => Ty::I16,
            Sty::I32 => Ty::I32,
            Sty::I64 => Ty::I64,
            Sty::I128 => Ty::I128,
            Sty::Isize => Ty::Isize,
            Sty::U8 => Ty::U8,
            Sty::U16 => Ty::U16,
            Sty::U32 => Ty::U32,
            Sty::U64 => Ty::U64,
            Sty::U128 => Ty::U128,
            Sty::Usize => Ty::Usize,
        }
    }

    /// The scalar graph type a trust-ir type is, under `ctx`. Every other type
    /// (char, floats, vectors, refinements, pointers, aggregates, and
    /// pointer-width integers at an unestablished width) is `None`.
    pub(crate) fn from_ir(ty: &Ty, ctx: Ctx) -> Option<Sty> {
        let sty = match ty {
            Ty::Bool => Sty::Bool,
            Ty::I8 => Sty::I8,
            Ty::I16 => Sty::I16,
            Ty::I32 => Sty::I32,
            Ty::I64 => Sty::I64,
            Ty::I128 => Sty::I128,
            Ty::Isize => Sty::Isize,
            Ty::U8 => Sty::U8,
            Ty::U16 => Sty::U16,
            Ty::U32 => Sty::U32,
            Ty::U64 => Sty::U64,
            Ty::U128 => Sty::U128,
            Ty::Usize => Sty::Usize,
            _ => return None,
        };
        ctx.width(sty).map(|_| sty)
    }
}

/// The module facts the checker reads types under.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Ctx {
    /// `Module::pointer_bits()`.
    pub(crate) pointer_bits: u32,
}

impl Ctx {
    /// The width of `sty`, or `None` when it is not established (a
    /// pointer-width integer at a pointer width other than 32 or 64).
    pub(crate) fn width(self, sty: Sty) -> Option<u32> {
        Some(match sty {
            Sty::Bool => 1,
            Sty::I8 | Sty::U8 => 8,
            Sty::I16 | Sty::U16 => 16,
            Sty::I32 | Sty::U32 => 32,
            Sty::I64 | Sty::U64 => 64,
            Sty::I128 | Sty::U128 => 128,
            Sty::Isize | Sty::Usize => match self.pointer_bits {
                32 | 64 => self.pointer_bits,
                _ => return None,
            },
        })
    }
}

/// `2^w - 1` for `1 <= w <= 128`.
pub(crate) const fn mask(width: u32) -> u128 {
    if width >= 128 {
        u128::MAX
    } else {
        (1u128 << width) - 1
    }
}

/// Binary graph operators (section 7.2 codes 1..=11).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum BinK {
    Add,
    Sub,
    Mul,
    And,
    Or,
    Xor,
    RotL,
    RotR,
    BAnd,
    BOr,
    BXor,
}

pub(crate) const ALL_BIN: [BinK; 11] = [
    BinK::Add,
    BinK::Sub,
    BinK::Mul,
    BinK::And,
    BinK::Or,
    BinK::Xor,
    BinK::RotL,
    BinK::RotR,
    BinK::BAnd,
    BinK::BOr,
    BinK::BXor,
];

impl BinK {
    pub(crate) const fn code(self) -> u8 {
        match self {
            BinK::Add => 1,
            BinK::Sub => 2,
            BinK::Mul => 3,
            BinK::And => 4,
            BinK::Or => 5,
            BinK::Xor => 6,
            BinK::RotL => 7,
            BinK::RotR => 8,
            BinK::BAnd => 9,
            BinK::BOr => 10,
            BinK::BXor => 11,
        }
    }

    pub(crate) const fn name(self) -> &'static str {
        match self {
            BinK::Add => "add",
            BinK::Sub => "sub",
            BinK::Mul => "mul",
            BinK::And => "and",
            BinK::Or => "or",
            BinK::Xor => "xor",
            BinK::RotL => "rotl",
            BinK::RotR => "rotr",
            BinK::BAnd => "band",
            BinK::BOr => "bor",
            BinK::BXor => "bxor",
        }
    }

    /// Whether the operator works on `Bool` operands only.
    pub(crate) const fn is_bool_only(self) -> bool {
        matches!(self, BinK::BAnd | BinK::BOr | BinK::BXor)
    }

    /// Whether the operator is admitted at `Bool` as well as at `IT`.
    pub(crate) const fn admits_bool(self) -> bool {
        matches!(
            self,
            BinK::And | BinK::Or | BinK::Xor | BinK::BAnd | BinK::BOr | BinK::BXor
        )
    }
}

/// Unary graph operators (section 7.2 codes 1..=7).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum UnK {
    Neg,
    Not,
    CtPop,
    CtLz,
    CtTz,
    BSwap,
    BitReverse,
}

pub(crate) const ALL_UN: [UnK; 7] = [
    UnK::Neg,
    UnK::Not,
    UnK::CtPop,
    UnK::CtLz,
    UnK::CtTz,
    UnK::BSwap,
    UnK::BitReverse,
];

impl UnK {
    pub(crate) const fn code(self) -> u8 {
        match self {
            UnK::Neg => 1,
            UnK::Not => 2,
            UnK::CtPop => 3,
            UnK::CtLz => 4,
            UnK::CtTz => 5,
            UnK::BSwap => 6,
            UnK::BitReverse => 7,
        }
    }

    pub(crate) const fn name(self) -> &'static str {
        match self {
            UnK::Neg => "neg",
            UnK::Not => "not",
            UnK::CtPop => "ctpop",
            UnK::CtLz => "ctlz",
            UnK::CtTz => "cttz",
            UnK::BSwap => "bswap",
            UnK::BitReverse => "bitreverse",
        }
    }
}

/// Integer comparison predicates (section 7.2 codes 1..=10).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum Pred {
    Eq,
    Ne,
    Ult,
    Ule,
    Ugt,
    Uge,
    Slt,
    Sle,
    Sgt,
    Sge,
}

pub(crate) const ALL_PRED: [Pred; 10] = [
    Pred::Eq,
    Pred::Ne,
    Pred::Ult,
    Pred::Ule,
    Pred::Ugt,
    Pred::Uge,
    Pred::Slt,
    Pred::Sle,
    Pred::Sgt,
    Pred::Sge,
];

impl Pred {
    pub(crate) const fn code(self) -> u8 {
        match self {
            Pred::Eq => 1,
            Pred::Ne => 2,
            Pred::Ult => 3,
            Pred::Ule => 4,
            Pred::Ugt => 5,
            Pred::Uge => 6,
            Pred::Slt => 7,
            Pred::Sle => 8,
            Pred::Sgt => 9,
            Pred::Sge => 10,
        }
    }

    pub(crate) const fn name(self) -> &'static str {
        match self {
            Pred::Eq => "eq",
            Pred::Ne => "ne",
            Pred::Ult => "ult",
            Pred::Ule => "ule",
            Pred::Ugt => "ugt",
            Pred::Uge => "uge",
            Pred::Slt => "slt",
            Pred::Sle => "sle",
            Pred::Sgt => "sgt",
            Pred::Sge => "sge",
        }
    }

    /// Whether the predicate is admitted at `Bool` (only `eq` and `ne`).
    pub(crate) const fn admits_bool(self) -> bool {
        matches!(self, Pred::Eq | Pred::Ne)
    }
}

/// Integer resize casts (section 7.2 codes 1..=3).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum CastK {
    Trunc,
    ZExt,
    SExt,
}

pub(crate) const ALL_CAST: [CastK; 3] = [CastK::Trunc, CastK::ZExt, CastK::SExt];

impl CastK {
    pub(crate) const fn code(self) -> u8 {
        match self {
            CastK::Trunc => 1,
            CastK::ZExt => 2,
            CastK::SExt => 3,
        }
    }

    pub(crate) const fn name(self) -> &'static str {
        match self {
            CastK::Trunc => "trunc",
            CastK::ZExt => "zext",
            CastK::SExt => "sext",
        }
    }
}

/// A term operator with its types (section 2.2 / the 7.2 `opdesc`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum OpDesc {
    Bin(BinK, Sty),
    Un(UnK, Sty),
    Cmp(Pred, Sty),
    Cast(CastK, Sty, Sty),
    Select(Sty),
}

impl OpDesc {
    pub(crate) const fn arity(self) -> usize {
        match self {
            OpDesc::Bin(..) | OpDesc::Cmp(..) => 2,
            OpDesc::Un(..) | OpDesc::Cast(..) => 1,
            OpDesc::Select(_) => 3,
        }
    }

    /// Operand types, in operand order.
    pub(crate) fn operand_tys(self) -> Vec<Sty> {
        match self {
            OpDesc::Bin(_, t) | OpDesc::Cmp(_, t) => vec![t, t],
            OpDesc::Un(_, t) => vec![t],
            OpDesc::Cast(_, s, _) => vec![s],
            OpDesc::Select(t) => vec![Sty::Bool, t, t],
        }
    }

    pub(crate) const fn result_ty(self) -> Sty {
        match self {
            OpDesc::Bin(_, t) | OpDesc::Un(_, t) | OpDesc::Select(t) => t,
            OpDesc::Cmp(..) => Sty::Bool,
            OpDesc::Cast(_, _, d) => d,
        }
    }

    /// The type-category part of admission (section 2.2), independent of the
    /// module: integer-only operators refuse `Bool`, `band bor bxor` require
    /// `Bool`, casts are between integers only.
    pub(crate) const fn admitted_category(self) -> bool {
        match self {
            OpDesc::Bin(k, t) => {
                if k.is_bool_only() {
                    t.is_bool()
                } else {
                    !t.is_bool() || k.admits_bool()
                }
            }
            OpDesc::Un(_, t) => !t.is_bool(),
            OpDesc::Cmp(p, t) => !t.is_bool() || p.admits_bool(),
            OpDesc::Cast(_, s, d) => !s.is_bool() && !d.is_bool(),
            OpDesc::Select(_) => true,
        }
    }

    /// Full admission under `ctx`: the category rule and every type a graph
    /// type of this module.
    pub(crate) fn admitted(self, ctx: Ctx) -> bool {
        let types_ok = match self {
            OpDesc::Bin(_, t) | OpDesc::Un(_, t) | OpDesc::Cmp(_, t) | OpDesc::Select(t) => {
                ctx.width(t).is_some()
            }
            OpDesc::Cast(_, s, d) => ctx.width(s).is_some() && ctx.width(d).is_some(),
        };
        types_ok && self.admitted_category()
    }

    /// A short rendering for diagnostics, e.g. `add.u32`.
    pub(crate) fn describe(self) -> String {
        match self {
            OpDesc::Bin(k, t) => format!("{}.{}", k.name(), t.name()),
            OpDesc::Un(k, t) => format!("{}.{}", k.name(), t.name()),
            OpDesc::Cmp(p, t) => format!("icmp.{}.{}", p.name(), t.name()),
            OpDesc::Cast(k, s, d) => format!("{}.{}.{}", k.name(), s.name(), d.name()),
            OpDesc::Select(t) => format!("select.{}", t.name()),
        }
    }
}
