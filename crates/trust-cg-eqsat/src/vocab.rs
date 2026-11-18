// crates/trust-cg-eqsat/src/vocab.rs - scalar types, operator descriptors and their byte codes
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The vocabulary shared by the graph, the rules and the derivation format
//! (`docs/eqsat-tier-e.md` sections 2.1, 2.2 and 7.2).
//!
//! The codes here are the version-1 byte codes of section 7.2 and nothing
//! else; the checker reads them with its own table. A scalar type's width is
//! resolved against the module's pointer width only for `isize`/`usize`, and
//! only when that width is 32 or 64 ([`GraphWidths`]); otherwise those two
//! types are not graph types at all.

use trust_ir::{BinOp, CastOp, ICmpOp, Ty, UnOp};

/// A scalar graph type: `Bool` or an integer type of section 2.1.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ScalarTy {
    /// `bool`, width 1.
    Bool,
    /// `i8`.
    I8,
    /// `i16`.
    I16,
    /// `i32`.
    I32,
    /// `i64`.
    I64,
    /// `i128`.
    I128,
    /// `isize` (pointer width; a graph type only at 32 or 64 bits).
    Isize,
    /// `u8`.
    U8,
    /// `u16`.
    U16,
    /// `u32`.
    U32,
    /// `u64`.
    U64,
    /// `u128`.
    U128,
    /// `usize` (pointer width; a graph type only at 32 or 64 bits).
    Usize,
}

impl ScalarTy {
    /// Every scalar type, in code order.
    pub const ALL: [ScalarTy; 13] = [
        ScalarTy::Bool,
        ScalarTy::I8,
        ScalarTy::I16,
        ScalarTy::I32,
        ScalarTy::I64,
        ScalarTy::I128,
        ScalarTy::Isize,
        ScalarTy::U8,
        ScalarTy::U16,
        ScalarTy::U32,
        ScalarTy::U64,
        ScalarTy::U128,
        ScalarTy::Usize,
    ];

    /// The section 7.2 type code.
    #[must_use]
    pub const fn code(self) -> u8 {
        match self {
            ScalarTy::Bool => 0x01,
            ScalarTy::I8 => 0x10,
            ScalarTy::I16 => 0x11,
            ScalarTy::I32 => 0x12,
            ScalarTy::I64 => 0x13,
            ScalarTy::I128 => 0x14,
            ScalarTy::Isize => 0x15,
            ScalarTy::U8 => 0x20,
            ScalarTy::U16 => 0x21,
            ScalarTy::U32 => 0x22,
            ScalarTy::U64 => 0x23,
            ScalarTy::U128 => 0x24,
            ScalarTy::Usize => 0x25,
        }
    }

    /// The type with section 7.2 code `code`, if any.
    #[must_use]
    pub fn from_code(code: u8) -> Option<ScalarTy> {
        ScalarTy::ALL.into_iter().find(|ty| ty.code() == code)
    }

    /// The rule-file spelling (section 5.1 `TYPE`).
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            ScalarTy::Bool => "bool",
            ScalarTy::I8 => "i8",
            ScalarTy::I16 => "i16",
            ScalarTy::I32 => "i32",
            ScalarTy::I64 => "i64",
            ScalarTy::I128 => "i128",
            ScalarTy::Isize => "isize",
            ScalarTy::U8 => "u8",
            ScalarTy::U16 => "u16",
            ScalarTy::U32 => "u32",
            ScalarTy::U64 => "u64",
            ScalarTy::U128 => "u128",
            ScalarTy::Usize => "usize",
        }
    }

    /// The type spelled `name` in a rule file.
    #[must_use]
    pub fn from_name(name: &str) -> Option<ScalarTy> {
        ScalarTy::ALL.into_iter().find(|ty| ty.name() == name)
    }

    /// Whether this is `Bool`.
    #[must_use]
    pub const fn is_bool(self) -> bool {
        matches!(self, ScalarTy::Bool)
    }

    /// Whether the signed reading applies (only used for display; section 3
    /// reads every comparison predicate by its own signedness, not the type's).
    #[must_use]
    pub const fn is_signed(self) -> bool {
        matches!(
            self,
            ScalarTy::I8
                | ScalarTy::I16
                | ScalarTy::I32
                | ScalarTy::I64
                | ScalarTy::I128
                | ScalarTy::Isize
        )
    }

    /// The trust-ir type this scalar type stands for.
    #[must_use]
    pub fn to_ty(self) -> Ty {
        match self {
            ScalarTy::Bool => Ty::Bool,
            ScalarTy::I8 => Ty::I8,
            ScalarTy::I16 => Ty::I16,
            ScalarTy::I32 => Ty::I32,
            ScalarTy::I64 => Ty::I64,
            ScalarTy::I128 => Ty::I128,
            ScalarTy::Isize => Ty::Isize,
            ScalarTy::U8 => Ty::U8,
            ScalarTy::U16 => Ty::U16,
            ScalarTy::U32 => Ty::U32,
            ScalarTy::U64 => Ty::U64,
            ScalarTy::U128 => Ty::U128,
            ScalarTy::Usize => Ty::Usize,
        }
    }
}

/// The widths of the scalar types in one module: `isize`/`usize` resolve to
/// the module's pointer width when it is 32 or 64, and are not graph types
/// otherwise (section 2.1).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct GraphWidths {
    pointer_bits: Option<u32>,
}

impl GraphWidths {
    /// Widths for a module whose `Module::pointer_bits()` is `pointer_bits`.
    #[must_use]
    pub const fn new(pointer_bits: u32) -> Self {
        let pointer_bits = match pointer_bits {
            32 | 64 => Some(pointer_bits),
            _ => None,
        };
        Self { pointer_bits }
    }

    /// The width of `ty`, or `None` when `ty` is not a graph type here.
    #[must_use]
    pub const fn width(self, ty: ScalarTy) -> Option<u32> {
        Some(match ty {
            ScalarTy::Bool => 1,
            ScalarTy::I8 | ScalarTy::U8 => 8,
            ScalarTy::I16 | ScalarTy::U16 => 16,
            ScalarTy::I32 | ScalarTy::U32 => 32,
            ScalarTy::I64 | ScalarTy::U64 => 64,
            ScalarTy::I128 | ScalarTy::U128 => 128,
            ScalarTy::Isize | ScalarTy::Usize => match self.pointer_bits {
                Some(bits) => bits,
                None => return None,
            },
        })
    }

    /// Whether `ty` is a graph type in this module.
    #[must_use]
    pub const fn admits(self, ty: ScalarTy) -> bool {
        self.width(ty).is_some()
    }

    /// The scalar graph type of a trust-ir type: exact `Bool` or an exact
    /// integer type of `IT` (never `char`, a refinement or a vector).
    #[must_use]
    pub fn scalar(self, ty: &Ty) -> Option<ScalarTy> {
        let scalar = match ty {
            Ty::Bool => ScalarTy::Bool,
            Ty::I8 => ScalarTy::I8,
            Ty::I16 => ScalarTy::I16,
            Ty::I32 => ScalarTy::I32,
            Ty::I64 => ScalarTy::I64,
            Ty::I128 => ScalarTy::I128,
            Ty::Isize => ScalarTy::Isize,
            Ty::U8 => ScalarTy::U8,
            Ty::U16 => ScalarTy::U16,
            Ty::U32 => ScalarTy::U32,
            Ty::U64 => ScalarTy::U64,
            Ty::U128 => ScalarTy::U128,
            Ty::Usize => ScalarTy::Usize,
            _ => return None,
        };
        self.admits(scalar).then_some(scalar)
    }
}

/// The mask of a `width`-bit residue (`width` in 1..=128).
#[must_use]
pub const fn mask(width: u32) -> u128 {
    if width >= 128 {
        u128::MAX
    } else {
        (1u128 << width) - 1
    }
}

/// Binary operator codes (section 7.2 `Bin`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum BinOpCode {
    /// `add`, code 1.
    Add,
    /// `sub`, code 2.
    Sub,
    /// `mul`, code 3.
    Mul,
    /// `and`, code 4.
    And,
    /// `or`, code 5.
    Or,
    /// `xor`, code 6.
    Xor,
    /// `rotl`, code 7.
    RotL,
    /// `rotr`, code 8.
    RotR,
    /// `band`, code 9.
    BAnd,
    /// `bor`, code 10.
    BOr,
    /// `bxor`, code 11.
    BXor,
}

impl BinOpCode {
    /// Every binary operator, in code order.
    pub const ALL: [BinOpCode; 11] = [
        BinOpCode::Add,
        BinOpCode::Sub,
        BinOpCode::Mul,
        BinOpCode::And,
        BinOpCode::Or,
        BinOpCode::Xor,
        BinOpCode::RotL,
        BinOpCode::RotR,
        BinOpCode::BAnd,
        BinOpCode::BOr,
        BinOpCode::BXor,
    ];

    /// The section 7.2 code.
    #[must_use]
    pub const fn code(self) -> u8 {
        match self {
            BinOpCode::Add => 1,
            BinOpCode::Sub => 2,
            BinOpCode::Mul => 3,
            BinOpCode::And => 4,
            BinOpCode::Or => 5,
            BinOpCode::Xor => 6,
            BinOpCode::RotL => 7,
            BinOpCode::RotR => 8,
            BinOpCode::BAnd => 9,
            BinOpCode::BOr => 10,
            BinOpCode::BXor => 11,
        }
    }

    /// The rule-file spelling.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            BinOpCode::Add => "add",
            BinOpCode::Sub => "sub",
            BinOpCode::Mul => "mul",
            BinOpCode::And => "and",
            BinOpCode::Or => "or",
            BinOpCode::Xor => "xor",
            BinOpCode::RotL => "rotl",
            BinOpCode::RotR => "rotr",
            BinOpCode::BAnd => "band",
            BinOpCode::BOr => "bor",
            BinOpCode::BXor => "bxor",
        }
    }

    /// Whether the operator is admitted at `ty` (section 2.2): the integer
    /// operators at `IT`, `and or xor` also at `Bool`, `band bor bxor` only
    /// at `Bool`.
    #[must_use]
    pub const fn admitted_at(self, ty: ScalarTy) -> bool {
        match self {
            BinOpCode::Add
            | BinOpCode::Sub
            | BinOpCode::Mul
            | BinOpCode::RotL
            | BinOpCode::RotR => !ty.is_bool(),
            BinOpCode::And | BinOpCode::Or | BinOpCode::Xor => true,
            BinOpCode::BAnd | BinOpCode::BOr | BinOpCode::BXor => ty.is_bool(),
        }
    }

    /// The graph operator of a trust-ir binary operator, if it has one.
    #[must_use]
    pub const fn from_ir(op: BinOp) -> Option<BinOpCode> {
        Some(match op {
            BinOp::Add => BinOpCode::Add,
            BinOp::Sub => BinOpCode::Sub,
            BinOp::Mul => BinOpCode::Mul,
            BinOp::And => BinOpCode::And,
            BinOp::Or => BinOpCode::Or,
            BinOp::Xor => BinOpCode::Xor,
            BinOp::RotL => BinOpCode::RotL,
            BinOp::RotR => BinOpCode::RotR,
            BinOp::BAnd => BinOpCode::BAnd,
            BinOp::BOr => BinOpCode::BOr,
            BinOp::BXor => BinOpCode::BXor,
            BinOp::UDiv
            | BinOp::SDiv
            | BinOp::URem
            | BinOp::SRem
            | BinOp::Shl
            | BinOp::LShr
            | BinOp::AShr
            | BinOp::FAdd
            | BinOp::FSub
            | BinOp::FMul
            | BinOp::FDiv
            | BinOp::FRem
            | BinOp::FMin
            | BinOp::FMax
            | BinOp::FCopySign => return None,
        })
    }

    /// The trust-ir operator that this graph operator is emitted as.
    #[must_use]
    pub const fn to_ir(self) -> BinOp {
        match self {
            BinOpCode::Add => BinOp::Add,
            BinOpCode::Sub => BinOp::Sub,
            BinOpCode::Mul => BinOp::Mul,
            BinOpCode::And => BinOp::And,
            BinOpCode::Or => BinOp::Or,
            BinOpCode::Xor => BinOp::Xor,
            BinOpCode::RotL => BinOp::RotL,
            BinOpCode::RotR => BinOp::RotR,
            BinOpCode::BAnd => BinOp::BAnd,
            BinOpCode::BOr => BinOp::BOr,
            BinOpCode::BXor => BinOp::BXor,
        }
    }
}

/// Unary operator codes (section 7.2 `Un`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum UnOpCode {
    /// `neg`, code 1.
    Neg,
    /// `not`, code 2.
    Not,
    /// `ctpop`, code 3.
    CtPop,
    /// `ctlz`, code 4.
    CtLz,
    /// `cttz`, code 5.
    CtTz,
    /// `bswap`, code 6.
    BSwap,
    /// `bitreverse`, code 7.
    BitReverse,
}

impl UnOpCode {
    /// Every unary operator, in code order.
    pub const ALL: [UnOpCode; 7] = [
        UnOpCode::Neg,
        UnOpCode::Not,
        UnOpCode::CtPop,
        UnOpCode::CtLz,
        UnOpCode::CtTz,
        UnOpCode::BSwap,
        UnOpCode::BitReverse,
    ];

    /// The section 7.2 code.
    #[must_use]
    pub const fn code(self) -> u8 {
        match self {
            UnOpCode::Neg => 1,
            UnOpCode::Not => 2,
            UnOpCode::CtPop => 3,
            UnOpCode::CtLz => 4,
            UnOpCode::CtTz => 5,
            UnOpCode::BSwap => 6,
            UnOpCode::BitReverse => 7,
        }
    }

    /// The rule-file spelling.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            UnOpCode::Neg => "neg",
            UnOpCode::Not => "not",
            UnOpCode::CtPop => "ctpop",
            UnOpCode::CtLz => "ctlz",
            UnOpCode::CtTz => "cttz",
            UnOpCode::BSwap => "bswap",
            UnOpCode::BitReverse => "bitreverse",
        }
    }

    /// Whether the operator is admitted at `ty`: `IT` only (section 2.2).
    #[must_use]
    pub const fn admitted_at(self, ty: ScalarTy) -> bool {
        !ty.is_bool()
    }

    /// The graph operator of a trust-ir unary operator, if it has one.
    #[must_use]
    pub const fn from_ir(op: UnOp) -> Option<UnOpCode> {
        Some(match op {
            UnOp::Neg => UnOpCode::Neg,
            UnOp::Not => UnOpCode::Not,
            UnOp::CtPop => UnOpCode::CtPop,
            UnOp::CtLz => UnOpCode::CtLz,
            UnOp::CtTz => UnOpCode::CtTz,
            UnOp::BSwap => UnOpCode::BSwap,
            UnOp::BitReverse => UnOpCode::BitReverse,
            UnOp::FNeg | UnOp::FAbs | UnOp::FSqrt | UnOp::FFloor | UnOp::FCeil | UnOp::FTrunc => {
                return None;
            }
        })
    }

    /// The trust-ir operator that this graph operator is emitted as.
    #[must_use]
    pub const fn to_ir(self) -> UnOp {
        match self {
            UnOpCode::Neg => UnOp::Neg,
            UnOpCode::Not => UnOp::Not,
            UnOpCode::CtPop => UnOp::CtPop,
            UnOpCode::CtLz => UnOp::CtLz,
            UnOpCode::CtTz => UnOp::CtTz,
            UnOpCode::BSwap => UnOp::BSwap,
            UnOpCode::BitReverse => UnOp::BitReverse,
        }
    }
}

/// Comparison predicate codes (section 7.2 `Cmp`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CmpPred {
    /// `eq`, code 1.
    Eq,
    /// `ne`, code 2.
    Ne,
    /// `ult`, code 3.
    Ult,
    /// `ule`, code 4.
    Ule,
    /// `ugt`, code 5.
    Ugt,
    /// `uge`, code 6.
    Uge,
    /// `slt`, code 7.
    Slt,
    /// `sle`, code 8.
    Sle,
    /// `sgt`, code 9.
    Sgt,
    /// `sge`, code 10.
    Sge,
}

impl CmpPred {
    /// Every predicate, in code order.
    pub const ALL: [CmpPred; 10] = [
        CmpPred::Eq,
        CmpPred::Ne,
        CmpPred::Ult,
        CmpPred::Ule,
        CmpPred::Ugt,
        CmpPred::Uge,
        CmpPred::Slt,
        CmpPred::Sle,
        CmpPred::Sgt,
        CmpPred::Sge,
    ];

    /// The section 7.2 code.
    #[must_use]
    pub const fn code(self) -> u8 {
        match self {
            CmpPred::Eq => 1,
            CmpPred::Ne => 2,
            CmpPred::Ult => 3,
            CmpPred::Ule => 4,
            CmpPred::Ugt => 5,
            CmpPred::Uge => 6,
            CmpPred::Slt => 7,
            CmpPred::Sle => 8,
            CmpPred::Sgt => 9,
            CmpPred::Sge => 10,
        }
    }

    /// The rule-file spelling (`icmp.` + predicate).
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            CmpPred::Eq => "icmp.eq",
            CmpPred::Ne => "icmp.ne",
            CmpPred::Ult => "icmp.ult",
            CmpPred::Ule => "icmp.ule",
            CmpPred::Ugt => "icmp.ugt",
            CmpPred::Uge => "icmp.uge",
            CmpPred::Slt => "icmp.slt",
            CmpPred::Sle => "icmp.sle",
            CmpPred::Sgt => "icmp.sgt",
            CmpPred::Sge => "icmp.sge",
        }
    }

    /// Whether the predicate is admitted at operand type `ty`: every
    /// predicate at `IT`, only `eq`/`ne` at `Bool` (section 2.2).
    #[must_use]
    pub const fn admitted_at(self, ty: ScalarTy) -> bool {
        !ty.is_bool() || matches!(self, CmpPred::Eq | CmpPred::Ne)
    }

    /// The graph predicate of a trust-ir integer predicate.
    #[must_use]
    pub const fn from_ir(op: ICmpOp) -> CmpPred {
        match op {
            ICmpOp::Eq => CmpPred::Eq,
            ICmpOp::Ne => CmpPred::Ne,
            ICmpOp::Ult => CmpPred::Ult,
            ICmpOp::Ule => CmpPred::Ule,
            ICmpOp::Ugt => CmpPred::Ugt,
            ICmpOp::Uge => CmpPred::Uge,
            ICmpOp::Slt => CmpPred::Slt,
            ICmpOp::Sle => CmpPred::Sle,
            ICmpOp::Sgt => CmpPred::Sgt,
            ICmpOp::Sge => CmpPred::Sge,
        }
    }

    /// The trust-ir predicate this graph predicate is emitted as.
    #[must_use]
    pub const fn to_ir(self) -> ICmpOp {
        match self {
            CmpPred::Eq => ICmpOp::Eq,
            CmpPred::Ne => ICmpOp::Ne,
            CmpPred::Ult => ICmpOp::Ult,
            CmpPred::Ule => ICmpOp::Ule,
            CmpPred::Ugt => ICmpOp::Ugt,
            CmpPred::Uge => ICmpOp::Uge,
            CmpPred::Slt => ICmpOp::Slt,
            CmpPred::Sle => ICmpOp::Sle,
            CmpPred::Sgt => ICmpOp::Sgt,
            CmpPred::Sge => ICmpOp::Sge,
        }
    }
}

/// Cast operator codes (section 7.2 `Cast`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CastOpCode {
    /// `trunc`, code 1.
    Trunc,
    /// `zext`, code 2.
    ZExt,
    /// `sext`, code 3.
    SExt,
}

impl CastOpCode {
    /// Every cast operator, in code order.
    pub const ALL: [CastOpCode; 3] = [CastOpCode::Trunc, CastOpCode::ZExt, CastOpCode::SExt];

    /// The section 7.2 code.
    #[must_use]
    pub const fn code(self) -> u8 {
        match self {
            CastOpCode::Trunc => 1,
            CastOpCode::ZExt => 2,
            CastOpCode::SExt => 3,
        }
    }

    /// A short name.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            CastOpCode::Trunc => "trunc",
            CastOpCode::ZExt => "zext",
            CastOpCode::SExt => "sext",
        }
    }

    /// The graph cast of a trust-ir cast operator, if it has one.
    #[must_use]
    pub const fn from_ir(op: CastOp) -> Option<CastOpCode> {
        Some(match op {
            CastOp::Trunc => CastOpCode::Trunc,
            CastOp::ZExt => CastOpCode::ZExt,
            CastOp::SExt => CastOpCode::SExt,
            CastOp::FPTrunc
            | CastOp::FPExt
            | CastOp::FPToUI
            | CastOp::FPToSI
            | CastOp::UIToFP
            | CastOp::SIToFP
            | CastOp::PtrToInt
            | CastOp::IntToPtr
            | CastOp::PtrToPtr
            | CastOp::Bitcast
            | CastOp::Transmute
            | CastOp::ReifyFnPointer
            | CastOp::FPToSISat
            | CastOp::FPToUISat => return None,
        })
    }

    /// The trust-ir cast this graph cast is emitted as.
    #[must_use]
    pub const fn to_ir(self) -> CastOp {
        match self {
            CastOpCode::Trunc => CastOp::Trunc,
            CastOpCode::ZExt => CastOp::ZExt,
            CastOpCode::SExt => CastOp::SExt,
        }
    }
}

/// A term operator with its types (section 7.2 `opdesc`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum OpDesc {
    /// `Bin(op, T)`: arity 2, result `T`.
    Bin(BinOpCode, ScalarTy),
    /// `Un(op, T)`: arity 1, result `T`.
    Un(UnOpCode, ScalarTy),
    /// `Cmp(pred, T)` over operands of type `T`: arity 2, result `Bool`.
    Cmp(CmpPred, ScalarTy),
    /// `Cast(op, S, D)`: arity 1, operand `S`, result `D`.
    Cast(CastOpCode, ScalarTy, ScalarTy),
    /// `Select(T)`: arity 3 (`Bool`, `T`, `T`), result `T`.
    Select(ScalarTy),
    /// `Pinned(order, T)`: a reduction whose order is pinned in the operator
    /// (`docs/eqsat-tier-s.md` section 2.2): arity 1, operand `T`, result
    /// `T`. A Tier S region operator only: no trust-ir instruction denotes
    /// it, the Tier E reader never makes one, and a version-1 derivation
    /// that names one is refused by the checker.
    Pinned(u32, ScalarTy),
}

impl OpDesc {
    /// The number of operands.
    #[must_use]
    pub const fn arity(self) -> usize {
        match self {
            OpDesc::Bin(..) | OpDesc::Cmp(..) => 2,
            OpDesc::Un(..) | OpDesc::Cast(..) | OpDesc::Pinned(..) => 1,
            OpDesc::Select(_) => 3,
        }
    }

    /// The result type.
    #[must_use]
    pub const fn result_ty(self) -> ScalarTy {
        match self {
            OpDesc::Bin(_, ty) | OpDesc::Un(_, ty) | OpDesc::Select(ty) | OpDesc::Pinned(_, ty) => {
                ty
            }
            OpDesc::Cmp(..) => ScalarTy::Bool,
            OpDesc::Cast(_, _, dst) => dst,
        }
    }

    /// The type of operand `index` (`None` past the arity).
    #[must_use]
    pub const fn operand_ty(self, index: usize) -> Option<ScalarTy> {
        match (self, index) {
            (OpDesc::Bin(_, ty) | OpDesc::Cmp(_, ty), 0 | 1) => Some(ty),
            (OpDesc::Un(_, ty) | OpDesc::Pinned(_, ty), 0) => Some(ty),
            (OpDesc::Cast(_, src, _), 0) => Some(src),
            (OpDesc::Select(_), 0) => Some(ScalarTy::Bool),
            (OpDesc::Select(ty), 1 | 2) => Some(ty),
            _ => None,
        }
    }

    /// Whether the operator is admitted at its types (section 2.2): a cast
    /// needs both types in `IT`, a pinned reduction an integer type.
    #[must_use]
    pub const fn admitted(self) -> bool {
        match self {
            OpDesc::Bin(op, ty) => op.admitted_at(ty),
            OpDesc::Un(op, ty) => op.admitted_at(ty),
            OpDesc::Cmp(pred, ty) => pred.admitted_at(ty),
            OpDesc::Cast(_, src, dst) => !src.is_bool() && !dst.is_bool(),
            OpDesc::Select(_) => true,
            OpDesc::Pinned(_, ty) => !ty.is_bool(),
        }
    }

    /// The static extraction cost of section 6 (a pinned reduction:
    /// `docs/eqsat-tier-s.md` section 5).
    #[must_use]
    pub const fn cost(self) -> u64 {
        match self {
            OpDesc::Bin(BinOpCode::Mul, _) => 3,
            OpDesc::Un(
                UnOpCode::CtPop
                | UnOpCode::CtLz
                | UnOpCode::CtTz
                | UnOpCode::BSwap
                | UnOpCode::BitReverse,
                _,
            ) => 2,
            OpDesc::Pinned(..) => REDUCTION_COST,
            OpDesc::Bin(..)
            | OpDesc::Un(..)
            | OpDesc::Cmp(..)
            | OpDesc::Cast(..)
            | OpDesc::Select(_) => 1,
        }
    }

    /// The operator class name used by [`crate::Stats::forms_by_class`].
    #[must_use]
    pub const fn class_name(self) -> &'static str {
        match self {
            OpDesc::Bin(op, _) => op.name(),
            OpDesc::Un(op, _) => op.name(),
            OpDesc::Cmp(..) => "icmp",
            OpDesc::Cast(..) => "cast",
            OpDesc::Select(_) => "select",
            OpDesc::Pinned(..) => "pinned",
        }
    }

    /// Append the section 7.2 `opdesc` bytes.
    pub fn encode(self, out: &mut Vec<u8>) {
        match self {
            OpDesc::Bin(op, ty) => out.extend_from_slice(&[0x01, op.code(), ty.code()]),
            OpDesc::Un(op, ty) => out.extend_from_slice(&[0x02, op.code(), ty.code()]),
            OpDesc::Cmp(pred, ty) => out.extend_from_slice(&[0x03, pred.code(), ty.code()]),
            OpDesc::Cast(op, src, dst) => {
                out.extend_from_slice(&[0x04, op.code(), src.code(), dst.code()]);
            }
            OpDesc::Select(ty) => out.extend_from_slice(&[0x05, ty.code()]),
            OpDesc::Pinned(order, ty) => {
                out.push(0x06);
                out.extend_from_slice(&order.to_le_bytes());
                out.push(ty.code());
            }
        }
    }
}

/// Static cost of a constant node (section 6).
pub const CONST_COST: u64 = 1;

/// Static cost of a see-through copy in the input body (section 6).
pub const COPY_COST: u64 = 1;

/// Static cost of a reduction, pinned or order-free
/// (`docs/eqsat-tier-s.md` section 5). The two cost the same, so an
/// order-free node is elaborated only where that shares a pinned reduction
/// the region already computes.
pub const REDUCTION_COST: u64 = 4;
