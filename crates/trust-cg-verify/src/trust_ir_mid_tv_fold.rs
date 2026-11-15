// trust-cg-verify/trust_ir_mid_tv_fold.rs - the constant folding checker
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The checker of the mid-end's constant folding ([`ConstFoldWitness`]).
//!
//! Each claimed fold names a value defined as the single result of an
//! instruction whose operands are all `const`s (in the source, or folded by
//! an earlier fold of the same witness, which this checker applies in
//! order), and the constant the pass replaced it with. This module evaluates
//! the instruction itself, with the reference interpreter's integer
//! semantics restated here (every constant masked to its type's width,
//! arithmetic modulo the width, signed division and the comparisons reading
//! the bits as two's complement whatever the type's signedness), and
//! accepts the fold only when the instruction raises nothing on those
//! operands and the claimed constant is exactly the canonical spelling of
//! its result at the instruction's result type: `const bool` for a
//! comparison, and for an integer type of at most 64 bits the value in the
//! type's own range (signed types negative where the sign bit is set). The
//! folded instruction becomes `const <result type> <constant>` in place,
//! under the same result. Exact: the source computes that value there and
//! raises nothing.
//!
//! The forms: integer `add`, `sub`, `mul`, `and`, `or`, `xor`, rotates,
//! shifts by an amount below the width, unsigned division and remainder by a
//! nonzero divisor, signed ones by a divisor other than zero that does not
//! overflow; `and`, `or`, `xor` and the boolean connectives over `bool`
//! constants; `neg` and `not` of an integer; `icmp` of integers or `bool`s;
//! and the `zext`, `sext`, `trunc` and same-width `bitcast` casts between
//! integers (a `bool` operand of an extension read as one bit, as the
//! interpreter reads it). A `const bool` the rustc bridge spells as the
//! integer 0 or 1 is respelled `false` or `true`: the interpreter's view of
//! the lane's idioms and the wasm32 lane read the two spellings alike, and
//! trust-ir's validator reports the integer one (`ConstTypeMismatch`), which
//! a callee's copy would otherwise carry into its caller. Likewise an
//! integer constant of at most 64 bits spelled outside its type's range
//! (`const i8 254`) is respelled as the constant of the same bits at the
//! type's width (`const i8 -2`): the reference interpreter
//! (`InterpretInt::from_i128`) and the wasm32 lane (`carrier_value`) both
//! read the constant's bits at the width. Every integer operand must have the width of the
//! type the instruction declares for it (the interpreter's view converts
//! another integer type of the same width by its bits, and faults on any
//! other); integers wider than 64 bits are not folded. Everything else is
//! refused.

use std::collections::{HashMap, HashSet};

use trust_ir::{
    BinOp, BlockId, CastOp, Constant, Function, ICmpOp, Inst, InstrNode, Ty, UnOp, ValueId,
};

use super::loops::value_types;
use super::{MidTvError, WitnessVerdict, int_shape};

/// One fold: the instruction defining `value` becomes `const <its result
/// type> constant`.
#[derive(Debug, Clone, PartialEq)]
pub struct ConstFold {
    pub value: ValueId,
    pub constant: Constant,
}

/// Constant folding's claim, applied in order.
#[derive(Debug, Clone, Default, PartialEq)]
pub struct ConstFoldWitness {
    pub folds: Vec<ConstFold>,
}

fn refuse(value: ValueId, why: impl Into<String>) -> MidTvError {
    MidTvError::NotConstantFold {
        value,
        why: why.into(),
    }
}

/// All ones at `bits` (1 to 128).
fn mask(bits: u32) -> u128 {
    if bits >= 128 {
        u128::MAX
    } else {
        (1u128 << bits) - 1
    }
}

/// `raw` (masked to `bits`) read as two's complement.
fn signed(raw: u128, bits: u32) -> i128 {
    if bits >= 128 {
        return raw as i128;
    }
    let sign = 1u128 << (bits - 1);
    if raw & sign == 0 {
        raw as i128
    } else {
        (raw | !mask(bits)) as i128
    }
}

/// A constant operand: its bits at its width, or a `bool`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Operand {
    Int { bits: u32, raw: u128 },
    Bool(bool),
}

/// What the constant instruction `inst` holds, read as the interpreter reads
/// it, for the forms this checker folds.
fn operand(pointer_bits: u32, inst: &Inst) -> Option<Operand> {
    match inst {
        Inst::Const {
            ty,
            value: Constant::Int(k),
        } => {
            let (bits, _) = int_shape(ty, pointer_bits)?;
            (bits <= 64).then(|| Operand::Int {
                bits,
                raw: (*k as u128) & mask(bits),
            })
        }
        Inst::Const {
            ty: Ty::Bool,
            value: Constant::Bool(b),
        } => Some(Operand::Bool(*b)),
        _ => None,
    }
}

/// The canonical constant of `raw` at the integer type `ty` (`bits` wide).
fn int_constant(ty: &Ty, bits: u32, raw: u128) -> Constant {
    if ty.is_signed() {
        Constant::Int(signed(raw, bits))
    } else {
        Constant::Int(raw as i128)
    }
}

/// The result of `inst` on constant operands, as the canonical constant of
/// its result type, or why it is not folded.
fn evaluate(
    lookup: &dyn Fn(ValueId) -> Option<Operand>,
    pointer_bits: u32,
    inst: &Inst,
) -> Result<(Ty, Constant), &'static str> {
    let int_of = |v: ValueId, bits: u32| -> Result<u128, &'static str> {
        match lookup(v) {
            Some(Operand::Int { bits: b, raw }) if b == bits => Ok(raw),
            Some(Operand::Int { .. }) => Err("an operand has another width"),
            Some(Operand::Bool(_)) => Err("an integer operand is a bool"),
            None => Err("an operand is not a constant"),
        }
    };
    let bool_of = |v: ValueId| -> Result<bool, &'static str> {
        match lookup(v) {
            Some(Operand::Bool(b)) => Ok(b),
            _ => Err("a bool operand is not a bool constant"),
        }
    };
    match inst {
        Inst::BinOp { op, ty, lhs, rhs } if *ty == Ty::Bool => {
            let (a, b) = (bool_of(*lhs)?, bool_of(*rhs)?);
            let r = match op {
                BinOp::And | BinOp::BAnd => a & b,
                BinOp::Or | BinOp::BOr => a | b,
                BinOp::Xor | BinOp::BXor => a ^ b,
                _ => return Err("not a boolean operation"),
            };
            Ok((Ty::Bool, Constant::Bool(r)))
        }
        Inst::BinOp { op, ty, lhs, rhs } => {
            let (bits, _) = int_shape(ty, pointer_bits).ok_or("not an integer operation")?;
            if bits > 64 {
                return Err("wider than 64 bits");
            }
            let (a, b) = (int_of(*lhs, bits)?, int_of(*rhs, bits)?);
            let m = mask(bits);
            let raw = match op {
                BinOp::Add => a.wrapping_add(b),
                BinOp::Sub => a.wrapping_sub(b),
                BinOp::Mul => a.wrapping_mul(b),
                BinOp::And => a & b,
                BinOp::Or => a | b,
                BinOp::Xor => a ^ b,
                BinOp::Shl | BinOp::LShr | BinOp::AShr => {
                    if b >= u128::from(bits) {
                        return Err("the shift amount is not below the width");
                    }
                    let n = b as u32;
                    match op {
                        BinOp::Shl => a << n,
                        BinOp::LShr => a >> n,
                        _ => (signed(a, bits) >> n) as u128,
                    }
                }
                BinOp::UDiv | BinOp::URem => {
                    if b == 0 {
                        return Err("a division by zero");
                    }
                    if *op == BinOp::UDiv { a / b } else { a % b }
                }
                BinOp::SDiv | BinOp::SRem => {
                    let (x, y) = (signed(a, bits), signed(b, bits));
                    if y == 0 {
                        return Err("a division by zero");
                    }
                    if y == -1 && x == signed(1u128 << (bits - 1), bits) {
                        return Err("a signed division that overflows");
                    }
                    (if *op == BinOp::SDiv { x / y } else { x % y }) as u128
                }
                BinOp::RotL | BinOp::RotR => {
                    let n = (b % u128::from(bits)) as u32;
                    if n == 0 {
                        a
                    } else if *op == BinOp::RotL {
                        (a << n) | (a >> (bits - n))
                    } else {
                        (a >> n) | (a << (bits - n))
                    }
                }
                _ => return Err("not an integer operation this checker folds"),
            } & m;
            Ok((ty.clone(), int_constant(ty, bits, raw)))
        }
        Inst::UnOp { op, ty, operand: v } => {
            let (bits, _) = int_shape(ty, pointer_bits).ok_or("not an integer operation")?;
            if bits > 64 {
                return Err("wider than 64 bits");
            }
            let a = int_of(*v, bits)?;
            let raw = match op {
                UnOp::Neg => 0u128.wrapping_sub(a),
                UnOp::Not => !a,
                _ => return Err("not an integer operation this checker folds"),
            } & mask(bits);
            Ok((ty.clone(), int_constant(ty, bits, raw)))
        }
        Inst::ICmp { op, ty, lhs, rhs } => {
            if *ty == Ty::Bool {
                let (a, b) = (u128::from(bool_of(*lhs)?), u128::from(bool_of(*rhs)?));
                return Ok((Ty::Bool, Constant::Bool(compare(*op, a, b, 1))));
            }
            let (bits, _) = int_shape(ty, pointer_bits).ok_or("not an integer compare")?;
            if bits > 64 {
                return Err("wider than 64 bits");
            }
            let (a, b) = (int_of(*lhs, bits)?, int_of(*rhs, bits)?);
            Ok((Ty::Bool, Constant::Bool(compare(*op, a, b, bits))))
        }
        Inst::Cast {
            op,
            src_ty,
            dst_ty,
            operand: v,
        } => {
            let (dst_bits, _) = int_shape(dst_ty, pointer_bits).ok_or("not an integer cast")?;
            if dst_bits > 64 {
                return Err("wider than 64 bits");
            }
            let (src_bits, raw) = match (src_ty, lookup(*v)) {
                (Ty::Bool, Some(Operand::Bool(b))) => (1, u128::from(b)),
                (_, Some(Operand::Int { bits, raw })) => {
                    let (declared, _) =
                        int_shape(src_ty, pointer_bits).ok_or("not an integer cast")?;
                    if declared != bits {
                        return Err("the operand has another width");
                    }
                    (bits, raw)
                }
                _ => return Err("the operand is not a constant of the cast's source"),
            };
            let raw = match op {
                CastOp::ZExt if dst_bits >= src_bits => raw,
                CastOp::SExt if dst_bits >= src_bits => {
                    (signed(raw, src_bits) as u128) & mask(dst_bits)
                }
                CastOp::Trunc if dst_bits <= src_bits && *src_ty != Ty::Bool => {
                    raw & mask(dst_bits)
                }
                CastOp::Bitcast if dst_bits == src_bits && *src_ty != Ty::Bool => raw,
                _ => return Err("not a cast this checker folds"),
            };
            Ok((dst_ty.clone(), int_constant(dst_ty, dst_bits, raw)))
        }
        _ => Err("not a form this checker folds"),
    }
}

/// `op` on the `bits`-wide raw values `a` and `b`.
fn compare(op: ICmpOp, a: u128, b: u128, bits: u32) -> bool {
    let (x, y) = (signed(a, bits), signed(b, bits));
    match op {
        ICmpOp::Eq => a == b,
        ICmpOp::Ne => a != b,
        ICmpOp::Ult => a < b,
        ICmpOp::Ule => a <= b,
        ICmpOp::Ugt => a > b,
        ICmpOp::Uge => a >= b,
        ICmpOp::Slt => x < y,
        ICmpOp::Sle => x <= y,
        ICmpOp::Sgt => x > y,
        ICmpOp::Sge => x >= y,
    }
}

pub(super) fn rebuild_const_fold(
    pointer_bits: u32,
    source: &Function,
    witness: &ConstFoldWitness,
) -> Result<(Function, WitnessVerdict), MidTvError> {
    let mut cur = source.clone();
    // Where each single-result instruction is; a fold replaces it in place,
    // so the positions hold for the whole check.
    let mut at: HashMap<ValueId, (usize, usize)> = HashMap::new();
    let mut defined: HashSet<ValueId> = HashSet::new();
    for (bi, block) in cur.blocks.iter().enumerate() {
        defined.extend(block.params.iter().map(|(v, _)| *v));
        for (ni, node) in block.body.iter().enumerate() {
            for result in &node.results {
                if !defined.insert(*result) {
                    at.remove(result);
                    continue;
                }
                if node.results.len() == 1 {
                    at.insert(*result, (bi, ni));
                }
            }
        }
    }
    for fold in &witness.folds {
        let Some(&(bi, ni)) = at.get(&fold.value) else {
            return Err(refuse(
                fold.value,
                "not the single result of one instruction",
            ));
        };
        let inst = &cur.blocks[bi].body[ni].inst;
        // The bridge's `bool` constant spelled as the integer 0 or 1 is
        // respelled (module docs).
        if let Inst::Const {
            ty: Ty::Bool,
            value: Constant::Int(k @ (0 | 1)),
        } = inst
        {
            if fold.constant != Constant::Bool(*k == 1) {
                return Err(refuse(fold.value, "not the bool the integer spells"));
            }
            cur.blocks[bi].body[ni].inst = Inst::Const {
                ty: Ty::Bool,
                value: fold.constant.clone(),
            };
            continue;
        }
        // An integer constant spelled outside its type's range is respelled
        // in range: the same bits at the type's width (module docs).
        if let Inst::Const {
            ty,
            value: Constant::Int(k),
        } = inst
        {
            let canonical = int_shape(ty, pointer_bits)
                .filter(|(bits, _)| *bits <= 64)
                .map(|(bits, _)| int_constant(ty, bits, (*k as u128) & mask(bits)));
            match canonical {
                Some(c) if c != Constant::Int(*k) && c == fold.constant => {
                    let ty = ty.clone();
                    cur.blocks[bi].body[ni].inst = Inst::Const { ty, value: c };
                    continue;
                }
                _ => {
                    return Err(refuse(
                        fold.value,
                        "not an integer constant spelled out of range",
                    ));
                }
            }
        }
        if matches!(inst, Inst::Const { .. }) {
            return Err(refuse(fold.value, "already a constant"));
        }
        let lookup = |v: ValueId| -> Option<Operand> {
            let &(b, n) = at.get(&v)?;
            operand(pointer_bits, &cur.blocks[b].body[n].inst)
        };
        let (ty, constant) =
            evaluate(&lookup, pointer_bits, inst).map_err(|why| refuse(fold.value, why))?;
        if constant != fold.constant {
            return Err(refuse(
                fold.value,
                format!("evaluates to {constant:?}, not {:?}", fold.constant),
            ));
        }
        cur.blocks[bi].body[ni].inst = Inst::Const {
            ty,
            value: constant,
        };
    }
    Ok((
        cur,
        WitnessVerdict {
            exact: witness.folds.len(),
            refinements: 0,
        },
    ))
}

// ---------------------------------------------------------------------------
// Algebraic simplification
// ---------------------------------------------------------------------------

/// The identities of [`SimplifyWitness`] (module docs of the checker).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SimplifyRule {
    /// `x op e` (or `e op x` for a commutative `op`) with `e` the identity
    /// element of `op` on the right: `add`/`or`/`xor` 0, `sub` 0, a shift by
    /// 0, a rotate by a multiple of the width, `mul` 1, `and` all ones,
    /// unsigned or signed division by 1. The value becomes `copy x`.
    Identity,
    /// `and (zext a), m` (either order) with `m` all ones over `a`'s width:
    /// becomes `copy` of the `zext`.
    MaskedExtension,
    /// `trunc (zext a)` or `trunc (sext a)` back to `a`'s type: `copy a`.
    TruncExtension,
    /// `bitcast (bitcast x)` back to `x`'s type: `copy x`.
    BitcastRoundTrip,
    /// `trunc (or|xor|add x, (shl y, k))` to a width at most `k`: the high
    /// part contributes no bit, so it becomes `trunc x`.
    TruncLowPart,
    /// `lshr (or x, (shl y, k)), k` (either order of the `or`) with `x` below
    /// `2^k` (a `zext` from at most `k` bits, an `and` with a constant below
    /// `2^k`, or such a constant) and `y` a `zext` from at most `width - k`
    /// bits: becomes `copy y`.
    HighPart,
    /// `rotl x, c` (`0 < c < width`) whose every use in the function is an
    /// `and` of its type with a constant mask below `2^c`: the masked bits
    /// of the rotate are `x`'s top `c` bits, so it becomes `lshr x, k` with
    /// `k` a FRESH value, `const <type> (width - c)`, inserted just before
    /// it (the witness's `operand`). Every use reads the same bits; the
    /// value itself differs only in bits no use reads.
    MaskedRotate,
    /// `copy T x` with `x` an integer of another type `S` of the same width
    /// (the rustc bridge's sign-reinterpreting copy, which trust-ir's
    /// validator reports as `OperandTypeMismatch` and the wasm32 lane and
    /// the differential's view read as moving the bits): becomes
    /// `bitcast S x to T`; with `x` a thin pointer of another pointer type
    /// `S` than the thin pointer `T` (the bridge's copy of a `*const` as a
    /// `*mut`, which the lane and the view read as the same address):
    /// `ptrtoptr S x to T`. The witness's `operand` is `x`.
    ReinterpretCopy,
    /// `sub a, b` at the pointer width where `a` is, through
    /// address-preserving casts (`copy`, `ptrtoptr`, `ptrtoint` to and
    /// `inttoptr` from the pointer width, `bitcast` between integers of
    /// that width: each the identity on an address, in the reference
    /// interpreter and on wasm), `add p, x` (either order) at the pointer
    /// width, and `p` and `b` are, through the same casts, one value:
    /// `(r + x) - r` is `x`, so it becomes `copy x` (`x` of the result's
    /// type), the witness's `operand` being `x`. The rustc bridge spells a
    /// slice's length as the difference of its end and start addresses.
    PointerDifference,
}

impl SimplifyRule {
    /// Stable name for evidence.
    pub const fn as_str(self) -> &'static str {
        match self {
            SimplifyRule::Identity => "identity",
            SimplifyRule::MaskedExtension => "masked_extension",
            SimplifyRule::TruncExtension => "trunc_extension",
            SimplifyRule::BitcastRoundTrip => "bitcast_round_trip",
            SimplifyRule::TruncLowPart => "trunc_low_part",
            SimplifyRule::HighPart => "high_part",
            SimplifyRule::MaskedRotate => "masked_rotate",
            SimplifyRule::ReinterpretCopy => "reinterpret_copy",
            SimplifyRule::PointerDifference => "pointer_difference",
        }
    }
}

/// One simplification of the instruction defining `value` by `rule`;
/// `operand` is the value it copies, for [`SimplifyRule::TruncLowPart`]
/// the new operand of the `trunc`, for [`SimplifyRule::MaskedRotate`]
/// the fresh value of the shift amount, and for
/// [`SimplifyRule::ReinterpretCopy`] the operand of the `bitcast`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Simplify {
    pub value: ValueId,
    pub rule: SimplifyRule,
    pub operand: ValueId,
}

/// Algebraic simplification's claim, applied in order.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct SimplifyWitness {
    pub rewrites: Vec<Simplify>,
}

/// The current function's single-result definitions and types during a
/// sequential check.
struct Current<'a> {
    func: &'a Function,
    at: &'a HashMap<ValueId, (usize, usize)>,
    params: &'a HashMap<ValueId, Ty>,
    pointer_bits: u32,
}

impl Current<'_> {
    fn inst(&self, v: ValueId) -> Option<&Inst> {
        let &(b, n) = self.at.get(&v)?;
        Some(&self.func.blocks[b].body[n].inst)
    }

    /// `v` through `copy`s of its own type.
    fn root(&self, mut v: ValueId) -> ValueId {
        for _ in 0..64 {
            match self.inst(v) {
                Some(Inst::Copy { ty, operand }) if self.ty(*operand).as_ref() == Some(ty) => {
                    v = *operand;
                }
                _ => break,
            }
        }
        v
    }

    fn ty(&self, v: ValueId) -> Option<Ty> {
        if let Some(t) = self.params.get(&v) {
            return Some(t.clone());
        }
        match self.inst(v)? {
            Inst::Copy { ty, .. }
            | Inst::Load { ty, .. }
            | Inst::Const { ty, .. }
            | Inst::Select { ty, .. }
            | Inst::BinOp { ty, .. }
            | Inst::UnOp { ty, .. } => Some(ty.clone()),
            Inst::Cast { dst_ty, .. } => Some(dst_ty.clone()),
            Inst::ICmp { .. } | Inst::FCmp { .. } => Some(Ty::Bool),
            _ => None,
        }
    }

    fn bits(&self, ty: &Ty) -> Option<u32> {
        int_shape(ty, self.pointer_bits).map(|(b, _)| b)
    }

    /// The constant `v` holds at `bits`, through copies.
    fn constant(&self, v: ValueId, bits: u32) -> Option<u128> {
        match self.inst(self.root(v))? {
            Inst::Const {
                ty,
                value: Constant::Int(k),
            } if self.bits(ty) == Some(bits) => Some((*k as u128) & mask(bits)),
            _ => None,
        }
    }

    /// `v` through the address-preserving casts of
    /// [`SimplifyRule::PointerDifference`].
    fn address(&self, mut v: ValueId) -> ValueId {
        let pointer_int = |ty: &Ty| self.bits(ty) == Some(self.pointer_bits);
        for _ in 0..64 {
            match self.inst(v) {
                Some(Inst::Copy { operand, .. })
                | Some(Inst::Cast {
                    op: CastOp::PtrToPtr,
                    operand,
                    ..
                }) => v = *operand,
                Some(Inst::Cast {
                    op: CastOp::PtrToInt,
                    dst_ty,
                    operand,
                    ..
                }) if pointer_int(dst_ty) => v = *operand,
                Some(Inst::Cast {
                    op: CastOp::IntToPtr,
                    src_ty,
                    operand,
                    ..
                }) if pointer_int(src_ty) => v = *operand,
                Some(Inst::Cast {
                    op: CastOp::Bitcast,
                    src_ty,
                    dst_ty,
                    operand,
                }) if pointer_int(src_ty) && pointer_int(dst_ty) => v = *operand,
                _ => return v,
            }
        }
        v
    }

    /// `(source bits, operand)` when `v` is (through copies) a `zext`.
    fn zext(&self, v: ValueId) -> Option<(u32, ValueId)> {
        match self.inst(self.root(v))? {
            Inst::Cast {
                op: CastOp::ZExt,
                src_ty,
                operand,
                ..
            } => Some((self.bits(src_ty)?, *operand)),
            _ => None,
        }
    }

    /// Whether `v` is below `2^k` at `bits` (module docs of the rule).
    fn below(&self, v: ValueId, k: u32, bits: u32) -> bool {
        if let Some((from, _)) = self.zext(v) {
            return from <= k;
        }
        if let Some(c) = self.constant(v, bits) {
            return k >= 128 || c < (1u128 << k);
        }
        match self.inst(self.root(v)) {
            Some(Inst::BinOp {
                op: BinOp::And,
                lhs,
                rhs,
                ..
            }) => [*lhs, *rhs].iter().any(|m| {
                self.constant(*m, bits)
                    .is_some_and(|c| k >= 128 || c < (1u128 << k))
            }),
            _ => false,
        }
    }
}

/// What the rewrite of `inst` (defining a value of type `ty`) by `rule` with
/// `operand` is, or why it does not hold.
fn simplified(
    cur: &Current<'_>,
    inst: &Inst,
    rule: SimplifyRule,
    operand: ValueId,
) -> Result<Inst, &'static str> {
    let root = |v: ValueId| cur.root(v);
    let copy = |ty: &Ty, v: ValueId| -> Result<Inst, &'static str> {
        if cur.ty(v).as_ref() != Some(ty) {
            return Err("the copied value does not have the result's type");
        }
        Ok(Inst::Copy {
            ty: ty.clone(),
            operand: v,
        })
    };
    match (rule, inst) {
        (
            SimplifyRule::PointerDifference,
            Inst::BinOp {
                op: BinOp::Sub,
                ty,
                lhs,
                rhs,
            },
        ) => {
            if cur.bits(ty) != Some(cur.pointer_bits) {
                return Err("not a subtraction at the pointer width");
            }
            let base = cur.address(*rhs);
            let Some(Inst::BinOp {
                op: BinOp::Add,
                ty: add_ty,
                lhs: p,
                rhs: x,
            }) = cur.inst(cur.address(*lhs))
            else {
                return Err("the minuend is not an addition behind address casts");
            };
            if cur.bits(add_ty) != Some(cur.pointer_bits) {
                return Err("the addition is not at the pointer width");
            }
            let kept = if cur.address(*p) == base {
                *x
            } else if cur.address(*x) == base {
                *p
            } else {
                return Err("no addend is the subtrahend's address");
            };
            if kept != operand {
                return Err("the operand is not the other addend");
            }
            copy(ty, operand)
        }
        (SimplifyRule::ReinterpretCopy, Inst::Copy { ty, operand: x }) => {
            if *x != operand {
                return Err("the operand is not the copied value");
            }
            let from = cur.ty(*x).ok_or("the copied value's type is unknown")?;
            if &from == ty {
                return Err("the copy does not change the type");
            }
            let thin = |t: &Ty| {
                matches!(
                    t,
                    Ty::Ptr | Ty::PtrConst(_) | Ty::PtrMut(_) | Ty::Ref(_) | Ty::RefMut(_)
                )
            };
            if thin(&from) && thin(ty) {
                return Ok(Inst::Cast {
                    op: CastOp::PtrToPtr,
                    src_ty: from,
                    dst_ty: ty.clone(),
                    operand: *x,
                });
            }
            match (cur.bits(&from), cur.bits(ty)) {
                (Some(a), Some(b)) if a == b => Ok(Inst::Cast {
                    op: CastOp::Bitcast,
                    src_ty: from,
                    dst_ty: ty.clone(),
                    operand: *x,
                }),
                _ => Err("not two integer types of one width, nor two thin pointer types"),
            }
        }
        (SimplifyRule::Identity, Inst::BinOp { op, ty, lhs, rhs }) => {
            let bits = cur.bits(ty).ok_or("not an integer operation")?;
            let all = mask(bits);
            let right = |v: ValueId| cur.constant(v, bits);
            let holds = |keep: ValueId, other: ValueId, commuted: bool| {
                let Some(c) = right(other) else {
                    return false;
                };
                keep == operand
                    && match op {
                        BinOp::Add | BinOp::Or | BinOp::Xor => c == 0,
                        BinOp::Mul => c == 1,
                        BinOp::And => c == all,
                        BinOp::Sub | BinOp::Shl | BinOp::LShr | BinOp::AShr => !commuted && c == 0,
                        // A rotate's amount is reduced modulo the width.
                        BinOp::RotL | BinOp::RotR => !commuted && c % u128::from(bits) == 0,
                        BinOp::UDiv | BinOp::SDiv => !commuted && c == 1,
                        _ => false,
                    }
            };
            if holds(*lhs, *rhs, false) || holds(*rhs, *lhs, true) {
                copy(ty, operand)
            } else {
                Err("no operand is the identity of the operation")
            }
        }
        (
            SimplifyRule::MaskedExtension,
            Inst::BinOp {
                op: BinOp::And,
                ty,
                lhs,
                rhs,
            },
        ) => {
            let bits = cur.bits(ty).ok_or("not an integer operation")?;
            let fits = |x: ValueId, m: ValueId| {
                x == operand
                    && cur.zext(x).is_some_and(|(from, _)| {
                        cur.constant(m, bits)
                            .is_some_and(|c| c & mask(from) == mask(from))
                    })
            };
            if fits(*lhs, *rhs) || fits(*rhs, *lhs) {
                copy(ty, operand)
            } else {
                Err("not a mask over an extension's bits")
            }
        }
        (
            SimplifyRule::TruncExtension,
            Inst::Cast {
                op: CastOp::Trunc,
                dst_ty,
                operand: x,
                ..
            },
        ) => match cur.inst(root(*x)) {
            Some(Inst::Cast {
                op: CastOp::ZExt | CastOp::SExt,
                src_ty,
                operand: a,
                ..
            }) if src_ty == dst_ty && *a == operand => copy(dst_ty, operand),
            _ => Err("not the truncation of an extension back to its source"),
        },
        (
            SimplifyRule::BitcastRoundTrip,
            Inst::Cast {
                op: CastOp::Bitcast,
                dst_ty,
                operand: x,
                ..
            },
        ) => match cur.inst(root(*x)) {
            Some(Inst::Cast {
                op: CastOp::Bitcast,
                operand: a,
                ..
            }) if *a == operand && cur.ty(operand).as_ref() == Some(dst_ty) => {
                copy(dst_ty, operand)
            }
            _ => Err("not a bitcast round trip"),
        },
        (
            SimplifyRule::TruncLowPart,
            Inst::Cast {
                op: CastOp::Trunc,
                src_ty,
                dst_ty,
                operand: x,
            },
        ) => {
            let (from, to) = (
                cur.bits(src_ty).ok_or("not an integer truncation")?,
                cur.bits(dst_ty).ok_or("not an integer truncation")?,
            );
            let Some(Inst::BinOp { op, ty, lhs, rhs }) = cur.inst(root(*x)) else {
                return Err("the truncated value is not an or, xor or add");
            };
            if !matches!(op, BinOp::Or | BinOp::Xor | BinOp::Add) || ty != src_ty || to > from {
                return Err("the truncated value is not an or, xor or add of its type");
            }
            let high = |v: ValueId| match cur.inst(root(v)) {
                Some(Inst::BinOp {
                    op: BinOp::Shl,
                    ty: t,
                    rhs: amount,
                    ..
                }) if t == src_ty => cur
                    .constant(*amount, from)
                    .is_some_and(|k| k >= u128::from(to) && k < u128::from(from)),
                _ => false,
            };
            let keep = if high(*rhs) && *lhs == operand {
                *lhs
            } else if high(*lhs) && *rhs == operand {
                *rhs
            } else {
                return Err("neither part is shifted past the truncated width");
            };
            if cur.ty(keep).as_ref() != Some(src_ty) {
                return Err("the kept part does not have the truncated type");
            }
            Ok(Inst::Cast {
                op: CastOp::Trunc,
                src_ty: src_ty.clone(),
                dst_ty: dst_ty.clone(),
                operand: keep,
            })
        }
        (
            SimplifyRule::HighPart,
            Inst::BinOp {
                op: BinOp::LShr,
                ty,
                lhs,
                rhs,
            },
        ) => {
            let bits = cur.bits(ty).ok_or("not an integer shift")?;
            let k = cur
                .constant(*rhs, bits)
                .ok_or("the shift is not by a constant")?;
            if k == 0 || k >= u128::from(bits) {
                return Err("the shift is not inside the width");
            }
            let k = k as u32;
            let Some(Inst::BinOp {
                op: BinOp::Or,
                ty: t,
                lhs: a,
                rhs: b,
            }) = cur.inst(root(*lhs))
            else {
                return Err("the shifted value is not an or");
            };
            if t != ty {
                return Err("the or has another type");
            }
            let shifted = |v: ValueId| match cur.inst(root(v)) {
                Some(Inst::BinOp {
                    op: BinOp::Shl,
                    ty: t,
                    lhs: y,
                    rhs: amount,
                }) if t == ty && cur.constant(*amount, bits) == Some(u128::from(k)) => Some(*y),
                _ => None,
            };
            let (low, y) = match (shifted(*a), shifted(*b)) {
                (_, Some(y)) => (*a, y),
                (Some(y), None) => (*b, y),
                _ => return Err("no part of the or is shifted by the amount"),
            };
            if y != operand {
                return Err("the high part is not the claimed value");
            }
            let fits_high = cur.zext(y).is_some_and(|(from, _)| from <= bits - k);
            if !cur.below(low, k, bits) || !fits_high {
                return Err("the parts may overlap");
            }
            copy(ty, y)
        }
        _ => Err("the instruction is not the rule's form"),
    }
}

/// [`SimplifyRule::MaskedRotate`] on the current function: the constant
/// instruction defining the fresh shift amount and the shift that replaces
/// the rotate, or why the rule does not hold.
fn masked_rotate(
    func: &Function,
    at: &HashMap<ValueId, (usize, usize)>,
    params: &HashMap<ValueId, Ty>,
    pointer_bits: u32,
    rewrite: &Simplify,
) -> Result<(Inst, Inst), &'static str> {
    let cur = Current {
        func,
        at,
        params,
        pointer_bits,
    };
    let Some(Inst::BinOp {
        op: BinOp::RotL,
        ty,
        lhs: x,
        rhs: amount,
    }) = cur.inst(rewrite.value)
    else {
        return Err("the value is not a rotate left");
    };
    let bits = cur.bits(ty).ok_or("not an integer rotate")?;
    let c = cur
        .constant(*amount, bits)
        .ok_or("the rotate is not by a constant")?;
    if c == 0 || c >= u128::from(bits) {
        return Err("the rotate amount is not inside the width");
    }
    let fresh = rewrite.operand;
    if at.contains_key(&fresh) || params.contains_key(&fresh) {
        return Err("the shift amount is not a fresh value");
    }
    let mut uses = 0usize;
    for node in func.blocks.iter().flat_map(|b| &b.body) {
        if node.results.contains(&fresh) || node.inst.uses_value(fresh) {
            return Err("the shift amount is not a fresh value");
        }
        if !node.inst.uses_value(rewrite.value) {
            continue;
        }
        let Inst::BinOp {
            op: BinOp::And,
            ty: t,
            lhs,
            rhs,
        } = &node.inst
        else {
            return Err("a use of the rotate is not an and");
        };
        let mask = match (*lhs == rewrite.value, *rhs == rewrite.value) {
            (true, false) => *rhs,
            (false, true) => *lhs,
            _ => return Err("an and uses the rotate twice"),
        };
        if t != ty {
            return Err("an and of the rotate has another type");
        }
        match cur.constant(mask, bits) {
            Some(m) if m < (1u128 << c) => uses += 1,
            _ => return Err("an and of the rotate keeps bits the shift does not compute"),
        }
    }
    if uses == 0 {
        return Err("the rotate has no use");
    }
    Ok((
        Inst::Const {
            ty: ty.clone(),
            value: Constant::Int((u128::from(bits) - c) as i128),
        },
        Inst::BinOp {
            op: BinOp::LShr,
            ty: ty.clone(),
            lhs: *x,
            rhs: fresh,
        },
    ))
}

pub(super) fn rebuild_simplify(
    pointer_bits: u32,
    source: &Function,
    witness: &SimplifyWitness,
) -> Result<(Function, WitnessVerdict), MidTvError> {
    let mut cur = source.clone();
    let mut at: HashMap<ValueId, (usize, usize)> = HashMap::new();
    let mut params: HashMap<ValueId, Ty> = HashMap::new();
    for (bi, block) in cur.blocks.iter().enumerate() {
        for (v, t) in &block.params {
            params.insert(*v, t.clone());
        }
        for (ni, node) in block.body.iter().enumerate() {
            if let [r] = node.results.as_slice() {
                at.insert(*r, (bi, ni));
            }
        }
    }
    for rewrite in &witness.rewrites {
        let bad = |why: String| MidTvError::NotSimplification {
            value: rewrite.value,
            why,
        };
        let Some(&(bi, ni)) = at.get(&rewrite.value) else {
            return Err(bad("not the single result of an instruction".to_string()));
        };
        if rewrite.rule == SimplifyRule::MaskedRotate {
            let (constant, shift) = masked_rotate(&cur, &at, &params, pointer_bits, rewrite)
                .map_err(|why| bad(format!("masked_rotate: {why}")))?;
            for slot in at.values_mut() {
                if slot.0 == bi && slot.1 >= ni {
                    slot.1 += 1;
                }
            }
            at.insert(rewrite.operand, (bi, ni));
            let block = &mut cur.blocks[bi];
            block.body[ni].inst = shift;
            block
                .body
                .insert(ni, InstrNode::new(constant).with_results([rewrite.operand]));
            continue;
        }
        let inst = {
            let view = Current {
                func: &cur,
                at: &at,
                params: &params,
                pointer_bits,
            };
            simplified(
                &view,
                &cur.blocks[bi].body[ni].inst,
                rewrite.rule,
                rewrite.operand,
            )
            .map_err(|why| bad(format!("{}: {why}", rewrite.rule.as_str())))?
        };
        cur.blocks[bi].body[ni].inst = inst;
    }
    Ok((
        cur,
        WitnessVerdict {
            exact: 0,
            refinements: witness.rewrites.len(),
        },
    ))
}

#[cfg(test)]
#[path = "trust_ir_mid_tv_fold_tests.rs"]
mod tests;

// ---------------------------------------------------------------------------
// Respelling the bridge's ill-typed operands
// ---------------------------------------------------------------------------

/// What one respelling does (module documentation of
/// [`rebuild_respell`]).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RespellRule {
    /// An `icmp` at a typed thin pointer compares its operands cast to
    /// `ptr` by the fresh `ptrtoptr`s `lhs` and `rhs`.
    PointerCompare { lhs: ValueId, rhs: ValueId },
    /// A `memcopy` or `memset` whose byte count is an unsigned integer of
    /// pointer width other than `usize` takes the fresh `count`, its `zext`
    /// to `usize` (a `const usize` of it when it is a constant).
    ByteCount { count: ValueId },
}

/// One respelling of the instruction at `(block, index)` of the SOURCE.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Respell {
    pub block: BlockId,
    pub index: usize,
    pub rule: RespellRule,
}

/// The operand respelling's claim.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct RespellWitness {
    pub rewrites: Vec<Respell>,
}

/// The operand respelling ([`RespellWitness`]): two forms the rustc bridge
/// emits that trust-ir's validator reports, which an inlined copy carries
/// into its caller (the wasm32 lane emits a mid-end output only when it adds
/// no finding), each respelled at the type the validator asks for with the
/// meaning the lane and the differential's view give it. Each claimed
/// rewrite names an instruction of the SOURCE by position, once:
///
/// * [`RespellRule::PointerCompare`]: an `icmp` whose declared type is a
///   thin pointer other than `ptr` (`&T`, `&mut T`, `*const T`, `*mut T`)
///   with both operands of that type (this module's typing), which the
///   validator reports (`ICmpRequiresIntegerOrPtr`: a slice iterator's
///   position against its end). It becomes `lhs = ptrtoptr <ty> a to ptr`,
///   `rhs = ptrtoptr <ty> b to ptr` (fresh, in that order, just before it)
///   and the same comparison at `ptr` of `lhs` and `rhs`. Exact: the casts
///   keep the address, and the comparison reads the addresses (the view
///   compares every pointer comparison's addresses, the lane the address
///   words).
/// * [`RespellRule::ByteCount`]: a `memcopy` or `memset` whose byte count
///   is of an unsigned integer type of the module's pointer width other
///   than `usize` (the bridge's `u32` on wasm32), which the validator
///   reports (`OperandTypeMismatch`: the count is a `usize`). The fresh
///   `count`, just before it, is `const usize k` when the count is the
///   integer constant `k`, and `zext <ty> n to usize` otherwise; the
///   instruction takes it. Exact: the value is the same number (both
///   unsigned of one width), which is what the instruction reads.
pub(super) fn rebuild_respell(
    pointer_bits: u32,
    source: &Function,
    witness: &RespellWitness,
) -> Result<(Function, WitnessVerdict), MidTvError> {
    let types = value_types(source);
    let mut defs: HashMap<ValueId, &Inst> = HashMap::new();
    let mut taken: HashSet<ValueId> = HashSet::new();
    for block in &source.blocks {
        taken.extend(block.params.iter().map(|(v, _)| *v));
        for node in &block.body {
            taken.extend(node.results.iter().copied());
            node.inst.visit_value_operands(|v| {
                taken.insert(v);
            });
            if let [r] = node.results.as_slice() {
                defs.insert(*r, &node.inst);
            }
        }
    }
    if let Some(names) = &source.value_names {
        taken.extend(names.iter().map(|(v, _)| *v));
    }
    let positions = super::block_positions(source);
    if witness.rewrites.is_empty() {
        return Err(MidTvError::NotSimplification {
            value: ValueId::new(0),
            why: "respell: the witness claims no rewrite".to_string(),
        });
    }
    let typed_pointer = |t: &Ty| {
        matches!(
            t,
            Ty::PtrConst(_) | Ty::PtrMut(_) | Ty::Ref(_) | Ty::RefMut(_)
        )
    };
    let mut replaced: HashMap<(usize, usize), Vec<InstrNode>> = HashMap::new();
    for rewrite in &witness.rewrites {
        let bad = |why: &str| MidTvError::NotSimplification {
            value: ValueId::new(0),
            why: format!("respell at {}[{}]: {why}", rewrite.block, rewrite.index),
        };
        let bi = *positions
            .get(&rewrite.block)
            .ok_or_else(|| bad("no such block"))?;
        let node = source.blocks[bi]
            .body
            .get(rewrite.index)
            .ok_or_else(|| bad("no such instruction"))?;
        if replaced.contains_key(&(bi, rewrite.index)) {
            return Err(bad("rewritten twice"));
        }
        let mut fresh = |v: ValueId| {
            if taken.insert(v) {
                Ok(v)
            } else {
                Err(bad("a named value is not fresh"))
            }
        };
        let nodes = match (&rewrite.rule, &node.inst) {
            (RespellRule::PointerCompare { lhs: a, rhs: b }, Inst::ICmp { op, ty, lhs, rhs }) => {
                if !typed_pointer(ty) {
                    return Err(bad("not a comparison at a typed thin pointer"));
                }
                if types.get(lhs) != Some(ty) || types.get(rhs) != Some(ty) {
                    return Err(bad("an operand is not of the comparison's type"));
                }
                let (a, b) = (fresh(*a)?, fresh(*b)?);
                let cast = |operand: ValueId, result: ValueId| {
                    let mut n = node.clone();
                    n.inst = Inst::Cast {
                        op: CastOp::PtrToPtr,
                        src_ty: ty.clone(),
                        dst_ty: Ty::Ptr,
                        operand,
                    };
                    n.results = vec![result];
                    n
                };
                let mut compare = node.clone();
                compare.inst = Inst::ICmp {
                    op: *op,
                    ty: Ty::Ptr,
                    lhs: a,
                    rhs: b,
                };
                vec![cast(*lhs, a), cast(*rhs, b), compare]
            }
            (
                RespellRule::ByteCount { count },
                Inst::MemCopy { bytes, .. } | Inst::MemSet { bytes, .. },
            ) => {
                let ty = types
                    .get(bytes)
                    .ok_or_else(|| bad("the count's type is unknown"))?;
                if *ty == Ty::Usize || int_shape(ty, pointer_bits) != Some((pointer_bits, false)) {
                    return Err(bad(
                        "the count is not an unsigned integer of pointer width other than usize",
                    ));
                }
                let count = fresh(*count)?;
                let mut def = node.clone();
                def.inst = match defs.get(bytes) {
                    Some(Inst::Const {
                        value: Constant::Int(k),
                        ..
                    }) if *k >= 0 && *k >> pointer_bits == 0 => Inst::Const {
                        ty: Ty::Usize,
                        value: Constant::Int(*k),
                    },
                    _ => Inst::Cast {
                        op: CastOp::ZExt,
                        src_ty: ty.clone(),
                        dst_ty: Ty::Usize,
                        operand: *bytes,
                    },
                };
                def.results = vec![count];
                let mut op = node.clone();
                match &mut op.inst {
                    Inst::MemCopy { bytes, .. } | Inst::MemSet { bytes, .. } => *bytes = count,
                    _ => unreachable!("matched above"),
                }
                vec![def, op]
            }
            _ => return Err(bad("the instruction is not of the rule's form")),
        };
        replaced.insert((bi, rewrite.index), nodes);
    }
    let mut expected = source.clone();
    for (bi, block) in expected.blocks.iter_mut().enumerate() {
        let body = std::mem::take(&mut block.body);
        block.body = body
            .into_iter()
            .enumerate()
            .flat_map(|(ni, n)| replaced.remove(&(bi, ni)).unwrap_or_else(|| vec![n]))
            .collect();
    }
    Ok((
        expected,
        WitnessVerdict {
            exact: witness.rewrites.len(),
            refinements: 0,
        },
    ))
}
