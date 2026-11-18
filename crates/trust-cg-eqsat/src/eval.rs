// crates/trust-cg-eqsat/src/eval.rs - section 3 semantics of graph operators on residues
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Section 3 of `docs/eqsat-tier-e.md`: every graph operator as a function on
//! residues `r < 2^w`. The engine uses it for `eval` in rule right-hand sides
//! and for side conditions; it never decides what a function computes (the
//! skeleton and the checker do). The tests compare it with trust-ir's
//! reference interpreter at boundary values.
//!
//! Every function here is total on residues of a width in `1..=128`; an
//! operand that is not a residue of its width, or an operator not admitted at
//! its type, yields `None` (a typed refusal, never a panic).

use crate::vocab::{BinOpCode, CastOpCode, CmpPred, GraphWidths, OpDesc, UnOpCode, mask};

/// The two's-complement reading of a `width`-bit residue.
#[must_use]
pub fn signed(r: u128, width: u32) -> i128 {
    if width == 0 || width > 128 {
        return 0;
    }
    let shift = 128 - width;
    ((r << shift) as i128) >> shift
}

fn residue_ok(r: u128, width: u32) -> bool {
    (1..=128).contains(&width) && r & !mask(width) == 0
}

/// `op` at width `width` on residues `a`, `b`.
#[must_use]
pub fn bin(op: BinOpCode, width: u32, a: u128, b: u128) -> Option<u128> {
    if !residue_ok(a, width) || !residue_ok(b, width) {
        return None;
    }
    let m = mask(width);
    Some(match op {
        BinOpCode::Add => a.wrapping_add(b) & m,
        BinOpCode::Sub => a.wrapping_sub(b) & m,
        BinOpCode::Mul => a.wrapping_mul(b) & m,
        BinOpCode::And | BinOpCode::BAnd => a & b,
        BinOpCode::Or | BinOpCode::BOr => a | b,
        BinOpCode::Xor | BinOpCode::BXor => a ^ b,
        BinOpCode::RotL => rotate_left(a, b % u128::from(width), width),
        BinOpCode::RotR => {
            let amount = b % u128::from(width);
            if amount == 0 {
                a
            } else {
                rotate_left(a, u128::from(width) - amount, width)
            }
        }
    })
}

fn rotate_left(a: u128, amount: u128, width: u32) -> u128 {
    // amount < width <= 128, so both shifts are in range.
    let amount = amount as u32;
    if amount == 0 {
        return a;
    }
    let m = mask(width);
    ((a << amount) | (a >> (width - amount))) & m
}

/// `op` at width `width` on residue `a`.
#[must_use]
pub fn un(op: UnOpCode, width: u32, a: u128) -> Option<u128> {
    if !residue_ok(a, width) {
        return None;
    }
    let m = mask(width);
    let pad = 128 - width;
    Some(match op {
        UnOpCode::Neg => 0u128.wrapping_sub(a) & m,
        UnOpCode::Not => a ^ m,
        UnOpCode::CtPop => u128::from(a.count_ones()),
        UnOpCode::CtLz => u128::from(a.leading_zeros() - pad),
        UnOpCode::CtTz => {
            if a == 0 {
                u128::from(width)
            } else {
                u128::from(a.trailing_zeros())
            }
        }
        UnOpCode::BSwap => {
            if width % 8 != 0 {
                return None;
            }
            a.swap_bytes() >> pad
        }
        UnOpCode::BitReverse => a.reverse_bits() >> pad,
    })
}

/// `pred` at operand width `width`: `Some(true)` or `Some(false)`.
#[must_use]
pub fn cmp(pred: CmpPred, width: u32, a: u128, b: u128) -> Option<bool> {
    if !residue_ok(a, width) || !residue_ok(b, width) {
        return None;
    }
    let (sa, sb) = (signed(a, width), signed(b, width));
    Some(match pred {
        CmpPred::Eq => a == b,
        CmpPred::Ne => a != b,
        CmpPred::Ult => a < b,
        CmpPred::Ule => a <= b,
        CmpPred::Ugt => a > b,
        CmpPred::Uge => a >= b,
        CmpPred::Slt => sa < sb,
        CmpPred::Sle => sa <= sb,
        CmpPred::Sgt => sa > sb,
        CmpPred::Sge => sa >= sb,
    })
}

/// `op` from width `src` to width `dst` (section 3: `trunc`/`zext` reduce the
/// residue modulo `2^dst`; `sext` sign-extends from `src` bits first), for
/// every pair of widths.
#[must_use]
pub fn cast(op: CastOpCode, src: u32, dst: u32, r: u128) -> Option<u128> {
    if !residue_ok(r, src) || !(1..=128).contains(&dst) {
        return None;
    }
    let m = mask(dst);
    Some(match op {
        CastOpCode::Trunc | CastOpCode::ZExt => r & m,
        CastOpCode::SExt => (signed(r, src) as u128) & m,
    })
}

/// `select c a b`: `a` when `c` is 1, else `b` (`c` must be a 1-bit residue).
#[must_use]
pub fn select(c: u128, a: u128, b: u128) -> Option<u128> {
    match c {
        1 => Some(a),
        0 => Some(b),
        _ => None,
    }
}

/// Evaluate the term operator `desc` on residues `args`, with the module's
/// widths. `None` when an operand is not a residue of its type, the arity is
/// wrong, a type is not a graph type here, the operator is not admitted, or
/// the operator is a pinned reduction (uninterpreted).
#[must_use]
pub fn op(widths: GraphWidths, desc: OpDesc, args: &[u128]) -> Option<u128> {
    if !desc.admitted() || args.len() != desc.arity() {
        return None;
    }
    match desc {
        OpDesc::Bin(op, ty) => bin(op, widths.width(ty)?, *args.first()?, *args.get(1)?),
        OpDesc::Un(op, ty) => un(op, widths.width(ty)?, *args.first()?),
        OpDesc::Cmp(pred, ty) => {
            cmp(pred, widths.width(ty)?, *args.first()?, *args.get(1)?).map(u128::from)
        }
        OpDesc::Cast(op, src, dst) => {
            cast(op, widths.width(src)?, widths.width(dst)?, *args.first()?)
        }
        OpDesc::Select(ty) => {
            let width = widths.width(ty)?;
            let (c, a, b) = (*args.first()?, *args.get(1)?, *args.get(2)?);
            if !residue_ok(a, width) || !residue_ok(b, width) {
                return None;
            }
            select(c, a, b)
        }
        // A pinned reduction is uninterpreted here: it is a function of its
        // operand, and nothing in this crate evaluates it.
        OpDesc::Pinned(..) => None,
    }
}

/// The residue a rule-file integer `INT` (sign and magnitude, already range
/// checked) denotes at width `width`: `INT mod 2^w`.
#[must_use]
pub fn int_residue(negative: bool, magnitude: u128, width: u32) -> u128 {
    let m = mask(width);
    if negative {
        0u128.wrapping_sub(magnitude) & m
    } else {
        magnitude & m
    }
}

/// The residue a trust-ir `Constant::Int(v)` denotes at width `width`:
/// `v mod 2^w`.
#[must_use]
pub fn i128_residue(value: i128, width: u32) -> u128 {
    (value as u128) & mask(width)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn signed_reading() {
        assert_eq!(signed(0xff, 8), -1);
        assert_eq!(signed(0x7f, 8), 127);
        assert_eq!(signed(0x80, 8), -128);
        assert_eq!(signed(u128::MAX, 128), -1);
        assert_eq!(signed(1, 1), -1);
    }

    #[test]
    fn residues_of_integers() {
        assert_eq!(int_residue(true, 1, 8), 255);
        assert_eq!(int_residue(true, 1, 128), u128::MAX);
        assert_eq!(int_residue(false, 256, 8), 0);
        assert_eq!(int_residue(true, 1u128 << 127, 128), 1u128 << 127);
        assert_eq!(i128_residue(-1, 16), 0xffff);
    }

    #[test]
    fn rotations_reduce_the_amount() {
        assert_eq!(bin(BinOpCode::RotL, 8, 0x81, 1), Some(0x03));
        assert_eq!(bin(BinOpCode::RotL, 8, 0x81, 9), Some(0x03));
        assert_eq!(bin(BinOpCode::RotR, 8, 0x81, 1), Some(0xc0));
        assert_eq!(bin(BinOpCode::RotR, 8, 0x81, 8), Some(0x81));
        assert_eq!(bin(BinOpCode::RotL, 128, 1u128 << 127, 1), Some(1));
    }

    #[test]
    fn non_residues_are_refused() {
        assert_eq!(bin(BinOpCode::Add, 8, 256, 0), None);
        assert_eq!(un(UnOpCode::BSwap, 1, 1), None);
        assert_eq!(select(2, 0, 0), None);
    }
}
