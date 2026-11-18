// trust-cg-eqsat-check/src/semantics.rs - section 3 semantics of graph operators on residues
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The checker's own statement of docs/eqsat-tier-e.md section 3: every graph
//! operator as a function of residues in `[0, 2^w)`.
//!
//! Used for `(eval OP ...)` right-hand sides and for side conditions. It is
//! this crate's reading of the spec text, written without reference to the
//! engine; it claims agreement with section 3, not with the interpreter
//! directly (section 2.2 cites the interpreter evidence for that).

use crate::types::{BinK, CastK, Ctx, OpDesc, Pred, Sty, UnK, mask};

/// The signed (two's complement) reading of residue `r` at width `w`.
fn signed(r: u128, w: u32) -> i128 {
    if w >= 128 {
        return r as i128;
    }
    let sign = (r >> (w - 1)) & 1 == 1;
    if sign {
        (r | !mask(w)) as i128
    } else {
        r as i128
    }
}

fn rotate_left(a: u128, amount: u32, w: u32) -> u128 {
    let m = mask(w);
    let s = amount % w;
    if s == 0 {
        return a & m;
    }
    ((a << s) | (a >> (w - s))) & m
}

fn bswap(a: u128, w: u32) -> u128 {
    let bytes = w / 8;
    let mut out = 0u128;
    for i in 0..bytes {
        let byte = (a >> (8 * i)) & 0xff;
        out |= byte << (8 * (bytes - 1 - i));
    }
    out
}

fn bitreverse(a: u128, w: u32) -> u128 {
    let mut out = 0u128;
    for i in 0..w {
        if (a >> i) & 1 == 1 {
            out |= 1u128 << (w - 1 - i);
        }
    }
    out
}

/// Evaluates `desc` on residues `args` (each already `< 2^w` of its operand
/// type). `None` when a type has no established width, the arity is wrong,
/// an argument is out of range, or a width is not a whole number of bytes
/// for `bswap` (never the case for an admitted type).
pub(crate) fn eval(desc: OpDesc, args: &[u128], ctx: Ctx) -> Option<u128> {
    if args.len() != desc.arity() || !desc.admitted(ctx) {
        return None;
    }
    for (arg, ty) in args.iter().zip(desc.operand_tys()) {
        if *arg > mask(ctx.width(ty)?) {
            return None;
        }
    }
    match desc {
        OpDesc::Bin(k, t) => {
            let w = ctx.width(t)?;
            let m = mask(w);
            let (a, b) = (args[0], args[1]);
            Some(match k {
                BinK::Add => a.wrapping_add(b) & m,
                BinK::Sub => a.wrapping_sub(b) & m,
                BinK::Mul => a.wrapping_mul(b) & m,
                BinK::And | BinK::BAnd => a & b,
                BinK::Or | BinK::BOr => a | b,
                BinK::Xor | BinK::BXor => a ^ b,
                BinK::RotL => rotate_left(a, (b % u128::from(w)) as u32, w),
                BinK::RotR => {
                    let s = (b % u128::from(w)) as u32;
                    rotate_left(a, (w - s) % w, w)
                }
            })
        }
        OpDesc::Un(k, t) => {
            let w = ctx.width(t)?;
            let m = mask(w);
            let a = args[0];
            Some(match k {
                UnK::Neg => a.wrapping_neg() & m,
                UnK::Not => a ^ m,
                UnK::CtPop => u128::from(a.count_ones()),
                UnK::CtLz => {
                    if a == 0 {
                        u128::from(w)
                    } else {
                        u128::from(w - (128 - a.leading_zeros()))
                    }
                }
                UnK::CtTz => {
                    if a == 0 {
                        u128::from(w)
                    } else {
                        u128::from(a.trailing_zeros())
                    }
                }
                UnK::BSwap => {
                    if w % 8 != 0 {
                        return None;
                    }
                    bswap(a, w)
                }
                UnK::BitReverse => bitreverse(a, w),
            })
        }
        OpDesc::Cmp(p, t) => {
            let w = ctx.width(t)?;
            let (a, b) = (args[0], args[1]);
            let (sa, sb) = (signed(a, w), signed(b, w));
            let holds = match p {
                Pred::Eq => a == b,
                Pred::Ne => a != b,
                Pred::Ult => a < b,
                Pred::Ule => a <= b,
                Pred::Ugt => a > b,
                Pred::Uge => a >= b,
                Pred::Slt => sa < sb,
                Pred::Sle => sa <= sb,
                Pred::Sgt => sa > sb,
                Pred::Sge => sa >= sb,
            };
            Some(u128::from(holds))
        }
        OpDesc::Cast(k, s, d) => {
            let ws = ctx.width(s)?;
            let wd = ctx.width(d)?;
            let r = args[0];
            Some(match k {
                CastK::Trunc | CastK::ZExt => r & mask(wd),
                CastK::SExt => (signed(r, ws) as u128) & mask(wd),
            })
        }
        OpDesc::Select(_) => Some(if args[0] == 1 { args[1] } else { args[2] }),
        // A pinned reduction is uninterpreted: the checker never folds one.
        OpDesc::Pinned(..) => None,
    }
}

/// The residue of a constant of type `t` read as a section 3 value of
/// `Constant::Int(v)`: `v mod 2^w`.
pub(crate) fn int_residue(v: i128, w: u32) -> u128 {
    (v as u128) & mask(w)
}

/// Whether `Constant::Int(v)` lies in the range trust-ir admits for `t`
/// (the signed range for signed types, the unsigned range otherwise).
pub(crate) fn int_fits(v: i128, t: Sty, w: u32) -> bool {
    if t.is_bool() {
        return false;
    }
    if t.is_signed() {
        if w >= 128 {
            return true;
        }
        let half = 1i128 << (w - 1);
        (-half..half).contains(&v)
    } else {
        if v < 0 {
            return false;
        }
        w >= 128 || (v >> w) == 0
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const C64: Ctx = Ctx { pointer_bits: 64 };

    #[test]
    fn arithmetic_wraps() {
        assert_eq!(
            eval(OpDesc::Bin(BinK::Add, Sty::U8), &[250, 10], C64),
            Some(4)
        );
        assert_eq!(
            eval(OpDesc::Bin(BinK::Sub, Sty::I8), &[0, 1], C64),
            Some(255)
        );
        assert_eq!(
            eval(OpDesc::Bin(BinK::Mul, Sty::U128), &[u128::MAX, 2], C64),
            Some(u128::MAX - 1)
        );
        assert_eq!(
            eval(OpDesc::Un(UnK::Neg, Sty::U32), &[1], C64),
            Some(0xffff_ffff)
        );
        assert_eq!(
            eval(OpDesc::Un(UnK::Not, Sty::U8), &[0x0f], C64),
            Some(0xf0)
        );
    }

    #[test]
    fn bit_operators() {
        assert_eq!(eval(OpDesc::Un(UnK::CtLz, Sty::U32), &[0], C64), Some(32));
        assert_eq!(eval(OpDesc::Un(UnK::CtLz, Sty::U32), &[1], C64), Some(31));
        assert_eq!(eval(OpDesc::Un(UnK::CtTz, Sty::U16), &[0], C64), Some(16));
        assert_eq!(eval(OpDesc::Un(UnK::CtTz, Sty::U16), &[8], C64), Some(3));
        assert_eq!(eval(OpDesc::Un(UnK::CtPop, Sty::U8), &[0xff], C64), Some(8));
        assert_eq!(
            eval(OpDesc::Un(UnK::BSwap, Sty::U32), &[0x1122_3344], C64),
            Some(0x4433_2211)
        );
        assert_eq!(
            eval(OpDesc::Un(UnK::BitReverse, Sty::U8), &[1], C64),
            Some(0x80)
        );
        assert_eq!(
            eval(OpDesc::Bin(BinK::RotL, Sty::U8), &[0x81, 9], C64),
            Some(0x03)
        );
        assert_eq!(
            eval(OpDesc::Bin(BinK::RotR, Sty::U8), &[0x81, 1], C64),
            Some(0xc0)
        );
        assert_eq!(
            eval(OpDesc::Bin(BinK::RotR, Sty::U8), &[0x81, 8], C64),
            Some(0x81)
        );
    }

    #[test]
    fn comparisons_and_casts() {
        assert_eq!(
            eval(OpDesc::Cmp(Pred::Slt, Sty::I8), &[0xff, 0], C64),
            Some(1)
        );
        assert_eq!(
            eval(OpDesc::Cmp(Pred::Ult, Sty::I8), &[0xff, 0], C64),
            Some(0)
        );
        assert_eq!(
            eval(OpDesc::Cast(CastK::SExt, Sty::I8, Sty::I32), &[0x80], C64),
            Some(0xffff_ff80)
        );
        assert_eq!(
            eval(OpDesc::Cast(CastK::ZExt, Sty::I8, Sty::I32), &[0x80], C64),
            Some(0x80)
        );
        assert_eq!(
            eval(
                OpDesc::Cast(CastK::Trunc, Sty::U32, Sty::U8),
                &[0x1234],
                C64
            ),
            Some(0x34)
        );
        assert_eq!(eval(OpDesc::Select(Sty::U8), &[0, 1, 2], C64), Some(2));
    }

    #[test]
    fn refuses_unadmitted_or_out_of_range() {
        assert_eq!(eval(OpDesc::Bin(BinK::Add, Sty::Bool), &[0, 1], C64), None);
        assert_eq!(eval(OpDesc::Bin(BinK::Add, Sty::U8), &[256, 1], C64), None);
        let c16 = Ctx { pointer_bits: 16 };
        assert_eq!(eval(OpDesc::Bin(BinK::Add, Sty::Usize), &[1, 1], c16), None);
    }

    #[test]
    fn constant_ranges() {
        assert!(int_fits(-128, Sty::I8, 8));
        assert!(!int_fits(128, Sty::I8, 8));
        assert!(!int_fits(-1, Sty::U32, 32));
        assert_eq!(int_residue(-1, 8), 255);
    }
}
