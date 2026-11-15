// trust-cg-irmid/passes/const_fold.rs - constant folding
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Constant folding: an integer or `bool` instruction whose operands are all
//! constants becomes the constant it computes, in place under the same
//! result, when it raises nothing on them (no division by zero, no
//! overflowing signed division, no shift by the width or more). The bridge
//! spells offsets and counts as constant expressions (`mul (bitcast 6), 8`),
//! the inliner binds callees' parameters to the callers' constants, and the
//! loop unroller turns an induction variable into a constant per copy;
//! folding them lets the branch, range and memory passes see the values,
//! and the wasm lane emit one immediate instead of the expression.
//!
//! The forms (integers of at most 64 bits, every operand of the width its
//! instruction declares): `add`, `sub`, `mul`, bitwise operations, rotates,
//! shifts below the width, divisions and remainders that are defined, `neg`,
//! `not`, `icmp` (also of `bool` constants), the boolean connectives over
//! `bool` constants, and `zext`, `sext`, `trunc` and same-width `bitcast`
//! between integers. The result is spelled canonically: `const bool`, or the
//! integer in its type's own range; a `bool` constant the bridge spells as
//! the integer 0 or 1, and an integer constant the bridge spells outside its
//! type's range (`const i8 254`, the niche of an `Option<Ordering>`; the
//! interpreter and the wasm32 lane read its bits at the type's width), are
//! respelled so (trust-ir's validator reports both spellings, and the
//! inliner's copy of a callee would carry the finding into its caller). The pass folds to a fixed point, each
//! fold in an order whose operands are folded first; the witness lists the
//! folds in that order and the checker
//! (`trust_cg_verify::trust_ir_mid_tv`, `trust_ir_mid_tv_fold.rs`) evaluates
//! every one again with its own code.

use std::collections::HashMap;

use trust_cg_verify::trust_ir_mid_tv::{ConstFold, ConstFoldWitness, PassWitness};
use trust_ir::{BinOp, CastOp, Constant, Function, ICmpOp, Inst, Ty, UnOp, ValueId};

use super::{MidPass, PassContext, int_shape};

pub(crate) struct ConstFoldPass;

/// The evidence name of constant folding.
pub(crate) const CONST_FOLD_NAME: &str = "const_fold";

impl MidPass for ConstFoldPass {
    fn name(&self) -> &'static str {
        CONST_FOLD_NAME
    }

    fn run(&self, cx: &PassContext<'_>, func: &Function) -> Option<(Function, PassWitness)> {
        let mut out = func.clone();
        let mut known: HashMap<ValueId, Known> = HashMap::new();
        for node in out.blocks.iter().flat_map(|b| &b.body) {
            if let ([result], Some(k)) = (
                node.results.as_slice(),
                constant(&node.inst, cx.pointer_bits),
            ) {
                known.insert(*result, k);
            }
        }
        let mut folds = Vec::new();
        // The bridge's `bool` constants spelled as integers.
        for node in out.blocks.iter_mut().flat_map(|b| &mut b.body) {
            if let (
                Inst::Const {
                    ty: Ty::Bool,
                    value: Constant::Int(k @ (0 | 1)),
                },
                [result],
            ) = (&node.inst, node.results.as_slice())
            {
                let constant = Constant::Bool(*k == 1);
                folds.push(ConstFold {
                    value: *result,
                    constant: constant.clone(),
                });
                known.insert(*result, Known::Bool(*k == 1));
                node.inst = Inst::Const {
                    ty: Ty::Bool,
                    value: constant,
                };
            }
        }
        // An integer constant spelled outside its type's range (the bridge's
        // `const i8 254` of a niche): the value is its bits at the type's
        // width (the interpreter and the wasm32 lane both wrap it), spelled
        // in range (trust-ir's validator reports `ConstTypeMismatch`, and a
        // splice would carry the finding into a caller).
        for node in out.blocks.iter_mut().flat_map(|b| &mut b.body) {
            if let (
                Inst::Const {
                    ty,
                    value: Constant::Int(k),
                },
                [result],
            ) = (&node.inst, node.results.as_slice())
                && let Some((bits, _)) = int_shape(ty, cx.pointer_bits)
                && bits <= 64
            {
                let canonical = spell(ty, bits, (*k as u128) & ones(bits));
                if canonical == Constant::Int(*k) {
                    continue;
                }
                folds.push(ConstFold {
                    value: *result,
                    constant: canonical.clone(),
                });
                let ty = ty.clone();
                node.inst = Inst::Const {
                    ty,
                    value: canonical,
                };
            }
        }
        loop {
            let mut grew = false;
            for block in &mut out.blocks {
                for node in &mut block.body {
                    let [result] = node.results.as_slice() else {
                        continue;
                    };
                    if known.contains_key(result) || matches!(node.inst, Inst::Const { .. }) {
                        continue;
                    }
                    let Some((ty, value)) = fold(&node.inst, &known, cx.pointer_bits) else {
                        continue;
                    };
                    let k = constant(
                        &Inst::Const {
                            ty: ty.clone(),
                            value: value.clone(),
                        },
                        cx.pointer_bits,
                    );
                    folds.push(ConstFold {
                        value: *result,
                        constant: value.clone(),
                    });
                    if let Some(k) = k {
                        known.insert(*result, k);
                    }
                    node.inst = Inst::Const { ty, value };
                    grew = true;
                }
            }
            if !grew {
                break;
            }
        }
        if folds.is_empty() {
            return None;
        }
        Some((out, PassWitness::ConstFold(ConstFoldWitness { folds })))
    }
}

/// A constant's bits at its width, or a `bool`.
#[derive(Debug, Clone, Copy)]
enum Known {
    Int { bits: u32, raw: u128 },
    Bool(bool),
}

fn ones(bits: u32) -> u128 {
    if bits >= 128 {
        u128::MAX
    } else {
        (1u128 << bits) - 1
    }
}

/// `raw` at `bits` as a signed value.
fn as_signed(raw: u128, bits: u32) -> i128 {
    let shift = 128 - bits;
    ((raw << shift) as i128) >> shift
}

/// What a `const` instruction holds, for the forms this pass reads.
fn constant(inst: &Inst, pointer_bits: u32) -> Option<Known> {
    match inst {
        Inst::Const {
            ty,
            value: Constant::Int(k),
        } => {
            let (bits, _) = int_shape(ty, pointer_bits)?;
            (bits <= 64).then(|| Known::Int {
                bits,
                raw: (*k as u128) & ones(bits),
            })
        }
        Inst::Const {
            ty: Ty::Bool,
            value: Constant::Bool(b),
        } => Some(Known::Bool(*b)),
        _ => None,
    }
}

/// `raw` at the integer type `ty`, spelled in the type's range.
fn spell(ty: &Ty, bits: u32, raw: u128) -> Constant {
    if ty.is_signed() {
        Constant::Int(as_signed(raw, bits))
    } else {
        Constant::Int(raw as i128)
    }
}

/// The fold of `inst` on the constants in `known`.
fn fold(inst: &Inst, known: &HashMap<ValueId, Known>, pointer_bits: u32) -> Option<(Ty, Constant)> {
    let int = |v: &ValueId, bits: u32| match known.get(v)? {
        Known::Int { bits: b, raw } if *b == bits => Some(*raw),
        _ => None,
    };
    let boolean = |v: &ValueId| match known.get(v)? {
        Known::Bool(b) => Some(*b),
        Known::Int { .. } => None,
    };
    match inst {
        Inst::BinOp { op, ty, lhs, rhs } if *ty == Ty::Bool => {
            let (a, b) = (boolean(lhs)?, boolean(rhs)?);
            let r = match op {
                BinOp::And | BinOp::BAnd => a && b,
                BinOp::Or | BinOp::BOr => a || b,
                BinOp::Xor | BinOp::BXor => a != b,
                _ => return None,
            };
            Some((Ty::Bool, Constant::Bool(r)))
        }
        Inst::BinOp { op, ty, lhs, rhs } => {
            let (bits, _) = int_shape(ty, pointer_bits)?;
            if bits > 64 {
                return None;
            }
            let (a, b) = (int(lhs, bits)?, int(rhs, bits)?);
            let r = match op {
                BinOp::Add => a.wrapping_add(b),
                BinOp::Sub => a.wrapping_sub(b),
                BinOp::Mul => a.wrapping_mul(b),
                BinOp::And => a & b,
                BinOp::Or => a | b,
                BinOp::Xor => a ^ b,
                BinOp::Shl if b < u128::from(bits) => a << b,
                BinOp::LShr if b < u128::from(bits) => a >> b,
                BinOp::AShr if b < u128::from(bits) => (as_signed(a, bits) >> b) as u128,
                BinOp::UDiv if b != 0 => a / b,
                BinOp::URem if b != 0 => a % b,
                BinOp::SDiv | BinOp::SRem => {
                    let (x, y) = (as_signed(a, bits), as_signed(b, bits));
                    let min = -(1i128 << (bits - 1));
                    if y == 0 || (y == -1 && x == min) {
                        return None;
                    }
                    if *op == BinOp::SDiv {
                        (x / y) as u128
                    } else {
                        (x % y) as u128
                    }
                }
                BinOp::RotL | BinOp::RotR => {
                    let n = u32::try_from(b % u128::from(bits)).ok()?;
                    let left = if *op == BinOp::RotL {
                        n
                    } else {
                        (bits - n) % bits
                    };
                    if left == 0 {
                        a
                    } else {
                        (a << left) | (a >> (bits - left))
                    }
                }
                _ => return None,
            } & ones(bits);
            Some((ty.clone(), spell(ty, bits, r)))
        }
        Inst::UnOp { op, ty, operand } => {
            let (bits, _) = int_shape(ty, pointer_bits)?;
            if bits > 64 {
                return None;
            }
            let a = int(operand, bits)?;
            let r = match op {
                UnOp::Neg => a.wrapping_neg(),
                UnOp::Not => !a,
                _ => return None,
            } & ones(bits);
            Some((ty.clone(), spell(ty, bits, r)))
        }
        Inst::ICmp { op, ty, lhs, rhs } => {
            let (a, b, bits) = if *ty == Ty::Bool {
                (u128::from(boolean(lhs)?), u128::from(boolean(rhs)?), 1)
            } else {
                let (bits, _) = int_shape(ty, pointer_bits)?;
                if bits > 64 {
                    return None;
                }
                (int(lhs, bits)?, int(rhs, bits)?, bits)
            };
            let (x, y) = (as_signed(a, bits), as_signed(b, bits));
            let r = match op {
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
            };
            Some((Ty::Bool, Constant::Bool(r)))
        }
        Inst::Cast {
            op,
            src_ty,
            dst_ty,
            operand,
        } => {
            let (to, _) = int_shape(dst_ty, pointer_bits)?;
            if to > 64 {
                return None;
            }
            let (from, raw) = if *src_ty == Ty::Bool {
                (1, u128::from(boolean(operand)?))
            } else {
                let (from, _) = int_shape(src_ty, pointer_bits)?;
                (from, int(operand, from)?)
            };
            let r = match op {
                CastOp::ZExt if to >= from => raw,
                CastOp::SExt if to >= from => (as_signed(raw, from) as u128) & ones(to),
                CastOp::Trunc if to <= from && from > 1 => raw & ones(to),
                CastOp::Bitcast if to == from && from > 1 => raw,
                _ => return None,
            };
            Some((dst_ty.clone(), spell(dst_ty, to, r)))
        }
        _ => None,
    }
}
