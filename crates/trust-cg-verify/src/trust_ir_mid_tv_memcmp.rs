// trust-cg-verify/trust_ir_mid_tv_memcmp.rs - a short memcmp as loads and compares
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The checker of the comparison-call rewrite ([`MemCmpWitness`]), deriving
//! its premises from the SOURCE function and the module with this module's
//! own code.
//!
//! The rustc bridge lowers `<[u8]>::eq` and `Ord::cmp` of byte slices (and
//! so `&str` equality) to a call of the C library's `memcmp`, as rustc does
//! for LLVM, which expands a call with a small constant length into loads
//! and compares; the wasm32 lane links `compiler_builtins`' byte loop.
//!
//! **The premise** (OD-141's, extended to comparisons; stated, not proved):
//! a call of the module's DECLARATION (no body) named `memcmp` or `bcmp`
//! whose signature is the C prototype (three parameters, not variadic, one
//! result; the first two pointer-like, the third an integer of the target's
//! pointer width (the bridge declares `i32`), the result a 32-bit integer)
//! performs the C library's operation: it reads the first `n` bytes of the
//! two objects, which C requires to exist (C11 7.24.4.1, 7.1.4: an object of
//! fewer bytes is undefined behaviour), compares them as `unsigned char`s,
//! and returns 0 when they are equal; otherwise `memcmp` returns a value of
//! the sign of the first differing byte's difference (`compiler_builtins`
//! returns that difference) and `bcmp` a nonzero value. The differential's
//! view gives such a declaration the body that loads and compares every one
//! of the `n` byte pairs (an uninitialised byte is undefined behaviour, as
//! a comparison inspects it) and returns the first difference
//! (`compare_body`).
//!
//! **Each claimed rewrite** names a call by its single result `r` and the
//! fresh values of its expansion, in order. The count operand must be
//! defined by an integer constant `k` with `0 <= k <= MAX_MEMCMP_BYTES` (its
//! bits read unsigned). The call becomes, in place:
//!
//! * `k == 0`: `r = const <ret> 0` (no fresh value): the bytes compared are
//!   none, and equal;
//! * `k == 1`: `la = load u8, a; lb = load u8, b; za = zext u8 la to <ret>;
//!   zb = zext u8 lb to <ret>; r = sub <ret> za, zb`: the difference of the
//!   two bytes as unsigned chars, the view's value exactly (and of the sign
//!   C asks of `memcmp`, nonzero exactly when they differ for `bcmp`);
//! * `k >= 2`: only when every use of `r` is a zero test (`icmp eq` or `icmp
//!   ne` of `r` with a value defined by an integer constant 0, either
//!   operand): the bytes as chunks of 8, 4, 2 and 1 bytes in that order
//!   (greedily, from offset 0), each `o = const usize off; pa = gep u8, a,
//!   [o]; la = load T, pa; pb = gep u8, b, [o]; lb = load T, pb; x = xor T
//!   la, lb` (`T` the unsigned integer of the chunk's width, `align 1`, not
//!   volatile), widened to `W` (`u64` when a chunk is 8 bytes, else `u32`)
//!   by `w = zext T x to W` unless `T` is `W`, and joined by `acc = or W
//!   acc, w` from the second chunk on; then `z = const W 0; ne = icmp ne W
//!   acc, z; r = zext bool ne to <ret>`. `acc` is zero exactly when every
//!   byte pair is equal, so `r` is zero exactly when the bytes are, and each
//!   zero test reads the same `bool` as from the call's value.
//!
//! Exact on every use under the premise: the expansion reads exactly the
//! `n` bytes of each object the call does (as integers whose inspection
//! faults on an uninitialised byte where the view's comparison does), and
//! `r`'s uses see the same values (`k <= 1`) or the same zero tests (`k >=
//! 2`). Each load has alignment 1, which no access can violate. An
//! instruction of another form, a non-constant count, a count past the
//! bound, a use that reads `r` otherwise (its sign) when `k >= 2`, a
//! function of the module DEFINED under the name and a name that is not
//! fresh are refused.

use std::collections::{HashMap, HashSet};

use trust_ir::{BinOp, CastOp, Constant, Function, ICmpOp, Inst, InstrNode, Module, Ty, ValueId};

use super::{Defs, MidTvError, WitnessVerdict, int_shape, used_values};

/// The most bytes a comparison call is expanded for (the checker's bound;
/// the pass's policy may be smaller).
pub const MAX_MEMCMP_BYTES: u64 = 16;

/// One comparison call rewritten: the call defines `value`; `fresh` are the
/// expansion's new values in order (module documentation).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MemCmp {
    pub value: ValueId,
    pub fresh: Vec<ValueId>,
}

/// The comparison-call rewrite's claim.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct MemCmpWitness {
    pub rewrites: Vec<MemCmp>,
}

fn pointer_like(ty: &Ty) -> bool {
    matches!(
        ty,
        Ty::Ptr | Ty::PtrConst(_) | Ty::PtrMut(_) | Ty::Ref(_) | Ty::RefMut(_)
    )
}

/// Whether `callee` is a declaration of `memcmp` or `bcmp` with the C
/// prototype (module documentation, the premise); its result type then.
pub(super) fn library_compare(module: &Module, pointer_bits: u32, callee: &Function) -> Option<Ty> {
    if !callee.is_declaration() || !matches!(callee.name.as_str(), "memcmp" | "bcmp") {
        return None;
    }
    let sig = module.func_type(callee.ty)?;
    let ([a, b, count], [ret]) = (sig.params.as_slice(), sig.returns.as_slice()) else {
        return None;
    };
    let count_ok = int_shape(count, pointer_bits).is_some_and(|(bits, _)| bits == pointer_bits);
    let ret_ok = int_shape(ret, pointer_bits).is_some_and(|(bits, _)| bits == 32);
    (!sig.is_vararg && pointer_like(a) && pointer_like(b) && count_ok && ret_ok)
        .then(|| ret.clone())
}

/// The chunks of `n` bytes: `(offset, width in bytes)`, 8, 4, 2 and 1 bytes
/// greedily from offset 0.
pub(super) fn chunks(n: u64) -> Vec<(u64, u64)> {
    let mut out = Vec::new();
    let mut offset = 0u64;
    for width in [8u64, 4, 2, 1] {
        while n - offset >= width {
            out.push((offset, width));
            offset += width;
        }
    }
    out
}

fn chunk_ty(width: u64) -> Ty {
    match width {
        8 => Ty::U64,
        4 => Ty::U32,
        2 => Ty::U16,
        _ => Ty::U8,
    }
}

/// The expansion of a comparison of `k` bytes of `a` and `b` defining
/// `result` of type `ret`, minting the fresh values from `fresh` in order;
/// `None` when `fresh` does not hold exactly the values it needs.
fn expansion(
    template: &InstrNode,
    k: u64,
    a: ValueId,
    b: ValueId,
    result: ValueId,
    ret: &Ty,
    fresh: &[ValueId],
) -> Option<Vec<InstrNode>> {
    let mut next = fresh.iter().copied();
    let mut out: Vec<InstrNode> = Vec::new();
    let mut emit = |inst: Inst, results: Vec<ValueId>| {
        let mut node = template.clone();
        node.inst = inst;
        node.results = results;
        out.push(node);
    };
    let load = |ty: Ty, ptr: ValueId| Inst::Load {
        ty,
        ptr,
        volatile: false,
        align: Some(1),
    };
    match k {
        0 => emit(
            Inst::Const {
                ty: ret.clone(),
                value: Constant::Int(0),
            },
            vec![result],
        ),
        1 => {
            let (la, lb, za, zb) = (next.next()?, next.next()?, next.next()?, next.next()?);
            emit(load(Ty::U8, a), vec![la]);
            emit(load(Ty::U8, b), vec![lb]);
            for (byte, wide) in [(la, za), (lb, zb)] {
                emit(
                    Inst::Cast {
                        op: CastOp::ZExt,
                        src_ty: Ty::U8,
                        dst_ty: ret.clone(),
                        operand: byte,
                    },
                    vec![wide],
                );
            }
            emit(
                Inst::BinOp {
                    op: BinOp::Sub,
                    ty: ret.clone(),
                    lhs: za,
                    rhs: zb,
                },
                vec![result],
            );
        }
        _ => {
            let parts = chunks(k);
            let wide = if parts.iter().any(|&(_, w)| w == 8) {
                Ty::U64
            } else {
                Ty::U32
            };
            let mut acc: Option<ValueId> = None;
            for (offset, width) in parts {
                let ty = chunk_ty(width);
                let (o, pa, la, pb, lb, x) = (
                    next.next()?,
                    next.next()?,
                    next.next()?,
                    next.next()?,
                    next.next()?,
                    next.next()?,
                );
                emit(
                    Inst::Const {
                        ty: Ty::Usize,
                        value: Constant::Int(i128::from(offset)),
                    },
                    vec![o],
                );
                for (base, at, loaded) in [(a, pa, la), (b, pb, lb)] {
                    emit(
                        Inst::GEP {
                            pointee_ty: Ty::U8,
                            base,
                            indices: vec![o],
                            inbounds: false,
                        },
                        vec![at],
                    );
                    emit(load(ty.clone(), at), vec![loaded]);
                }
                emit(
                    Inst::BinOp {
                        op: BinOp::Xor,
                        ty: ty.clone(),
                        lhs: la,
                        rhs: lb,
                    },
                    vec![x],
                );
                let widened = if ty == wide {
                    x
                } else {
                    let w = next.next()?;
                    emit(
                        Inst::Cast {
                            op: CastOp::ZExt,
                            src_ty: ty,
                            dst_ty: wide.clone(),
                            operand: x,
                        },
                        vec![w],
                    );
                    w
                };
                acc = Some(match acc {
                    None => widened,
                    Some(prev) => {
                        let joined = next.next()?;
                        emit(
                            Inst::BinOp {
                                op: BinOp::Or,
                                ty: wide.clone(),
                                lhs: prev,
                                rhs: widened,
                            },
                            vec![joined],
                        );
                        joined
                    }
                });
            }
            let (z, ne) = (next.next()?, next.next()?);
            emit(
                Inst::Const {
                    ty: wide.clone(),
                    value: Constant::Int(0),
                },
                vec![z],
            );
            emit(
                Inst::ICmp {
                    op: ICmpOp::Ne,
                    ty: wide,
                    lhs: acc?,
                    rhs: z,
                },
                vec![ne],
            );
            emit(
                Inst::Cast {
                    op: CastOp::ZExt,
                    src_ty: Ty::Bool,
                    dst_ty: ret.clone(),
                    operand: ne,
                },
                vec![result],
            );
        }
    }
    next.next().is_none().then_some(out)
}

pub(super) fn rebuild_mem_cmp(
    module: &Module,
    pointer_bits: u32,
    source: &Function,
    witness: &MemCmpWitness,
) -> Result<(Function, WitnessVerdict), MidTvError> {
    let defs = Defs::of(source);
    let mut at: HashMap<ValueId, (usize, usize)> = HashMap::new();
    let mut taken: HashSet<ValueId> = used_values(source);
    // The uses of each value, by the instruction using it.
    let mut uses: HashMap<ValueId, Vec<&Inst>> = HashMap::new();
    for (bi, block) in source.blocks.iter().enumerate() {
        taken.extend(block.params.iter().map(|(v, _)| *v));
        for (ni, node) in block.body.iter().enumerate() {
            taken.extend(node.results.iter().copied());
            if let [r] = node.results.as_slice() {
                at.insert(*r, (bi, ni));
            }
            node.inst.visit_value_operands(|v| {
                uses.entry(v).or_default().push(&node.inst);
            });
        }
    }
    if let Some(names) = &source.value_names {
        taken.extend(names.iter().map(|(v, _)| *v));
    }
    let zero = |v: ValueId| {
        matches!(
            defs.inst(v),
            Some(Inst::Const {
                value: Constant::Int(0),
                ty,
            }) if ty.is_integer()
        )
    };
    let mut replaced: HashMap<(usize, usize), Vec<InstrNode>> = HashMap::new();
    for rewrite in &witness.rewrites {
        let bad = |why: &str| MidTvError::NotMemCmp {
            value: rewrite.value,
            why: why.to_string(),
        };
        let &(bi, ni) = at
            .get(&rewrite.value)
            .ok_or_else(|| bad("not the single result of an instruction"))?;
        if replaced.contains_key(&(bi, ni)) {
            return Err(bad("rewritten twice"));
        }
        let node = &source.blocks[bi].body[ni];
        let Inst::Call { callee, args } = &node.inst else {
            return Err(bad("not a direct call"));
        };
        let callee_fn = module
            .function_by_id(*callee)
            .ok_or_else(|| bad("the callee is not a function of the module"))?;
        let ret = library_compare(module, pointer_bits, callee_fn).ok_or_else(|| {
            bad("the callee is not a declaration of memcmp or bcmp with the C prototype")
        })?;
        let [a, b, count] = args.as_slice() else {
            return Err(bad("the call does not pass three arguments"));
        };
        let sig = module
            .func_type(callee_fn.ty)
            .ok_or_else(|| bad("the callee has no signature"))?;
        for (arg, want) in [a, b].into_iter().zip(&sig.params) {
            if !defs.value_type(*arg).as_ref().is_some_and(pointer_like) || !pointer_like(want) {
                return Err(bad("a compared operand is not a pointer"));
            }
        }
        let k = match defs.inst(*count) {
            Some(Inst::Const {
                ty,
                value: Constant::Int(k),
            }) if ty == &sig.params[2] => {
                let bits = (*k as u128) & ((1u128 << pointer_bits) - 1);
                u64::try_from(bits).ok()
            }
            _ => None,
        }
        .ok_or_else(|| bad("the count is not an integer constant of its type"))?;
        if k > MAX_MEMCMP_BYTES {
            return Err(bad("the count is past the bound"));
        }
        if k >= 2 {
            let zero_tests = uses.get(&rewrite.value).into_iter().flatten().all(|inst| {
                matches!(
                    inst,
                    Inst::ICmp { op: ICmpOp::Eq | ICmpOp::Ne, lhs, rhs, .. }
                        if (*lhs == rewrite.value && *rhs != rewrite.value && zero(*rhs))
                            || (*rhs == rewrite.value && *lhs != rewrite.value && zero(*lhs))
                )
            });
            if !zero_tests {
                return Err(bad(
                    "a use reads the result other than by a zero test, and more than one byte is \
                     compared",
                ));
            }
        }
        for v in &rewrite.fresh {
            if !taken.insert(*v) {
                return Err(bad("a named value is not fresh"));
            }
        }
        let nodes = expansion(node, k, *a, *b, rewrite.value, &ret, &rewrite.fresh)
            .ok_or_else(|| bad("the fresh values are not the expansion's count"))?;
        replaced.insert((bi, ni), nodes);
    }
    if witness.rewrites.is_empty() {
        return Err(MidTvError::NotMemCmp {
            value: ValueId::new(0),
            why: "the witness claims no rewrite".to_string(),
        });
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

#[cfg(test)]
#[path = "trust_ir_mid_tv_memcmp_tests.rs"]
mod tests;
