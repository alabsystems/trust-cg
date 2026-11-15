// trust-cg-verify/trust_ir_mid_tv_memcall.rs - C memory library calls as bulk-memory instructions
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The checker of the memory-call rewrite ([`MemCallWitness`]), deriving its
//! premises from the SOURCE function and the module with this module's own
//! code.
//!
//! The rustc bridge lowers `ptr::copy` (and so `ptr::swap`),
//! `copy_nonoverlapping` with a length it does not expand and
//! `ptr::write_bytes` to calls of the C library's `memmove`, `memcpy` and
//! `memset`, exactly as rustc's LLVM backend emits `llvm.memmove`,
//! `llvm.memcpy` and `llvm.memset`. trust-ir has the same operations as
//! instructions: `memcopy overlap` (memmove: the ranges may overlap, the
//! copy behaves as if through a temporary), `memcopy` (memcpy: overlapping
//! ranges are undefined behaviour) and `memset` (the byte written to each of
//! the counted bytes). The wasm32 lane lowers those to `memory.copy` and
//! `memory.fill` under a guard that skips a zero count; its emission pass
//! expands a copy of a constant 1 to 32 bytes into loads and stores, and a
//! fill stays `memory.fill`. A call stays a call into `compiler_builtins`'
//! loop.
//!
//! **The premise** (the same one rustc and LLVM rely on, stated, not
//! proved): a call of the module's DECLARATION (a function without a body)
//! named `memmove`, `memcpy` or `memset` whose signature is the C prototype
//! (three parameters, not variadic, one result; the first parameter and the
//! result pointer-like, the second pointer-like for a copy and an integer of
//! 9 to 32 bits for `memset` (so that the fill's truncation to `u8` is a
//! narrowing `trunc`; the bridge declares a C `int`), the third an unsigned
//! integer of the target's pointer width: the bridge narrows `size_t` to
//! `u32` on wasm32)
//! performs the C library's operation and returns its first argument. A
//! function of the module DEFINED under one of these names (a program's own
//! `#[no_mangle] fn memmove`) is not admitted: its body is what runs.
//!
//! **Each claimed rewrite** names a call by its single result, which no
//! instruction may use (the bridge never reads the returned pointer), and
//! the fresh values the rewrite defines. A pointer argument may be of any
//! pointer-like type (the bridge passes `*mut T`; the address is the same),
//! the fill and the count must have their parameter's type. When the count
//! operand is defined by an integer constant `k` of the parameter's type,
//! the rewrite defines `count` as `const usize k` (the instructions take a
//! `usize` count). A copy's count may also be any other value `n` of the
//! parameter's type (a run-time count): `count` is then `n` as `usize`, a
//! `zext` of it (the parameter is an unsigned integer of pointer width, so
//! the value is the same number; trust-ir's validator types `usize` at no
//! fixed width and refuses a `bitcast` to it), or a `copy usize` when the
//! parameter is `usize` itself. A `memset`'s count must be a constant. A `memset`'s
//! fill operand is truncated to `u8` into `byte` (C converts the `int` to
//! `unsigned char`). The call becomes, in place:
//!
//! * `memmove(d, s, k)`: `count = const usize k; memcopy overlap d, s, count`;
//! * `memcpy(d, s, k)`: `count = const usize k; memcopy d, s, count`;
//! * `memmove(d, s, n)` / `memcpy(d, s, n)` with a run-time `n`: `count =
//!   zext n to usize` (or `copy usize n`) and the same instruction;
//! * `memset(d, c, k)`: `count = const usize k; byte = trunc c to u8;
//!   memset d, byte, count`.
//!
//! Exact under the premise: the instruction defines every behaviour the C
//! call defines, including the zero-count no-op, and its undefined
//! behaviour (a range outside a live allocation, overlap for `memcpy`) is
//! the call's. A copy is byte-granular and asserts no alignment, so an
//! unaligned operand is defined alike. No volatile form reaches this
//! rewrite: the bridge does not lower the volatile copy intrinsics to these
//! calls, and neither a call nor the instructions carry a volatile flag.

use std::collections::{HashMap, HashSet};

use trust_ir::{CastOp, Constant, Function, Inst, InstrNode, Module, Ty, ValueId};

use super::{Defs, MidTvError, WitnessVerdict, int_shape, used_values};

/// One memory library call rewritten as its instruction: the call is the
/// instruction defining `value`, `count` the fresh `usize` count (a `const
/// usize` of a constant count; for a copy with a run-time count, that count
/// as `usize`), and `byte` the fresh truncated fill operand of a `memset`
/// (`None` for a copy).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MemCall {
    pub value: ValueId,
    pub count: ValueId,
    pub byte: Option<ValueId>,
}

/// The memory-call rewrite's claim.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct MemCallWitness {
    pub rewrites: Vec<MemCall>,
}

/// Which C library operation a declaration is, re-derived from its name and
/// prototype (module docs, "The premise"), or `None`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Libcall {
    Move,
    Copy,
    Set,
}

fn pointer_like(ty: &Ty) -> bool {
    matches!(
        ty,
        Ty::Ptr | Ty::PtrConst(_) | Ty::PtrMut(_) | Ty::Ref(_) | Ty::RefMut(_)
    )
}

fn libcall(module: &Module, pointer_bits: u32, callee: &Function) -> Option<Libcall> {
    if !callee.is_declaration() {
        return None;
    }
    let kind = match callee.name.as_str() {
        "memmove" => Libcall::Move,
        "memcpy" => Libcall::Copy,
        "memset" => Libcall::Set,
        _ => return None,
    };
    let sig = module.func_type(callee.ty)?;
    let [dst, second, count] = sig.params.as_slice() else {
        return None;
    };
    let [ret] = sig.returns.as_slice() else {
        return None;
    };
    let second_ok = match kind {
        Libcall::Set => {
            int_shape(second, pointer_bits).is_some_and(|(bits, _)| (9..=32).contains(&bits))
        }
        Libcall::Move | Libcall::Copy => pointer_like(second),
    };
    let count_ok = int_shape(count, pointer_bits) == Some((pointer_bits, false));
    (!sig.is_vararg && pointer_like(dst) && pointer_like(ret) && second_ok && count_ok)
        .then_some(kind)
}

pub(super) fn rebuild_mem_call(
    module: &Module,
    pointer_bits: u32,
    source: &Function,
    witness: &MemCallWitness,
) -> Result<(Function, WitnessVerdict), MidTvError> {
    let defs = Defs::of(source);
    let used = used_values(source);
    let mut at: HashMap<ValueId, (usize, usize)> = HashMap::new();
    let mut taken: HashSet<ValueId> = used.clone();
    for (bi, block) in source.blocks.iter().enumerate() {
        taken.extend(block.params.iter().map(|(v, _)| *v));
        for (ni, node) in block.body.iter().enumerate() {
            taken.extend(node.results.iter().copied());
            if let [r] = node.results.as_slice() {
                at.insert(*r, (bi, ni));
            }
        }
    }
    if let Some(names) = &source.value_names {
        taken.extend(names.iter().map(|(v, _)| *v));
    }
    let mut replaced: HashMap<(usize, usize), Vec<InstrNode>> = HashMap::new();
    for rewrite in &witness.rewrites {
        let bad = |why: &str| MidTvError::NotMemCall {
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
        let kind = libcall(module, pointer_bits, callee_fn).ok_or_else(|| {
            bad("the callee is not a declaration of memmove, memcpy or memset with the C prototype")
        })?;
        let [dst, second, count] = args.as_slice() else {
            return Err(bad("the call does not pass three arguments"));
        };
        if used.contains(&rewrite.value) {
            return Err(bad("the returned pointer is used"));
        }
        let sig = module
            .func_type(callee_fn.ty)
            .ok_or_else(|| bad("the callee has no signature"))?;
        // A pointer argument is pointer-like (a pointer of another pointee
        // type is the same address; `memcopy` and `memset` take any
        // pointer-like operand); the fill and the count have their
        // parameter's type (the C operation reads them at the prototype's).
        for (arg, want) in args.iter().zip(&sig.params) {
            let have = defs.value_type(*arg);
            let ok = if pointer_like(want) {
                have.as_ref().is_some_and(pointer_like)
            } else {
                have.as_ref() == Some(want)
            };
            if !ok {
                return Err(bad("an argument does not have its parameter's type"));
            }
        }
        // The count: an integer constant of its parameter's type, or, for a
        // copy, any value of that type (its type was checked above).
        let k = match defs.inst(*count) {
            Some(Inst::Const {
                ty,
                value: Constant::Int(k),
            }) if ty == &sig.params[2] && *k >= 0 && *k >> pointer_bits == 0 => Some(*k),
            _ if kind != Libcall::Set => None,
            _ => {
                return Err(bad(
                    "a memset count that is not an integer constant of its type",
                ));
            }
        };
        if rewrite.byte.is_some() != (kind == Libcall::Set) {
            return Err(bad(
                "a fill byte is claimed for a copy, or missing for memset",
            ));
        }
        for v in std::iter::once(rewrite.count).chain(rewrite.byte) {
            if !taken.insert(v) {
                return Err(bad("a named value is not fresh"));
            }
        }
        let mut constant = node.clone();
        constant.inst = match k {
            Some(k) => Inst::Const {
                ty: Ty::Usize,
                value: Constant::Int(k),
            },
            None if sig.params[2] == Ty::Usize => Inst::Copy {
                ty: Ty::Usize,
                operand: *count,
            },
            None => Inst::Cast {
                op: CastOp::ZExt,
                src_ty: sig.params[2].clone(),
                dst_ty: Ty::Usize,
                operand: *count,
            },
        };
        constant.results = vec![rewrite.count];
        let mut out = vec![constant];
        let mut op = node.clone();
        op.results = Vec::new();
        match (kind, rewrite.byte) {
            (Libcall::Set, Some(byte)) => {
                let mut trunc = node.clone();
                trunc.inst = Inst::Cast {
                    op: CastOp::Trunc,
                    src_ty: sig.params[1].clone(),
                    dst_ty: Ty::U8,
                    operand: *second,
                };
                trunc.results = vec![byte];
                out.push(trunc);
                op.inst = Inst::MemSet {
                    dst: *dst,
                    byte,
                    bytes: rewrite.count,
                };
            }
            (Libcall::Move | Libcall::Copy, None) => {
                op.inst = Inst::MemCopy {
                    dst: *dst,
                    src: *second,
                    bytes: rewrite.count,
                    overlap: kind == Libcall::Move,
                };
            }
            _ => {
                return Err(bad(
                    "a fill byte is claimed for a copy, or missing for memset",
                ));
            }
        }
        out.push(op);
        replaced.insert((bi, ni), out);
    }
    let mut expected = source.clone();
    for (bi, block) in expected.blocks.iter_mut().enumerate() {
        let body = std::mem::take(&mut block.body);
        block.body = body
            .into_iter()
            .enumerate()
            .flat_map(|(ni, node)| replaced.remove(&(bi, ni)).unwrap_or_else(|| vec![node]))
            .collect();
    }
    let removed: HashSet<ValueId> = witness.rewrites.iter().map(|r| r.value).collect();
    super::drop_names(&mut expected, &removed);
    Ok((
        expected,
        WitnessVerdict {
            exact: witness.rewrites.len(),
            refinements: 0,
        },
    ))
}

#[cfg(test)]
#[path = "trust_ir_mid_tv_memcall_tests.rs"]
mod tests;
