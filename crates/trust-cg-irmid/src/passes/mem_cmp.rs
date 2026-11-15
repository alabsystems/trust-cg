// trust-cg-irmid/passes/mem_cmp.rs - a short memcmp as loads and compares
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The comparison-call rewrite: a call of the C library's `memcmp` or `bcmp`
//! declaration with a constant count of at most [`POLICY_BYTES`] becomes
//! the loads and compares that compute what its uses read, as LLVM expands
//! a call with a small constant length (the rustc bridge lowers byte-slice
//! and `&str` equality and ordering to `memcmp`; the wasm32 lane links
//! `compiler_builtins`' byte loop):
//!
//! * a count of 0 is the constant 0;
//! * a count of 1 is the difference of the two bytes read as unsigned
//!   chars (`compiler_builtins`' value, of the sign C asks);
//! * a larger count, only when every use of the result is a zero test
//!   (`icmp eq|ne` with the integer constant 0): the bytes as chunks of 8,
//!   4, 2 and 1 bytes, each pair xored, the xors or-ed together (as `u64`
//!   when a chunk is 8 bytes wide, else as `u32`), and the result 1 when
//!   that is nonzero, 0 otherwise. A use that reads the result's sign keeps
//!   the call.
//!
//! **Which calls** (each re-derived by the checker,
//! `trust_ir_mid_tv_memcmp.rs`): a direct call of a declaration of the
//! module named `memcmp` or `bcmp` with the C prototype (two pointer-like
//! parameters, an integer count of pointer width, a 32-bit integer
//! result), both compared operands pointer-like, the count defined by an
//! integer constant. A function the module defines under the name is not a
//! library call. The witness names each call by its result with the
//! expansion's fresh values in order.
//!
//! **Withheld from the default profile (OD-164's merge boundary).** The
//! rewrite reads a
//! declaration's name and prototype as the C library's comparison. That is
//! the external-semantics premise OD-143 records as open debt for the older
//! `memmove`/`memcpy`/`memset` rewrite, and OD-155 refuses the same kind of
//! name-based custody for the bridge's fill helper: a module import or an
//! undefined object symbol may link any implementation under the name. No
//! default pipeline runs this pass; the report names it in
//! `passes_withheld` with [`MEM_CMP_WITHHELD`], the call keeps its effects,
//! and the differential's view gives the declaration no body. The pass
//! stays for its checker's pipeline tests and for a restoration through
//! producer-authenticated typed instructions.

use std::collections::HashMap;

use trust_cg_verify::trust_ir_mid_tv::{MemCmp, MemCmpWitness, PassWitness};
use trust_ir::{BinOp, CastOp, Constant, Function, ICmpOp, Inst, InstrNode, Module, Ty, ValueId};

use super::loops::first_free_value;
use super::{MidPass, PassContext, int_shape, sole_defs, value_types};

pub(crate) struct MemCmpPass;

/// The evidence name of the comparison-call rewrite.
pub(crate) const MEM_CMP_NAME: &str = "mem_cmp";

/// Why the default profile withholds the comparison-call rewrite (module
/// docs, OD-164).
pub(crate) const MEM_CMP_WITHHELD: &str = "a memcmp or bcmp declaration's name and prototype \
     do not authenticate the C library's comparison (OD-164)";

/// The most bytes a call is expanded for (policy: LLVM's wasm32 expansion
/// stops near here; the checker admits `MAX_MEMCMP_BYTES`).
pub(crate) const POLICY_BYTES: u64 = 16;

fn thin(ty: &Ty) -> bool {
    matches!(
        ty,
        Ty::Ptr | Ty::PtrConst(_) | Ty::PtrMut(_) | Ty::Ref(_) | Ty::RefMut(_)
    )
}

/// The result type of a call of `callee` when it is a comparison
/// declaration with the C prototype.
fn compare_result(module: &Module, pointer_bits: u32, callee: &Function) -> Option<Ty> {
    if !callee.blocks.is_empty() || !matches!(callee.name.as_str(), "memcmp" | "bcmp") {
        return None;
    }
    let sig = module.func_type(callee.ty)?;
    if sig.is_vararg || sig.params.len() != 3 || sig.returns.len() != 1 {
        return None;
    }
    let width = |ty: &Ty| int_shape(ty, pointer_bits).map(|(bits, _)| bits);
    (thin(&sig.params[0])
        && thin(&sig.params[1])
        && width(&sig.params[2]) == Some(pointer_bits)
        && width(&sig.returns[0]) == Some(32))
    .then(|| sig.returns[0].clone())
}

/// The chunks of `n` bytes: `(offset, width)`, 8, 4, 2 and 1 bytes greedily.
fn chunks(n: u64) -> Vec<(u64, u64)> {
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

/// The expansion of a call (`node`, its result `result` of type `ret`)
/// comparing `k` bytes of `a` and `b`, with fresh values from `fresh`.
fn expand(
    node: &InstrNode,
    k: u64,
    (a, b): (ValueId, ValueId),
    result: ValueId,
    ret: &Ty,
    fresh: &mut dyn FnMut() -> ValueId,
) -> (Vec<InstrNode>, Vec<ValueId>) {
    let mut out: Vec<InstrNode> = Vec::new();
    let mut named: Vec<ValueId> = Vec::new();
    let mut emit = |inst: Inst, results: Vec<ValueId>| {
        let mut n = node.clone();
        n.inst = inst;
        n.results = results;
        out.push(n);
    };
    let mut new = || {
        let v = fresh();
        named.push(v);
        v
    };
    let load = |ty: Ty, ptr: ValueId| Inst::Load {
        ty,
        ptr,
        volatile: false,
        align: Some(1),
    };
    if k == 0 {
        emit(
            Inst::Const {
                ty: ret.clone(),
                value: Constant::Int(0),
            },
            vec![result],
        );
    } else if k == 1 {
        let (la, lb, za, zb) = (new(), new(), new(), new());
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
    } else {
        let parts = chunks(k);
        let wide = if parts.iter().any(|&(_, w)| w == 8) {
            Ty::U64
        } else {
            Ty::U32
        };
        let mut acc: Option<ValueId> = None;
        for (offset, width) in parts {
            let ty = match width {
                8 => Ty::U64,
                4 => Ty::U32,
                2 => Ty::U16,
                _ => Ty::U8,
            };
            let (o, pa, la, pb, lb, x) = (new(), new(), new(), new(), new(), new());
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
                let w = new();
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
                    let joined = new();
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
        let (z, ne) = (new(), new());
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
                lhs: acc.expect("at least one chunk"),
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
    (out, named)
}

impl MidPass for MemCmpPass {
    fn name(&self) -> &'static str {
        MEM_CMP_NAME
    }

    fn run(&self, cx: &PassContext<'_>, func: &Function) -> Option<(Function, PassWitness)> {
        let types = value_types(func);
        let defs = sole_defs(func);
        let zero = |v: &ValueId| {
            matches!(
                defs.get(v),
                Some(Inst::Const {
                    ty,
                    value: Constant::Int(0),
                }) if ty.is_integer()
            )
        };
        // Per value: whether every use is a zero test of it.
        let mut zero_tests: HashMap<ValueId, bool> = HashMap::new();
        for node in func.blocks.iter().flat_map(|b| &b.body) {
            let tested = match &node.inst {
                Inst::ICmp {
                    op: ICmpOp::Eq | ICmpOp::Ne,
                    lhs,
                    rhs,
                    ..
                } if lhs != rhs => {
                    if zero(rhs) {
                        Some(*lhs)
                    } else if zero(lhs) {
                        Some(*rhs)
                    } else {
                        None
                    }
                }
                _ => None,
            };
            node.inst.visit_value_operands(|v| {
                let all = zero_tests.entry(v).or_insert(true);
                *all &= tested == Some(v);
            });
        }
        let mut next = first_free_value(func);
        let mut fresh = || {
            let v = ValueId::new(next);
            next += 1;
            v
        };
        let mut rewrites = Vec::new();
        let mut out = func.clone();
        for block in &mut out.blocks {
            let body = std::mem::take(&mut block.body);
            let mut rebuilt = Vec::with_capacity(body.len());
            for node in body {
                let found = match (&node.inst, node.results.as_slice()) {
                    (Inst::Call { callee, args }, [result]) if args.len() == 3 => {
                        cx.module.function_by_id(*callee).and_then(|f| {
                            let ret = compare_result(cx.module, cx.pointer_bits, f)?;
                            let sig = cx.module.func_type(f.ty)?;
                            let k = match defs.get(&args[2])? {
                                Inst::Const {
                                    ty,
                                    value: Constant::Int(k),
                                } if ty == &sig.params[2] => {
                                    u64::try_from((*k as u128) & ((1u128 << cx.pointer_bits) - 1))
                                        .ok()?
                                }
                                _ => return None,
                            };
                            let operands = args[..2].iter().all(|a| types.get(a).is_some_and(thin));
                            let uses_ok = k <= 1 || zero_tests.get(result).copied().unwrap_or(true);
                            (operands && uses_ok && k <= POLICY_BYTES)
                                .then(|| (k, (args[0], args[1]), *result, ret))
                        })
                    }
                    _ => None,
                };
                let Some((k, operands, result, ret)) = found else {
                    rebuilt.push(node);
                    continue;
                };
                let (nodes, named) = expand(&node, k, operands, result, &ret, &mut fresh);
                rebuilt.extend(nodes);
                rewrites.push(MemCmp {
                    value: result,
                    fresh: named,
                });
            }
            block.body = rebuilt;
        }
        if rewrites.is_empty() {
            return None;
        }
        Some((out, PassWitness::MemCmp(MemCmpWitness { rewrites })))
    }
}
