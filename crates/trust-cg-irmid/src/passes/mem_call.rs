// trust-cg-irmid/passes/mem_call.rs - C memory library calls as bulk-memory instructions
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The memory-call rewrite: a call of the C library's `memmove`, `memcpy`
//! or `memset` declaration with a constant count, or of `memmove` or
//! `memcpy` with a run-time count, whose returned pointer is unused,
//! becomes the trust-ir instruction with that meaning (`memcopy overlap`,
//! `memcopy`, `memset`). The rustc bridge spells `ptr::copy` (so
//! `ptr::swap`), `copy_from_slice` and `ptr::write_bytes` as these calls,
//! as rustc does for LLVM; the wasm32 lane links `compiler_builtins`' loops
//! for them, while it lowers the instructions to `memory.copy` /
//! `memory.fill` under a guard that skips a zero count (LLVM emits
//! `memory.copy` for a run-time count too). At O1 and above a copy of a
//! constant 1 to 32 bytes is emitted without its zero-count guard and the
//! emission pass expands it into loads and stores (`wasm_local_tv`'s
//! small-copy rule); a fill stays a guarded `memory.fill`.
//!
//! **Run-time counts are withheld by default** (OD-165's merge boundary):
//! [`MemCallPass::CONSTANT_COUNTS`], the pipeline's instance, rewrites only
//! constant counts, so a `memmove` or `memcpy` of a run-time count stays a
//! call of the declaration. The widening stays for its tests.
//!
//! **Which calls** (each re-derived by the checker,
//! `trust_ir_mid_tv_memcall.rs`): a direct call whose callee is a
//! declaration of the module named `memmove`, `memcpy` or `memset` with the
//! C prototype (`(ptr, ptr, size) -> ptr` or `(ptr, int, size) -> ptr`, the
//! size an unsigned integer of pointer width, the fill an integer of 9 to
//! 32 bits, so that its truncation to `u8` narrows), each pointer argument
//! pointer-like and the fill and count of their parameter's types, the
//! count defined by an integer constant (any value of its type for a copy),
//! and the result used by no instruction. A function the module defines
//! under one of those names is not a library call.
//!
//! **The rewrite** replaces the call in place: a fresh `const usize` of a
//! constant count (a fresh `zext` of a run-time count to `usize`, or its
//! `copy` when the parameter is `usize`), for `memset` a fresh `trunc` of
//! the fill to `u8`, and the instruction. The witness names each call by
//! its result with the fresh values.

use std::collections::HashSet;

use trust_cg_verify::trust_ir_mid_tv::{MemCall, MemCallWitness, PassWitness};
use trust_ir::{CastOp, Constant, Function, Inst, Module, Ty, ValueId};

use super::loops::first_free_value;
use super::{MidPass, PassContext, drop_names, int_shape, sole_defs, value_types};

pub(crate) struct MemCallPass {
    /// Whether a `memmove` or `memcpy` of a run-time count is rewritten too
    /// (OD-165).
    run_time_counts: bool,
}

impl MemCallPass {
    /// The default profile's rewrite: constant counts only. The run-time
    /// count's widening is withheld (OD-165's merge boundary): it extends
    /// the name-based reading of the C library declarations that OD-143
    /// records as open debt, and the call keeps its effects.
    pub(crate) const CONSTANT_COUNTS: Self = Self {
        run_time_counts: false,
    };

    /// Also a copy of a run-time count, for the crate's tests.
    #[cfg(test)]
    pub(crate) const WITH_RUN_TIME_COUNTS: Self = Self {
        run_time_counts: true,
    };
}

/// The evidence name of the memory-call rewrite.
pub(crate) const MEM_CALL_NAME: &str = "mem_call";

/// The operation a callee is, by the pass's own reading of its name and
/// prototype.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Callee {
    Copy { overlap: bool },
    Set,
}

fn thin(ty: &Ty) -> bool {
    matches!(
        ty,
        Ty::Ptr | Ty::PtrConst(_) | Ty::PtrMut(_) | Ty::Ref(_) | Ty::RefMut(_)
    )
}

fn callee_kind(module: &Module, pointer_bits: u32, callee: &Function) -> Option<Callee> {
    if !callee.blocks.is_empty() {
        return None;
    }
    let kind = match callee.name.as_str() {
        "memmove" => Callee::Copy { overlap: true },
        "memcpy" => Callee::Copy { overlap: false },
        "memset" => Callee::Set,
        _ => return None,
    };
    let sig = module.func_type(callee.ty)?;
    if sig.is_vararg || sig.params.len() != 3 || sig.returns.len() != 1 {
        return None;
    }
    let second = match kind {
        Callee::Set => {
            int_shape(&sig.params[1], pointer_bits).is_some_and(|(b, _)| (9..=32).contains(&b))
        }
        Callee::Copy { .. } => thin(&sig.params[1]),
    };
    (thin(&sig.params[0])
        && thin(&sig.returns[0])
        && second
        && int_shape(&sig.params[2], pointer_bits) == Some((pointer_bits, false)))
    .then_some(kind)
}

impl MidPass for MemCallPass {
    fn name(&self) -> &'static str {
        MEM_CALL_NAME
    }

    fn run(&self, cx: &PassContext<'_>, func: &Function) -> Option<(Function, PassWitness)> {
        let types = value_types(func);
        let defs = sole_defs(func);
        let mut used: HashSet<ValueId> = HashSet::new();
        for node in func.blocks.iter().flat_map(|b| &b.body) {
            node.inst.visit_value_operands(|v| {
                used.insert(v);
            });
        }
        let mut next = first_free_value(func);
        let mut rewrites = Vec::new();
        let mut out = func.clone();
        for block in &mut out.blocks {
            let body = std::mem::take(&mut block.body);
            let mut rebuilt = Vec::with_capacity(body.len());
            for node in body {
                let found = match (&node.inst, node.results.as_slice()) {
                    (Inst::Call { callee, args }, [result]) if !used.contains(result) => {
                        cx.module.function_by_id(*callee).and_then(|f| {
                            let kind = callee_kind(cx.module, cx.pointer_bits, f)?;
                            let sig = cx.module.func_type(f.ty)?;
                            let typed = args.len() == 3
                                && args.iter().zip(&sig.params).all(|(a, t)| {
                                    if thin(t) {
                                        types.get(a).is_some_and(thin)
                                    } else {
                                        types.get(a) == Some(t)
                                    }
                                });
                            // A constant count; for a copy, any other count
                            // of the parameter's type (`typed` checks it).
                            let k = match defs.get(args.get(2)?) {
                                Some(Inst::Const {
                                    ty,
                                    value: Constant::Int(k),
                                }) if ty == &sig.params[2] && *k >= 0 => Some(*k),
                                _ if kind != Callee::Set && self.run_time_counts => None,
                                _ => return None,
                            };
                            typed.then(|| {
                                (
                                    kind,
                                    k,
                                    sig.params[1].clone(),
                                    sig.params[2].clone(),
                                    *result,
                                )
                            })
                        })
                    }
                    _ => None,
                };
                let Some((kind, k, second_ty, count_ty, result)) = found else {
                    rebuilt.push(node);
                    continue;
                };
                let Inst::Call { args, .. } = &node.inst else {
                    rebuilt.push(node);
                    continue;
                };
                let (dst, second, operand) = (args[0], args[1], args[2]);
                let count = ValueId::new(next);
                next += 1;
                let mut constant = node.clone();
                constant.inst = match k {
                    Some(k) => Inst::Const {
                        ty: Ty::Usize,
                        value: Constant::Int(k),
                    },
                    None if count_ty == Ty::Usize => Inst::Copy {
                        ty: Ty::Usize,
                        operand,
                    },
                    None => Inst::Cast {
                        op: CastOp::ZExt,
                        src_ty: count_ty,
                        dst_ty: Ty::Usize,
                        operand,
                    },
                };
                constant.results = vec![count];
                let mut op = node.clone();
                op.results = Vec::new();
                let byte = match kind {
                    Callee::Copy { overlap } => {
                        rebuilt.push(constant);
                        op.inst = Inst::MemCopy {
                            dst,
                            src: second,
                            bytes: count,
                            overlap,
                        };
                        None
                    }
                    Callee::Set => {
                        let byte = ValueId::new(next);
                        next += 1;
                        let mut trunc = node.clone();
                        trunc.inst = Inst::Cast {
                            op: CastOp::Trunc,
                            src_ty: second_ty,
                            dst_ty: Ty::U8,
                            operand: second,
                        };
                        trunc.results = vec![byte];
                        rebuilt.push(constant);
                        rebuilt.push(trunc);
                        op.inst = Inst::MemSet {
                            dst,
                            byte,
                            bytes: count,
                        };
                        Some(byte)
                    }
                };
                rebuilt.push(op);
                rewrites.push(MemCall {
                    value: result,
                    count,
                    byte,
                });
            }
            block.body = rebuilt;
        }
        if rewrites.is_empty() {
            return None;
        }
        let removed: HashSet<ValueId> = rewrites.iter().map(|r| r.value).collect();
        drop_names(&mut out, &removed);
        Some((out, PassWitness::MemCall(MemCallWitness { rewrites })))
    }
}
