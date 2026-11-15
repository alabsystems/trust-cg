// trust-cg-codegen/wasm/lower/pair.rs - which 128-bit integers live in two locals
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The 128-bit integer values the lowering carries as a
//! [`Carrier::Pair`](super::super::layout::Carrier::Pair) (two `i64` locals,
//! low and high half) instead of a 16-byte home in the frame.
//!
//! A [`Carrier::Mem`](super::super::layout::Carrier::Mem) value's local
//! holds the ADDRESS of its bytes, and some lowerings use that address
//! itself rather than the value: a `Select` or `Copy` of a memory-carried
//! value aliases its operand's bytes, a block parameter's edge copy moves
//! bytes, an atomic operation's operands are memory-based. A pair has no
//! address. So a value is pair-carried only when every instruction that
//! defines or reads it has a pair lowering, and the values those
//! address-sharing positions tie together are decided as one:
//!
//! * a block parameter, every argument its incoming edges bind to it, and
//!   the result and operands of a 128-bit `Copy` or `Select` form one class
//!   (a union-find over the function), carried alike;
//! * a class is memory-carried when ANY member is defined or read where only
//!   the memory form is lowered ([`classify`] lists the pair positions;
//!   everything else, the atomics included, keeps the memory form);
//! * every other 128-bit value is pair-carried.
//!
//! The decision is a function of the function and its typing alone, so the
//! lowering and any other consumer agree on it. The carrier does not change
//! the ABI: a 128-bit parameter arrives as two `i64` halves
//! (`ParamLane::Split128`), which the pair then IS, and a 128-bit result
//! leaves through `sret` under the C form, or as two `i64` results under the
//! internal ABI (`abi::lower_internal_sig`), whichever the signature uses.

use std::collections::{HashMap, HashSet};

use trust_ir::{Constant, FuncTy, Function, Inst, Module, Ty, ValueId};

use super::WasmLowerError;
use super::storage;
use super::wide::is_wide;

/// Union-find over the 128-bit values, each class with a "memory-carried"
/// mark.
struct Classes {
    parent: HashMap<ValueId, ValueId>,
    forced: HashSet<ValueId>,
}

impl Classes {
    fn root(&mut self, v: ValueId) -> ValueId {
        let mut r = v;
        while let Some(&p) = self.parent.get(&r) {
            if p == r {
                break;
            }
            r = p;
        }
        // Path compression.
        let mut c = v;
        while c != r {
            let next = self.parent[&c];
            self.parent.insert(c, r);
            c = next;
        }
        r
    }

    fn union(&mut self, a: ValueId, b: ValueId) {
        let (ra, rb) = (self.root(a), self.root(b));
        if ra == rb {
            return;
        }
        // The smaller id is the root, so the result does not depend on the
        // order unions are made in.
        let (keep, drop) = if ra < rb { (ra, rb) } else { (rb, ra) };
        self.parent.insert(drop, keep);
        if self.forced.remove(&drop) {
            self.forced.insert(keep);
        }
    }

    fn force(&mut self, v: ValueId) {
        let r = self.root(v);
        self.forced.insert(r);
    }
}

/// The wide parameter and result types of a callee signature.
fn wide_positions(ft: &FuncTy) -> (Vec<bool>, Vec<bool>) {
    (
        ft.params.iter().map(is_wide).collect(),
        ft.returns.iter().map(is_wide).collect(),
    )
}

/// What one instruction allows: the operand OCCURRENCES it reads a pair at
/// (a value read twice is listed twice), and whether each result may be a
/// pair. Edge arguments are listed too: their class is tied to the target's
/// parameter instead.
struct Allowed {
    operands: Vec<ValueId>,
    results: Vec<bool>,
}

/// Which positions of `inst` have a pair lowering (see the module docs).
/// `wide(v)` is whether `v` is a 128-bit value; `fn_returns` is the enclosing
/// function's result types.
fn classify(
    inst: &Inst,
    module: &Module,
    n_results: usize,
    wide: &dyn Fn(ValueId) -> bool,
    fn_returns: &[Ty],
) -> Allowed {
    let none = |n: usize| Allowed {
        operands: Vec::new(),
        results: vec![false; n],
    };
    let all_results = |n: usize| vec![true; n];
    match inst {
        // A 128-bit integer constant is two `i64.const`s; any other spelling
        // (bytes, `Uninit`) keeps its pooled image.
        Inst::Const { ty, value } if is_wide(ty) => Allowed {
            operands: Vec::new(),
            results: vec![matches!(value, Constant::Int(_) | Constant::U128(_)); n_results],
        },
        // The 128-bit operators read and write halves (`wide.rs`); a shift or
        // rotate amount of 128 bits is read through its low half.
        Inst::BinOp { ty, lhs, rhs, .. } if is_wide(ty) => Allowed {
            operands: vec![*lhs, *rhs],
            results: all_results(n_results),
        },
        Inst::UnOp { ty, operand, .. } if is_wide(ty) => Allowed {
            operands: vec![*operand],
            results: all_results(n_results),
        },
        Inst::ICmp { ty, lhs, rhs, .. } | Inst::Overflow { ty, lhs, rhs, .. } if is_wide(ty) => {
            Allowed {
                operands: vec![*lhs, *rhs],
                results: all_results(n_results),
            }
        }
        // Every cast the lane lowers for a 128-bit integer reads or writes
        // the halves (`value.rs`, `lower_mem_cast`).
        Inst::Cast { operand, .. } => Allowed {
            operands: vec![*operand],
            results: all_results(n_results),
        },
        Inst::Undef { ty } if is_wide(ty) => Allowed {
            operands: Vec::new(),
            results: all_results(n_results),
        },
        // Two `i64` loads / stores of the declared 128-bit integer.
        Inst::Load { ty, .. } if is_wide(ty) => Allowed {
            operands: Vec::new(),
            results: all_results(n_results),
        },
        Inst::Store { ty, value, .. } if is_wide(ty) => Allowed {
            operands: vec![*value],
            results: Vec::new(),
        },
        // A 128-bit argument is two `i64` halves and a 128-bit result comes
        // back through a scratch `sret` slot.
        Inst::Call { callee, args } => {
            match module
                .function_by_id(*callee)
                .and_then(|f| module.func_type(f.ty))
            {
                Some(ft) => {
                    let (params, rets) = wide_positions(ft);
                    Allowed {
                        operands: args
                            .iter()
                            .zip(&params)
                            .filter(|(_, w)| **w)
                            .map(|(a, _)| *a)
                            .collect(),
                        results: (0..n_results)
                            .map(|i| rets.get(i).copied().unwrap_or(false))
                            .collect(),
                    }
                }
                None => none(n_results),
            }
        }
        Inst::CallIndirect { sig, args, .. } => match module.func_type(*sig) {
            Some(ft) => {
                let (params, rets) = wide_positions(ft);
                Allowed {
                    operands: args
                        .iter()
                        .zip(&params)
                        .filter(|(_, w)| **w)
                        .map(|(a, _)| *a)
                        .collect(),
                    results: (0..n_results)
                        .map(|i| rets.get(i).copied().unwrap_or(false))
                        .collect(),
                }
            }
            None => none(n_results),
        },
        Inst::Return { values } => Allowed {
            operands: values
                .iter()
                .zip(fn_returns)
                .filter(|(_, t)| is_wide(t))
                .map(|(v, _)| *v)
                .collect(),
            results: Vec::new(),
        },
        // A lane read loads the halves; a lane write stores them.
        Inst::ExtractField { .. } => Allowed {
            operands: Vec::new(),
            results: all_results(n_results),
        },
        Inst::ExtractElement { index, .. } => Allowed {
            operands: vec![*index],
            results: all_results(n_results),
        },
        Inst::InsertField { value, .. } | Inst::ArraySplat { value, .. } => Allowed {
            operands: vec![*value],
            results: vec![false; n_results],
        },
        Inst::InsertElement { index, value, .. } => Allowed {
            operands: vec![*index, *value],
            results: vec![false; n_results],
        },
        Inst::MakeAggregate { fields, .. } => Allowed {
            operands: fields.clone(),
            results: vec![false; n_results],
        },
        // Indices and counts are read modulo 2^32 from the low half.
        Inst::GEP { indices, .. } => Allowed {
            operands: indices.clone(),
            results: vec![false; n_results],
        },
        Inst::Alloca {
            count: Some(count), ..
        } => Allowed {
            operands: vec![*count],
            results: vec![false; n_results],
        },
        Inst::MemCopy { bytes, .. } | Inst::MemSet { bytes, .. } => Allowed {
            operands: vec![*bytes],
            results: Vec::new(),
        },
        // A 128-bit switch compares the halves; its edge arguments, like
        // every branch's, are tied to the target's parameters.
        Inst::Switch { value, .. } => {
            let mut operands = vec![*value];
            for (_, args) in storage::edges(inst) {
                operands.extend(args.iter().copied().filter(|a| wide(*a)));
            }
            Allowed {
                operands,
                results: Vec::new(),
            }
        }
        Inst::Br { .. } | Inst::CondBr { .. } => {
            let mut operands = Vec::new();
            for (_, args) in storage::edges(inst) {
                operands.extend(args.iter().copied().filter(|a| wide(*a)));
            }
            Allowed {
                operands,
                results: Vec::new(),
            }
        }
        // Tied to their operands by `pair_carried` itself.
        Inst::Copy { ty, operand } if is_wide(ty) => Allowed {
            operands: vec![*operand],
            results: all_results(n_results),
        },
        Inst::Select {
            ty,
            then_val,
            else_val,
            ..
        } if is_wide(ty) => Allowed {
            operands: vec![*then_val, *else_val],
            results: all_results(n_results),
        },
        // Everything else, the atomics included, keeps the memory form.
        _ => none(n_results),
    }
}

/// The 128-bit integer values of `func` the lowering carries as a
/// [`Carrier::Pair`](super::super::layout::Carrier::Pair), given the lane's
/// typing of the function (`types`, `super::value_types`). Deterministic: a
/// function of `func`, `module` and `types` only.
pub(super) fn pair_carried(
    func: &Function,
    module: &Module,
    types: &HashMap<ValueId, Ty>,
) -> Result<HashSet<ValueId>, WasmLowerError> {
    let wide = |v: ValueId| types.get(&v).is_some_and(is_wide);
    let mut classes = Classes {
        parent: HashMap::new(),
        forced: HashSet::new(),
    };
    let mut all: Vec<ValueId> = types
        .iter()
        .filter(|(_, t)| is_wide(t))
        .map(|(v, _)| *v)
        .collect();
    all.sort_unstable();
    for &v in &all {
        classes.parent.insert(v, v);
    }
    if all.is_empty() {
        return Ok(HashSet::new());
    }
    let fn_returns: Vec<Ty> = module
        .func_type(func.ty)
        .map(|ft| ft.returns.clone())
        .unwrap_or_default();
    let block_params: HashMap<trust_ir::BlockId, &[(ValueId, Ty)]> = func
        .blocks
        .iter()
        .map(|b| (b.id, b.params.as_slice()))
        .collect();
    for block in &func.blocks {
        for node in &block.body {
            let inst = &node.inst;
            let allowed = classify(inst, module, node.results.len(), &wide, &fn_returns);
            // Results: a 128-bit result in a position with no pair lowering
            // keeps its memory form.
            for (i, &r) in node.results.iter().enumerate() {
                if wide(r) && !allowed.results.get(i).copied().unwrap_or(false) {
                    classes.force(r);
                }
            }
            // Operands: every 128-bit occurrence must be one the instruction
            // reads as a pair.
            let mut budget: HashMap<ValueId, usize> = HashMap::new();
            for v in &allowed.operands {
                *budget.entry(*v).or_insert(0) += 1;
            }
            let mut refused: Vec<ValueId> = Vec::new();
            inst.visit_value_operands(|v| {
                if !wide(v) {
                    return;
                }
                match budget.get_mut(&v) {
                    Some(n) if *n > 0 => *n -= 1,
                    _ => refused.push(v),
                }
            });
            for v in refused {
                classes.force(v);
            }
            // Address-sharing positions tie their values into one class; a
            // tie to a value that is not a 128-bit integer (a pointer carrier
            // standing in for one) keeps the memory form.
            match inst {
                Inst::Copy { ty, operand } if is_wide(ty) => {
                    for &r in &node.results {
                        if wide(r) && wide(*operand) {
                            classes.union(r, *operand);
                        } else if wide(r) {
                            classes.force(r);
                        }
                    }
                }
                Inst::Select {
                    ty,
                    then_val,
                    else_val,
                    ..
                } if is_wide(ty) => {
                    for &r in &node.results {
                        if !wide(r) {
                            continue;
                        }
                        for o in [*then_val, *else_val] {
                            if wide(o) {
                                classes.union(r, o);
                            } else {
                                classes.force(r);
                            }
                        }
                    }
                }
                _ => {}
            }
            for (target, args) in storage::edges(inst) {
                let Some(params) = block_params.get(&target) else {
                    continue;
                };
                for (&a, (p, _)) in args.iter().zip(params.iter()) {
                    match (wide(a), wide(*p)) {
                        (true, true) => classes.union(a, *p),
                        (true, false) => classes.force(a),
                        (false, true) => classes.force(*p),
                        (false, false) => {}
                    }
                }
            }
        }
    }
    let mut out = HashSet::new();
    for v in all {
        let r = classes.root(v);
        if !classes.forced.contains(&r) {
            out.insert(v);
        }
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The pair-carried values of function `name` of `text`, as value
    /// numbers.
    fn pairs(text: &str, name: &str) -> Vec<u32> {
        let module = trust_ir::parser::parse_module(text).expect("parse");
        let func = module.function_by_name(name).expect("function");
        let types = super::super::value_types(&module, func).expect("types");
        let mut out: Vec<u32> = pair_carried(func, &module, &types)
            .expect("classify")
            .into_iter()
            .map(|v| v.index())
            .collect();
        out.sort_unstable();
        out
    }

    const HEAD: &str = "module \"m\"\ntarget \"wasm32-unknown-unknown\" 4 little\n\n\
                        functy.0 = (i128, i128) -> (i128)\n\n";

    /// Arithmetic, a loop-carried block parameter and its arguments, and a
    /// select are all pairs when nothing reads them through memory.
    #[test]
    fn arithmetic_joins_and_selects_are_pairs() {
        let text = format!(
            "{HEAD}fn @f(functy.0) {{\nbb0(%0: i128, %1: i128):\n\
             \x20   %2 = add i128 %0, %1\n    br bb1(%2)\n\
             bb1(%3: i128):\n    %4 = icmp ult i128 %3, %1\n\
             \x20   %5 = select i128 %4, %3, %0\n    condbr %4, bb1(%5), bb2\n\
             bb2:\n    ret %3\n}}\n"
        );
        assert_eq!(pairs(&text, "f"), [0, 1, 2, 3, 5]);
    }

    /// An atomic operand keeps the memory form, and so does every value its
    /// class ties it to: the select it feeds, the select's other operand, and
    /// the block parameter the select's result is bound to with its other
    /// argument. Values outside the class stay pairs.
    #[test]
    fn a_memory_position_forces_its_whole_class() {
        let text = format!(
            "{HEAD}fn @f(functy.0) {{\nbb0(%0: i128, %1: i128):\n\
             \x20   %2 = alloca i128\n    %3 = add i128 %0, %1\n\
             \x20   %4 = mul i128 %0, %1\n    %5 = icmp ult i128 %3, %4\n\
             \x20   %6 = select i128 %5, %3, %4\n    br bb1(%6)\n\
             bb1(%7: i128):\n    atomic_store seq_cst i128 %7, ptr %2\n\
             \x20   %8 = sub i128 %0, %1\n    ret %8\n}}\n"
        );
        assert_eq!(pairs(&text, "f"), [0, 1, 8]);
    }

    /// A 128-bit value read through a lane that has no pair lowering (here
    /// a field read of the integer itself) keeps the memory form; a store,
    /// a load and a call argument or result of a 128-bit type do not.
    #[test]
    fn only_positions_with_a_pair_lowering_admit_a_pair() {
        let text = format!(
            "{HEAD}fn @g(functy.0) {{\nbb0(%0: i128, %1: i128):\n    ret %0\n}}\n\n\
             fn @f(functy.0) {{\nbb0(%0: i128, %1: i128):\n\
             \x20   %2 = alloca i128\n    store i128 %0, ptr %2\n\
             \x20   %3 = load i128, ptr %2\n    %4 = call @func.0(%3, %1)\n\
             \x20   %5 = extractfield u64 %4, 0\n    %6 = zext u64 %5 to i128\n\
             \x20   ret %6\n}}\n"
        );
        assert_eq!(pairs(&text, "f"), [0, 1, 3, 6]);
    }
}
