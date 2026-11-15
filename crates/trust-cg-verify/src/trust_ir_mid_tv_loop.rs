// trust-cg-verify/trust_ir_mid_tv_loop.rs - the loop passes' checkers
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The checkers of the mid-end's two loop passes: loop-invariant code motion
//! ([`LicmWitness`]) and closed-form induction ([`LoopCfWitness`]), the
//! trust-ir forms of the native machine passes `trust-cg-opt/src/licm.rs`
//! and `trust-cg-opt/src/loop_iv.rs`, whose safety arguments they restate
//! over trust-ir's semantics. Everything below is derived here from the
//! SOURCE function with this module's own code: the dominator tree
//! ([`super::dominator_tree`]), the natural loop of the named header, the
//! values that are never poison, invariance, the recurrences, the trip count
//! and the closed form. The pass's analyses are never consulted; a witness
//! names only the header, the values it rewrites and the fresh values it
//! defines.
//!
//! **The loop.** A witness names a header `H`. Its back edges are the edges
//! into `H` from blocks `H` dominates; its body is `H` with every block that
//! reaches a back edge's source without passing `H`. Every body block must
//! be dominated by `H` (otherwise the region has a second entry: an
//! irreducible or unreachable one, refused), and exactly one edge must enter
//! `H` from outside the body, from the PREHEADER `P`, whose terminator must
//! be `br H(args)`: reaching `P`'s end enters the loop. `H` must not be the
//! entry block, which the call enters with any arguments besides its CFG
//! edges, and `P` must be reachable from the entry: with `H` the entry, every
//! reachable edge into `H` is a back edge, and an unreachable block branching
//! to `H` would otherwise pass for the only way in and lend its arguments as
//! the loop's start values.
//!
//! **Never poison.** The interpreter faults when arithmetic, a compare, a
//! cast, a branch or select condition, a call argument or a return inspects
//! poison, and only `undef`, an uninitialized load and the values that carry
//! them are poison. A value is NEVER POISON here when it is a parameter of
//! the entry block (poison at the call boundary is undefined), a constant
//! (integer, `bool`, float), a null pointer, a global's or an allocation's
//! address, the result of an integer, float, compare, cast or overflow
//! operation (each inspects its operands, so it produces a concrete value or
//! faults), or a `copy`, `select` (both arms) or block parameter (every
//! argument of every edge into its block) of values never poison: the
//! greatest fixed point, an inductive invariant of every execution.
//!
//! **Loop-invariant code motion.** Per loop, in witness order:
//!
//! 1. Each claimed INVARIANT PARAMETER of `H` is passed back unchanged by
//!    every edge from the body, so it holds `P`'s argument `a` on every
//!    iteration; `a` is defined outside the body (a value `P`'s terminator
//!    uses dominates `P`, and `P` alone enters the loop, so it dominates `H`)
//!    and has the parameter's type (the header's binding, which the rewrite
//!    drops, faults on any other). Every use of the parameter becomes `a`,
//!    and the parameter and its argument on every edge into `H` go. Exact.
//! 2. Each claimed instruction (named by its first result) is moved, whole,
//!    from its body block to the end of `P` before its terminator, in witness
//!    order, when every operand is defined outside the body or by an
//!    instruction moved before it, and one tier admits it:
//!    * SPECULATABLE: a form that raises nothing on operands never poison
//!      (a constant at its own type: an integer, `bool`, `u128` or float
//!      constant, a null `ptr`, or the bridge's global-address stub of a
//!      global of the module at offset zero at a pointer type, which the
//!      differential reads as that global's address and the wasm lane emits
//!      as one; a null pointer and a global's address; integer `add`,
//!      `sub`, `mul`, bitwise and boolean operations and rotates; float
//!      `add`, `sub`, `mul`, `div`; shifts by a constant below the width;
//!      unsigned division and remainder by a nonzero constant,
//!      signed ones by a constant other than 0 and -1, every amount and
//!      divisor read as the bits the constant holds at the operation's width
//!      (the interpreter masks constants to their width and divides signed
//!      whatever the type's signedness, so `sdiv u32 x, 4294967295` divides
//!      by -1); compares of integers,
//!      `bool`s and floats; `zext`, `sext`, `trunc`, integer and float
//!      `bitcast`s, int/float conversions other than the unsaturated
//!      float-to-int ones, `ptrtoptr`; `ptrtoint`, whose operand the
//!      interpreter only creates at an address the target can name; and
//!      `inttoptr` of an integer at most as wide as a pointer when the body
//!      allocates, frees and calls nothing, so the address resolves to the
//!      same allocation on every iteration; `select`, `copy`, `overflow`
//!      operations) whose every operand is never poison and has the type the
//!      form declares for it (a cast: its source type, between types it
//!      converts without faulting; a select: a `bool` condition), by this
//!      module's typing ([`Defs::value_type`] and overflow results; a value
//!      it cannot type is refused). Moving it executes it where the source
//!      may not: it raises nothing there, and computes the value every
//!      source execution of it computes, from the same operands.
//!    * GUARANTEED: the instruction is in `H` and every instruction before
//!      it in `H` is one of the quiet forms below that neither writes memory
//!      nor stops execution in a defined way (no call, `assert`, store or
//!      atomic): reaching `P`'s end reaches it on the first iteration with
//!      the same operands unless an earlier instruction raises undefined
//!      behaviour. Any speculatable form, a division, remainder or shift by
//!      any amount, a `gep`, an `inttoptr` (as above) and a non-volatile
//!      `load` qualify, the load only when every instruction of the body is
//!      quiet (tier (a): no write, allocation, free or synchronization in the
//!      loop changes the bytes it reads), or when the body's only other
//!      instructions are non-volatile stores each provably disjoint from it
//!      (tier (b), the native pass's `addr_bases_disjoint`: distinct
//!      allocations (two `alloca` instructions, or globals of different
//!      names; every `global_addr` of one global names the same
//!      allocation), or disjoint constant byte ranges of one, the load and
//!      every store at a constant offset inside its allocation; see
//!      `unclobbered_load`), so it reads the same value on every iteration as
//!      at the end of `P`.
//!
//!    Both are exact: the moved instruction computes the same value from the
//!    same operands, and raises in the target only where the source raises
//!    (a guaranteed instruction's operand type fault included: the source
//!    executes the same instruction on the same operands).
//!
//! **Closed-form induction.** The loop must be a COUNTED REDUCTION:
//!
//! * the body's blocks other than `H` form no cycle, end in `br`, `condbr`
//!   or `switch` within the body, and every non-terminator instruction of
//!   the body is removable by this module's dead-code table
//!   ([`super::removal_class`]): no effect, nothing the wasm lane reads as
//!   exposing an address;
//! * exactly one back edge; the only edges leaving the body are `H`'s:
//!   `condbr c, ...` with one target in the body and the other, the EXIT,
//!   outside it, and `c` an `icmp` defined in `H` comparing a parameter
//!   `i` of `H` (the INDUCTION VARIABLE, integer type `Ti`) with a bound `n`
//!   defined outside the body (or an invariant parameter, read as `P`'s
//!   argument); normalized over operand order and which edge stays, the loop
//!   continues while `i <u n`, `i <s n` or `i != n`;
//! * every parameter of `H` is invariant (passed back unchanged) or an
//!   ACCUMULATOR whose back-edge argument is, through copies, `p + t`,
//!   `t + p`, `p - t`, or the value result of `add.overflow` /
//!   `sub.overflow` of those whose flag nothing uses, with `t` an affine
//!   term `b`, `x`, `a * x` or `x * a` in the parameter's integer type `Ta`:
//!   `a`, `b` constants (in the body) or values defined outside it (or
//!   invariant parameters), and `x` the induction variable (`Ta = Ti`), its
//!   `zext` (`Ta` wider, the `<u` exit) or its `sext` (`Ta` wider, the `<s`
//!   exit); the induction variable itself steps by `+ 1` exactly;
//! * every accumulator's initial value and every value coefficient is never
//!   poison and has the accumulator's type, and the bound has the induction
//!   variable's (the loop may run zero times, and the closed form inspects
//!   them).
//!
//! On visit `k` of `H` the induction variable is `i0 + k` (`i0` its initial
//! value): the trip count is `N = (i0 <u n) ? n - i0 : 0` (`<s` alike) or
//! `n - i0` (`!=`), computed at `Ti` and exact, and visit `N` exits. Under
//! the `<u` (`<s`) exit `i0 + k` does not wrap unsigned (signed) for `k <
//! N`, so the `zext` (`sext`) of the induction variable on visit `k` is the
//! extension of `i0` plus `k`. Each accumulator therefore leaves with
//! `p0 + a * S + b * N` (`-` for a subtraction), with `S = N * x0 + T(N)`,
//! `x0` the extension of `i0`, and `T(N) = N (N - 1) / 2` computed without
//! dividing a wrapped value: `((N - (N & 1)) >> 1) * (N - 1 + (N & 1))`, one
//! factor halved exactly; all of it modulo `2^bits(Ta)`, where the sums are
//! exact (a coefficient of one multiplies nothing). `N` at a wider `Ta` and
//! `S` at each `(Ta, extension)` are computed once, where first read, and
//! shared by the accumulators after. The rewrite inserts that
//! computation at the end of `P`, in the instruction order [`closed_form`]
//! fixes, with the witness's fresh values in that order; `P` then passes each accumulator's final value (the
//! induction variable's is `i0 + N`) and each invariant parameter's own
//! argument; `H` keeps its instructions, which now run once on the values of
//! the source's last visit, and ends in `br` to the exit with the exit
//! edge's arguments; the body's other blocks go. The removal is exact when
//! every removed instruction is in the table's exact class, else a
//! refinement (an instruction that inspects a value may raise undefined
//! behaviour the source loop would have raised).
//!
//! **What the check does not establish.** The algebra above (the trip count,
//! the non-wrapping extension, the triangular number and the accumulator's
//! induction step) is a lemma per width, not checked per compile: the lemmas
//! (`loop_cf_lemmas`, built with this module's tests) are discharged by exhaustive evaluation at small
//! widths and handed to the solver by this module's tests, each with a
//! control that drops its side condition. A compile's evidence for a kept
//! rewrite is this structural check and the interpreter differential.

use std::collections::{HashMap, HashSet};

use trust_ir::{
    BinOp, BlockId, CastOp, Constant, Function, ICmpOp, Inst, InstrNode, Module, OverflowOp, Ty,
    ValueId,
};

use super::{
    Defs, MidTvError, RemovalClass, WitnessVerdict, block_positions, dominator_tree, drop_names,
    incoming_edges, int_shape, removal_class, used_values,
};
#[cfg(test)]
use crate::lowering_proof::ProofObligation;
#[cfg(test)]
use crate::smt::SmtExpr;

// ---------------------------------------------------------------------------
// Witnesses
// ---------------------------------------------------------------------------

/// One loop's invariant code motion: the invariant parameters of `header`
/// removed, then the instructions defining `hoisted` (each named by its
/// first result) moved to the preheader, in order.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LicmLoop {
    pub header: BlockId,
    pub invariant_params: Vec<ValueId>,
    pub hoisted: Vec<ValueId>,
}

/// Loop-invariant code motion's claim, applied loop by loop.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct LicmWitness {
    pub loops: Vec<LicmLoop>,
}

impl LicmWitness {
    /// Parameters removed and instructions moved.
    pub fn rewrite_count(&self) -> usize {
        self.loops
            .iter()
            .map(|l| l.invariant_params.len() + l.hoisted.len())
            .sum()
    }
}

/// One counted reduction at `header` replaced by its closed form, whose
/// instructions define `values` in order.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LoopCfLoop {
    pub header: BlockId,
    pub values: Vec<ValueId>,
}

/// Closed-form induction's claim, applied loop by loop.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct LoopCfWitness {
    pub loops: Vec<LoopCfLoop>,
}

impl LoopCfWitness {
    /// Loops replaced.
    pub fn rewrite_count(&self) -> usize {
        self.loops.len()
    }
}

pub(super) fn refuse(header: BlockId, why: impl Into<String>) -> MidTvError {
    MidTvError::NotLoopRewrite {
        header,
        why: why.into(),
    }
}

// ---------------------------------------------------------------------------
// The loop and the never-poison values
// ---------------------------------------------------------------------------

/// A natural loop, by block position.
pub(super) struct LoopShape {
    pub(super) header: usize,
    pub(super) body: HashSet<usize>,
    pub(super) preheader: usize,
    /// The edges into the header from the body.
    pub(super) back_edges: usize,
}

/// The natural loop of `header` in `func` (module docs), or why not.
pub(super) fn loop_shape(func: &Function, header: BlockId) -> Result<LoopShape, MidTvError> {
    let positions = block_positions(func);
    let preds = incoming_edges(func, &positions);
    let h = *positions
        .get(&header)
        .ok_or_else(|| refuse(header, "no such block"))?;
    let (_, idom) = dominator_tree(func, &positions, &preds)
        .ok_or_else(|| refuse(header, "the function has no entry block"))?;
    let entry = positions[&func.entry];
    let dominates = |a: usize, mut b: usize| loop {
        if b == a {
            return true;
        }
        if b == entry || idom[b] == usize::MAX {
            return false;
        }
        b = idom[b];
    };
    if idom[h] == usize::MAX {
        return Err(refuse(header, "the header is unreachable"));
    }
    if h == entry {
        return Err(refuse(
            header,
            "the header is the entry block, which the call enters too",
        ));
    }
    let latches: Vec<usize> = preds[h]
        .iter()
        .copied()
        .filter(|&p| idom[p] != usize::MAX && dominates(h, p))
        .collect();
    if latches.is_empty() {
        return Err(refuse(header, "no back edge enters the header"));
    }
    let mut body: HashSet<usize> = HashSet::from([h]);
    let mut work = latches.clone();
    while let Some(b) = work.pop() {
        if body.insert(b) {
            work.extend(preds[b].iter().copied());
        }
    }
    if body
        .iter()
        .any(|&b| idom[b] == usize::MAX || !dominates(h, b))
    {
        return Err(refuse(
            header,
            "a block of the loop is not dominated by its header (a second entry)",
        ));
    }
    let outside: Vec<usize> = preds[h]
        .iter()
        .copied()
        .filter(|p| !body.contains(p))
        .collect();
    let [preheader] = outside.as_slice() else {
        return Err(refuse(
            header,
            format!(
                "{} edges enter the header from outside the loop",
                outside.len()
            ),
        ));
    };
    if idom[*preheader] == usize::MAX {
        return Err(refuse(header, "the preheader is unreachable"));
    }
    match func.blocks[*preheader].body.last().map(|n| &n.inst) {
        Some(Inst::Br { target, .. }) if *target == header => {}
        _ => {
            return Err(refuse(
                header,
                "the preheader does not end in an unconditional branch to the header",
            ));
        }
    }
    Ok(LoopShape {
        header: h,
        back_edges: preds[h].len() - 1,
        body,
        preheader: *preheader,
    })
}

/// The values of `func` that are never poison (module docs).
pub(crate) fn never_poison(func: &Function) -> HashSet<ValueId> {
    let mut set: HashSet<ValueId> = HashSet::new();
    // (result, then, else) of each `select`, (result, operand) of each copy.
    let mut selects: Vec<(ValueId, ValueId, ValueId)> = Vec::new();
    let mut copies: Vec<(ValueId, ValueId)> = Vec::new();
    // The arguments every edge passes into each block.
    let mut incoming: HashMap<BlockId, Vec<Vec<ValueId>>> = HashMap::new();
    for block in &func.blocks {
        set.extend(block.params.iter().map(|(v, _)| *v));
        for node in &block.body {
            if let Some(last) = node.inst.is_terminator().then_some(&node.inst) {
                for edge in last.successor_edges() {
                    incoming
                        .entry(edge.target)
                        .or_default()
                        .push(edge.args.to_vec());
                }
            }
            match &node.inst {
                Inst::Const {
                    value:
                        Constant::Int(_) | Constant::U128(_) | Constant::Bool(_) | Constant::Float(_),
                    ..
                }
                | Inst::NullPtr
                | Inst::GlobalAddr { .. }
                | Inst::Alloca { .. }
                | Inst::BinOp { .. }
                | Inst::UnOp { .. }
                | Inst::ICmp { .. }
                | Inst::FCmp { .. }
                | Inst::Cast { .. }
                | Inst::Overflow { .. } => set.extend(node.results.iter().copied()),
                Inst::Select {
                    then_val, else_val, ..
                } if node.results.len() == 1 => {
                    set.insert(node.results[0]);
                    selects.push((node.results[0], *then_val, *else_val));
                }
                Inst::Copy { operand, .. } if node.results.len() == 1 => {
                    set.insert(node.results[0]);
                    copies.push((node.results[0], *operand));
                }
                _ => {}
            }
        }
    }
    // Every block's parameters: the entry's have no incoming edge (poison
    // at the call boundary is undefined) unless a branch enters it.
    let params: Vec<(BlockId, usize, ValueId)> = func
        .blocks
        .iter()
        .flat_map(|b| {
            b.params
                .iter()
                .enumerate()
                .map(move |(i, (v, _))| (b.id, i, *v))
        })
        .collect();
    let empty = Vec::new();
    loop {
        let mut changed = false;
        for &(result, then_val, else_val) in &selects {
            if set.contains(&result) && !(set.contains(&then_val) && set.contains(&else_val)) {
                set.remove(&result);
                changed = true;
            }
        }
        for &(result, operand) in &copies {
            if set.contains(&result) && !set.contains(&operand) {
                set.remove(&result);
                changed = true;
            }
        }
        for &(block, index, value) in &params {
            if !set.contains(&value) {
                continue;
            }
            let edges = incoming.get(&block).unwrap_or(&empty);
            if edges
                .iter()
                .any(|args| args.get(index).is_none_or(|a| !set.contains(a)))
            {
                set.remove(&value);
                changed = true;
            }
        }
        if !changed {
            return set;
        }
    }
}

/// Where each value is defined: the block position (a parameter or an
/// instruction result).
pub(super) fn def_blocks(func: &Function) -> HashMap<ValueId, usize> {
    let mut defs = HashMap::new();
    for (bi, block) in func.blocks.iter().enumerate() {
        for (value, _) in &block.params {
            defs.insert(*value, bi);
        }
        for node in &block.body {
            for result in &node.results {
                defs.insert(*result, bi);
            }
        }
    }
    defs
}

/// The argument lists of `inst`'s edges into `target`, for the terminators
/// whose edges this module rewrites; `None` for any other terminator.
fn edge_args_mut(inst: &mut Inst, target: BlockId) -> Option<Vec<&mut Vec<ValueId>>> {
    let mut lists = Vec::new();
    match inst {
        Inst::Br { target: t, args } => {
            if *t == target {
                lists.push(args);
            }
        }
        Inst::CondBr {
            then_target,
            then_args,
            else_target,
            else_args,
            ..
        } => {
            if *then_target == target {
                lists.push(then_args);
            }
            if *else_target == target {
                lists.push(else_args);
            }
        }
        Inst::Switch {
            default,
            default_args,
            cases,
            ..
        } => {
            if *default == target {
                lists.push(default_args);
            }
            for case in cases {
                if case.target == target {
                    lists.push(&mut case.args);
                }
            }
        }
        _ => return None,
    }
    Some(lists)
}

/// The argument lists of `inst`'s edges into `target` (read-only form of
/// [`edge_args_mut`]: every successor edge).
fn edge_args(inst: &Inst, target: BlockId) -> Vec<Vec<ValueId>> {
    inst.successor_edges()
        .into_iter()
        .filter(|e| e.target == target)
        .map(|e| e.args.to_vec())
        .collect()
}

// ---------------------------------------------------------------------------
// Loop-invariant code motion
// ---------------------------------------------------------------------------

/// Forms that neither write memory, allocate, free, synchronize nor stop
/// execution in a defined way (they may raise undefined behaviour).
fn quiet(inst: &Inst) -> bool {
    matches!(
        inst,
        Inst::Const { .. }
            | Inst::NullPtr
            | Inst::GlobalAddr { .. }
            | Inst::Undef { .. }
            | Inst::Copy { .. }
            | Inst::BinOp { .. }
            | Inst::UnOp { .. }
            | Inst::Overflow { .. }
            | Inst::ICmp { .. }
            | Inst::FCmp { .. }
            | Inst::Cast { .. }
            | Inst::Select { .. }
            | Inst::GEP { .. }
            | Inst::PtrData { .. }
            | Inst::PtrMetadata { .. }
            | Inst::Load {
                volatile: false,
                ..
            }
            | Inst::Br { .. }
            | Inst::CondBr { .. }
            | Inst::Switch { .. }
    )
}

/// The bits an integer constant defining `value` holds at run time at a
/// width of `bits`, if one defines it: the interpreter masks every constant
/// to its width, so `const u32 4294967295` is all ones (signed -1 to
/// `sdiv`), and a `usize` constant a 64-bit validator admits wraps at a
/// 32-bit pointer width.
fn const_bits(defs: &Defs<'_>, value: ValueId, bits: u32) -> Option<u128> {
    match defs.inst(value)? {
        Inst::Const {
            value: Constant::Int(k),
            ty,
        } if ty.is_integer() => Some((*k as u128) & width_mask(bits)),
        _ => None,
    }
}

/// All ones at `bits` (at most 128).
fn width_mask(bits: u32) -> u128 {
    if bits >= 128 {
        u128::MAX
    } else {
        (1u128 << bits) - 1
    }
}

/// Whether `ty` is one of the interpreter's pointer-like types.
fn pointer_like(ty: &Ty) -> bool {
    matches!(
        ty,
        Ty::Ptr | Ty::PtrConst(_) | Ty::PtrMut(_) | Ty::Ref(_) | Ty::RefMut(_) | Ty::Rc(_)
    )
}

/// Whether `value`, a constant at `ty`, is the bridge's global-address stub
/// of a global of `module` at offset zero at a pointer type: the
/// differential's view ([`super::interpretable`]) reads it as that global's
/// address (`globaladdr`, then `ptrtoptr`), forms that raise nothing and
/// give the same address on every execution. A nonzero offset is refused:
/// the view adds it with a `gep`, which faults past the address space.
fn global_base_stub(module: &Module, ty: &Ty, value: &Constant) -> bool {
    matches!(
        ty,
        Ty::Ptr | Ty::PtrConst(_) | Ty::PtrMut(_) | Ty::Ref(_) | Ty::RefMut(_)
    ) && matches!(value, Constant::Int(k)
        if super::global_addr_stub(*k)
            .is_some_and(|(index, offset)| offset == 0 && (index as usize) < module.globals.len()))
}

/// Whether `inst` raises nothing when its operands are never poison
/// (module docs, the speculatable tier). Every operand must have the type
/// the form declares for it by `types` (the interpreter faults on any other;
/// an operand `types` cannot type fails), and a cast's types must be a pair
/// the interpreter converts without faulting. `allocates` says whether the
/// loop allocates, frees or calls.
fn speculatable(
    defs: &Defs<'_>,
    types: &HashMap<ValueId, Ty>,
    module: &Module,
    pointer_bits: u32,
    inst: &Inst,
    allocates: bool,
) -> bool {
    let scalar = |ty: &Ty| int_shape(ty, pointer_bits).is_some() || *ty == Ty::Bool;
    let is = |v: &ValueId, ty: &Ty| types.get(v) == Some(ty);
    let float = |ty: &Ty| matches!(ty, Ty::F32 | Ty::F64);
    let int_bits = |ty: &Ty| int_shape(ty, pointer_bits).map(|(bits, _)| bits);
    match inst {
        Inst::BinOp { op, ty, lhs, rhs } => {
            let int = int_shape(ty, pointer_bits);
            let form = match op {
                BinOp::Add
                | BinOp::Sub
                | BinOp::Mul
                | BinOp::And
                | BinOp::Or
                | BinOp::Xor
                | BinOp::RotL
                | BinOp::RotR => {
                    int.is_some()
                        || (*ty == Ty::Bool && matches!(op, BinOp::And | BinOp::Or | BinOp::Xor))
                }
                BinOp::BAnd | BinOp::BOr | BinOp::BXor => *ty == Ty::Bool,
                BinOp::FAdd | BinOp::FSub | BinOp::FMul | BinOp::FDiv => float(ty),
                // Every amount and divisor is read as the bits it holds at
                // the operation's width, as the interpreter reads it.
                BinOp::Shl | BinOp::LShr | BinOp::AShr => int.is_some_and(|(bits, _)| {
                    const_bits(defs, *rhs, bits).is_some_and(|k| k < u128::from(bits))
                }),
                BinOp::UDiv | BinOp::URem => int
                    .is_some_and(|(bits, _)| const_bits(defs, *rhs, bits).is_some_and(|k| k != 0)),
                // The interpreter divides signed at the width whatever the
                // type's signedness: all ones is -1, which overflows on the
                // minimum.
                BinOp::SDiv | BinOp::SRem => int.is_some_and(|(bits, _)| {
                    const_bits(defs, *rhs, bits).is_some_and(|k| k != 0 && k != width_mask(bits))
                }),
                _ => false,
            };
            form && is(lhs, ty) && is(rhs, ty)
        }
        Inst::ICmp { ty, lhs, rhs, .. } => scalar(ty) && is(lhs, ty) && is(rhs, ty),
        Inst::FCmp { ty, lhs, rhs, .. } => float(ty) && is(lhs, ty) && is(rhs, ty),
        Inst::Cast {
            op,
            src_ty,
            dst_ty,
            operand,
        } => {
            is(operand, src_ty)
                && match op {
                    CastOp::ZExt | CastOp::SExt => {
                        matches!((int_bits(src_ty), int_bits(dst_ty)), (Some(s), Some(d)) if d >= s)
                    }
                    CastOp::Trunc => {
                        matches!((int_bits(src_ty), int_bits(dst_ty)), (Some(s), Some(d)) if d <= s)
                    }
                    CastOp::Bitcast => {
                        let width = |ty: &Ty| match ty {
                            Ty::F32 => Some(32),
                            Ty::F64 => Some(64),
                            _ => int_bits(ty),
                        };
                        matches!((width(src_ty), width(dst_ty)), (Some(s), Some(d)) if s == d)
                    }
                    CastOp::UIToFP | CastOp::SIToFP => int_bits(src_ty).is_some() && float(dst_ty),
                    CastOp::FPExt | CastOp::FPTrunc => float(src_ty) && float(dst_ty),
                    CastOp::PtrToPtr => pointer_like(src_ty) && pointer_like(dst_ty),
                    CastOp::PtrToInt => pointer_like(src_ty) && int_bits(dst_ty).is_some(),
                    CastOp::IntToPtr => {
                        !allocates
                            && int_bits(src_ty).is_some_and(|bits| bits <= pointer_bits)
                            && pointer_like(dst_ty)
                    }
                    _ => false,
                }
        }
        Inst::Select {
            ty,
            cond,
            then_val,
            else_val,
        } => {
            !matches!(ty, Ty::Vector(..))
                && is(cond, &Ty::Bool)
                && is(then_val, ty)
                && is(else_val, ty)
        }
        Inst::Copy { ty, operand } => is(operand, ty),
        Inst::Const { ty, value } => match value {
            Constant::Int(k) => {
                int_shape(ty, pointer_bits).is_some()
                    || (*ty == Ty::Ptr && *k == 0)
                    || global_base_stub(module, ty, value)
            }
            Constant::U128(_) => *ty == Ty::U128,
            Constant::Bool(_) => *ty == Ty::Bool,
            Constant::Float(_) => float(ty),
            _ => false,
        },
        Inst::NullPtr | Inst::GlobalAddr { .. } => true,
        Inst::Overflow { ty, lhs, rhs, .. } => {
            int_shape(ty, pointer_bits).is_some() && is(lhs, ty) && is(rhs, ty)
        }
        _ => false,
    }
}

/// Whether the GUARANTEED tier admits `inst`, beyond the speculatable forms.
/// `unclobbered` says, for a load, whether no instruction of the loop can
/// change the bytes it reads (tier (b), [`unclobbered_load`]).
fn guaranteed_form(inst: &Inst, allocates: bool, body_quiet: bool, unclobbered: bool) -> bool {
    match inst {
        Inst::BinOp { .. } | Inst::GEP { .. } => true,
        Inst::Cast {
            op: CastOp::IntToPtr,
            ..
        } => !allocates,
        Inst::Load {
            volatile: false, ..
        } => body_quiet || unclobbered,
        _ => false,
    }
}

/// The identity of an allocation tier (b) compares: an `alloca` by the
/// instruction that allocates it, a global by its name, so every
/// `global_addr` of one global (and of two module entries sharing a symbol
/// name) is the same allocation.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Allocation<'m> {
    Slot(ValueId),
    Global(&'m str),
}

/// Tier (b): whether the load `ptr`/`ty` reads bytes no instruction of the
/// loop writes. Every instruction of the body must be quiet or a
/// non-volatile `store` (no call, allocation, free, bulk memory operation,
/// atomic or fence); the load's address and every store's must read
/// (`super::addr::address`) as an `alloca` (count-free or counted by a
/// positive constant) or `global_addr` plus a constant, the access lying
/// inside that allocation (`super::addr::allocation_size`, the
/// interpreter's layout); and each store must be to another allocation
/// ([`Allocation`]), or to the same one at bytes disjoint from the load's.
/// An allocation is identified by what it allocates, not by the value
/// naming it: every `global_addr` of one global (by name) names the same
/// allocation, however many instructions compute it, while two `alloca`
/// instructions, or two globals of different names, name disjoint
/// allocations (the interpreter's allocations never overlap, and a store
/// through an `alloca` the loop executes writes a fresh allocation the
/// load, whose address is computed before the loop, cannot name). An
/// address inside its allocation resolves to it (`inttoptr` gives the
/// containing allocation's provenance). So the load reads the same bytes on
/// every iteration as at the end of the preheader.
fn unclobbered_load<'m>(
    module: &'m Module,
    pointer_bits: u32,
    func: &Function,
    body: &HashSet<usize>,
    ptr: ValueId,
    ty: &Ty,
) -> bool {
    let defs = Defs::of(func);
    let layout = crate::fsym_layout::FsymLayout::new(module);
    let span = |p: ValueId, t: &Ty| -> Option<(Allocation<'m>, u128, u128)> {
        let (root, off) = super::addr::address(&defs, &layout, pointer_bits, p, 0)?;
        let root = root?;
        let size = u128::from(super::addr::allocation_size(module, &defs, &layout, root)?);
        let len = u128::from(layout.size(t).ok()?);
        let allocation = match defs.inst(root)? {
            Inst::Alloca { .. } => Allocation::Slot(root),
            Inst::GlobalAddr { global } => {
                Allocation::Global(&module.globals.get(global.index() as usize)?.name)
            }
            _ => return None,
        };
        (len > 0 && off.checked_add(len)? <= size).then_some((allocation, off, off + len))
    };
    let Some((root, lo, hi)) = span(ptr, ty) else {
        return false;
    };
    for &b in body {
        for node in &func.blocks[b].body {
            match &node.inst {
                Inst::Store {
                    ty: st,
                    ptr: sp,
                    volatile: false,
                    ..
                } => {
                    let Some((r, a, z)) = span(*sp, st) else {
                        return false;
                    };
                    if r == root && a < hi && lo < z {
                        return false;
                    }
                }
                other if quiet(other) => {}
                _ => return false,
            }
        }
    }
    true
}

pub(super) fn rebuild_licm(
    module: &Module,
    pointer_bits: u32,
    source: &Function,
    witness: &LicmWitness,
) -> Result<(Function, WitnessVerdict), MidTvError> {
    let mut cur = source.clone();
    let mut verdict = WitnessVerdict::default();
    for lp in &witness.loops {
        licm_loop(&mut cur, module, pointer_bits, lp)?;
        verdict.exact += lp.invariant_params.len() + lp.hoisted.len();
    }
    Ok((cur, verdict))
}

fn licm_loop(
    cur: &mut Function,
    module: &Module,
    pointer_bits: u32,
    lp: &LicmLoop,
) -> Result<(), MidTvError> {
    let header = lp.header;
    if lp.invariant_params.is_empty() && lp.hoisted.is_empty() {
        return Err(refuse(header, "the loop claims nothing"));
    }
    let shape = loop_shape(cur, header)?;
    let defs_at = def_blocks(cur);
    // ---- Invariant parameters.
    let mut map: HashMap<ValueId, ValueId> = HashMap::new();
    let mut drop_index: Vec<usize> = Vec::new();
    {
        let param_types = value_types(cur);
        let hb = &cur.blocks[shape.header];
        let Some(Inst::Br { args: init, .. }) =
            cur.blocks[shape.preheader].body.last().map(|n| &n.inst)
        else {
            return Err(refuse(header, "the preheader lost its branch"));
        };
        for &param in &lp.invariant_params {
            let Some(index) = hb.params.iter().position(|(v, _)| *v == param) else {
                return Err(refuse(
                    header,
                    format!("%{param} is not a header parameter"),
                ));
            };
            if drop_index.contains(&index) {
                return Err(refuse(header, format!("%{param} is claimed twice")));
            }
            for &b in &shape.body {
                let Some(last) = cur.blocks[b].body.last() else {
                    continue;
                };
                for args in edge_args(&last.inst, header) {
                    if args.get(index) != Some(&param) {
                        return Err(refuse(
                            header,
                            format!("a back edge does not pass %{param} back unchanged"),
                        ));
                    }
                }
            }
            let Some(&arg) = init.get(index) else {
                return Err(refuse(header, "the preheader passes too few arguments"));
            };
            // The header binds the argument at the parameter's type (the
            // interpreter faults on any other); the rewrite drops that check.
            if param_types.get(&arg) != Some(&hb.params[index].1) {
                return Err(refuse(
                    header,
                    format!("%{param}'s initial value does not have its type"),
                ));
            }
            if defs_at.get(&arg).is_none_or(|b| shape.body.contains(b)) {
                return Err(refuse(
                    header,
                    format!("%{param}'s initial value is not defined outside the loop"),
                ));
            }
            map.insert(param, arg);
            drop_index.push(index);
        }
    }
    if !map.is_empty() {
        drop_index.sort_unstable_by(|a, b| b.cmp(a));
        for bi in 0..cur.blocks.len() {
            let Some(last) = cur.blocks[bi].body.last_mut() else {
                continue;
            };
            if !last
                .inst
                .successor_edges()
                .iter()
                .any(|e| e.target == header)
            {
                continue;
            }
            let Some(lists) = edge_args_mut(&mut last.inst, header) else {
                return Err(refuse(
                    header,
                    "an edge into the header cannot be rewritten",
                ));
            };
            for list in lists {
                for &index in &drop_index {
                    if index < list.len() {
                        list.remove(index);
                    }
                }
            }
        }
        for &index in &drop_index {
            cur.blocks[shape.header].params.remove(index);
        }
        for block in &mut cur.blocks {
            for node in &mut block.body {
                trust_ir::mem2reg::rewrite_inst(&mut node.inst, &map);
            }
        }
        let removed: HashSet<ValueId> = map.keys().copied().collect();
        drop_names(cur, &removed);
    }
    if lp.hoisted.is_empty() {
        return Ok(());
    }
    // ---- Hoisted instructions.
    let poison_free = never_poison(cur);
    let defs_at = def_blocks(cur);
    let mut body_quiet = true;
    let mut allocates = false;
    for &b in &shape.body {
        for node in &cur.blocks[b].body {
            body_quiet &= quiet(&node.inst);
            allocates |= matches!(
                node.inst,
                Inst::Alloca { .. }
                    | Inst::HeapAlloc { .. }
                    | Inst::Dealloc { .. }
                    | Inst::Drop { .. }
                    | Inst::Call { .. }
                    | Inst::CallIndirect { .. }
                    | Inst::CallCannotUnwind { .. }
                    | Inst::CallIndirectCannotUnwind { .. }
            ) || !quiet(&node.inst)
                && !matches!(
                    node.inst,
                    Inst::Store {
                        volatile: false,
                        ..
                    }
                );
        }
    }
    let header_body = cur.blocks[shape.header].body.clone();
    // The definitions before any move: moving a node keeps its definition,
    // and a moved constant still decides a shift or a division.
    let before = cur.clone();
    let defs = Defs::of(&before);
    let types = value_types(&before);
    let mut moved: HashSet<ValueId> = HashSet::new();
    let mut nodes: Vec<InstrNode> = Vec::new();
    for &value in &lp.hoisted {
        let Some(&bi) = defs_at.get(&value) else {
            return Err(refuse(header, format!("%{value} is not defined")));
        };
        if !shape.body.contains(&bi) {
            return Err(refuse(
                header,
                format!("%{value} is not defined in the loop"),
            ));
        }
        let Some(ni) = cur.blocks[bi]
            .body
            .iter()
            .position(|n| n.results.first() == Some(&value))
        else {
            return Err(refuse(
                header,
                format!("%{value} is not an instruction's first result"),
            ));
        };
        let node = &cur.blocks[bi].body[ni];
        if node.inst.is_terminator() {
            return Err(refuse(header, format!("%{value} is a terminator's")));
        }
        let mut operands_ok = true;
        let mut operands_defined = true;
        node.inst.visit_value_operands(|v| {
            let outside = defs_at.get(&v).is_some_and(|b| !shape.body.contains(b));
            operands_ok &= outside || moved.contains(&v);
            operands_defined &= poison_free.contains(&v);
        });
        if !operands_ok {
            return Err(refuse(
                header,
                format!("%{value} has an operand defined in the loop"),
            ));
        }
        let spec = speculatable(&defs, &types, module, pointer_bits, &node.inst, allocates);
        let admitted = if spec && operands_defined {
            true
        } else if bi == shape.header {
            let first = header_body
                .iter()
                .position(|n| n.results.first() == Some(&value))
                .unwrap_or(usize::MAX);
            let clear = header_body.iter().take(first).all(|n| quiet(&n.inst));
            let unclobbered = match &node.inst {
                Inst::Load {
                    ty,
                    ptr,
                    volatile: false,
                    ..
                } if !body_quiet => {
                    unclobbered_load(module, pointer_bits, &before, &shape.body, *ptr, ty)
                }
                _ => false,
            };
            clear && (spec || guaranteed_form(&node.inst, allocates, body_quiet, unclobbered))
        } else {
            false
        };
        if !admitted {
            return Err(refuse(
                header,
                format!(
                    "%{value} is neither speculatable on defined operands nor guaranteed to execute"
                ),
            ));
        }
        let node = cur.blocks[bi].body.remove(ni);
        moved.extend(node.results.iter().copied());
        nodes.push(node);
    }
    let pre = &mut cur.blocks[shape.preheader].body;
    let at = pre.len() - 1;
    for (k, node) in nodes.into_iter().enumerate() {
        pre.insert(at + k, node);
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Closed-form induction
// ---------------------------------------------------------------------------

/// How a counted loop continues.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Exit {
    /// While `i <u n`.
    Ult,
    /// While `i <s n`.
    Slt,
    /// While `i != n`.
    Ne,
}

/// A coefficient of an affine term, available at the end of the preheader.
#[derive(Debug, Clone, PartialEq)]
enum Coef {
    /// Exactly one (an unscaled `x`); emits nothing.
    One,
    /// A constant of the accumulator's type, emitted as a fresh `const`.
    Const(Constant),
    /// A value defined outside the loop.
    Value(ValueId),
}

/// The induction variable's form in a term.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Ext {
    Same,
    Zext,
    Sext,
}

/// One accumulator's recurrence: `p' = p (+|-) (a * x + b)`.
#[derive(Debug, Clone, PartialEq)]
struct Recurrence {
    subtract: bool,
    a: Option<(Coef, Ext)>,
    b: Option<Coef>,
}

/// One header parameter's role.
#[derive(Debug, Clone, PartialEq)]
enum Role {
    Invariant,
    Accumulator(Recurrence),
}

pub(super) fn rebuild_loop_cf(
    pointer_bits: u32,
    source: &Function,
    witness: &LoopCfWitness,
) -> Result<(Function, WitnessVerdict), MidTvError> {
    // Every claimed value is fresh: not defined, used or named in the source,
    // and claimed once.
    let mut taken: HashSet<ValueId> = used_values(source);
    for block in &source.blocks {
        taken.extend(block.params.iter().map(|(v, _)| *v));
        for node in &block.body {
            taken.extend(node.results.iter().copied());
        }
    }
    if let Some(names) = &source.value_names {
        taken.extend(names.iter().map(|(v, _)| *v));
    }
    for lp in &witness.loops {
        for value in &lp.values {
            if !taken.insert(*value) {
                return Err(refuse(lp.header, format!("%{value} is not fresh")));
            }
        }
    }
    let mut cur = source.clone();
    let mut verdict = WitnessVerdict::default();
    for lp in &witness.loops {
        if closed_form_loop(&mut cur, pointer_bits, lp)? {
            verdict.exact += 1;
        } else {
            verdict.refinements += 1;
        }
    }
    Ok((cur, verdict))
}

/// Each instruction result's node and the node's results.
type Nodes<'f> = HashMap<ValueId, (&'f Inst, &'f [ValueId])>;

/// The type of `v`: [`Defs::value_type`], and an overflow operation's value
/// (its type) and flag (`bool`).
fn type_of(defs: &Defs<'_>, nodes: &Nodes<'_>, v: ValueId) -> Option<Ty> {
    defs.value_type(v).or_else(|| match nodes.get(&v)? {
        (Inst::Overflow { ty, .. }, results) => Some(if results.first() == Some(&v) {
            ty.clone()
        } else {
            Ty::Bool
        }),
        _ => None,
    })
}

/// Every value of `func` [`type_of`] types, by value.
pub(super) fn value_types(func: &Function) -> HashMap<ValueId, Ty> {
    let defs = Defs::of(func);
    let mut nodes: Nodes<'_> = HashMap::new();
    for node in func.blocks.iter().flat_map(|b| &b.body) {
        for result in &node.results {
            nodes.insert(*result, (&node.inst, node.results.as_slice()));
        }
    }
    let mut types = HashMap::new();
    for block in &func.blocks {
        let values = block
            .params
            .iter()
            .map(|(v, _)| *v)
            .chain(block.body.iter().flat_map(|n| n.results.iter().copied()));
        for value in values {
            if let Some(ty) = type_of(&defs, &nodes, value) {
                types.entry(value).or_insert(ty);
            }
        }
    }
    types
}

/// Follow `copy`s defined in the loop, each of a value of its own type, to
/// the value they copy.
fn through_copies(
    defs: &Defs<'_>,
    nodes: &Nodes<'_>,
    in_loop: &dyn Fn(ValueId) -> bool,
    mut v: ValueId,
) -> ValueId {
    for _ in 0..64 {
        match defs.inst(v) {
            Some(Inst::Copy { ty, operand })
                if in_loop(v) && type_of(defs, nodes, *operand).as_ref() == Some(ty) =>
            {
                v = *operand;
            }
            _ => break,
        }
    }
    v
}

/// Replace the counted reduction at `lp.header`; `true` when every removed
/// instruction was in the exact class.
fn closed_form_loop(
    cur: &mut Function,
    pointer_bits: u32,
    lp: &LoopCfLoop,
) -> Result<bool, MidTvError> {
    let header = lp.header;
    let shape = loop_shape(cur, header)?;
    if shape.back_edges != 1 {
        return Err(refuse(header, "the loop has more than one back edge"));
    }
    let defs = Defs::of(cur);
    let defs_at = def_blocks(cur);
    let in_body = |v: ValueId| defs_at.get(&v).is_some_and(|b| shape.body.contains(b));
    let h = shape.header;
    // ---- The body: no cycle but through the header, no exit but the
    // header's, nothing but removable instructions.
    let positions = block_positions(cur);
    let mut exact = true;
    for &b in &shape.body {
        let block = &cur.blocks[b];
        let Some((last, rest)) = block.body.split_last() else {
            return Err(refuse(header, "a loop block has no terminator"));
        };
        for node in rest {
            match removal_class(&defs, &node.inst) {
                Some(RemovalClass::Exact) => {}
                Some(RemovalClass::Refinement) => exact = false,
                None => {
                    return Err(refuse(
                        header,
                        format!("block {} has an instruction the loop cannot drop", block.id),
                    ));
                }
            }
        }
        if !matches!(
            last.inst,
            Inst::Br { .. } | Inst::CondBr { .. } | Inst::Switch { .. }
        ) {
            return Err(refuse(
                header,
                format!("block {} does not end in a branch", block.id),
            ));
        }
        if b != h
            && last.inst.successor_edges().iter().any(|e| {
                positions
                    .get(&e.target)
                    .is_none_or(|t| !shape.body.contains(t))
            })
        {
            return Err(refuse(
                header,
                "an edge leaves the loop other than the header's",
            ));
        }
    }
    // Acyclic without the header: a depth-first walk over body edges that
    // do not enter the header.
    {
        let mut state: HashMap<usize, u8> = HashMap::new();
        for &start in &shape.body {
            if start == h || state.contains_key(&start) {
                continue;
            }
            let mut stack = vec![(start, 0usize)];
            state.insert(start, 1);
            while let Some((b, k)) = stack.pop() {
                let succs: Vec<usize> = cur.blocks[b]
                    .body
                    .last()
                    .map(|t| t.inst.successor_edges())
                    .unwrap_or_default()
                    .iter()
                    .filter_map(|e| positions.get(&e.target).copied())
                    .filter(|t| *t != h && shape.body.contains(t))
                    .collect();
                if k < succs.len() {
                    stack.push((b, k + 1));
                    let s = succs[k];
                    match state.get(&s) {
                        Some(1) => return Err(refuse(header, "the loop body has an inner cycle")),
                        Some(_) => {}
                        None => {
                            state.insert(s, 1);
                            stack.push((s, 0));
                        }
                    }
                } else {
                    state.insert(b, 2);
                }
            }
        }
    }
    // Values of the body's other blocks are used nowhere outside the loop.
    for (bi, block) in cur.blocks.iter().enumerate() {
        if shape.body.contains(&bi) {
            continue;
        }
        for node in &block.body {
            let mut leaks = false;
            node.inst.visit_value_operands(|v| {
                leaks |= in_body(v) && defs_at.get(&v) != Some(&h);
            });
            if leaks {
                return Err(refuse(header, "a value of the loop body is used after it"));
            }
        }
    }
    // ---- The exit.
    let hb = &cur.blocks[h];
    let Some(Inst::CondBr {
        cond,
        then_target,
        then_args,
        else_target,
        else_args,
    }) = hb.body.last().map(|n| &n.inst)
    else {
        return Err(refuse(header, "the header does not end in a condbr"));
    };
    let then_in = positions
        .get(then_target)
        .is_some_and(|t| shape.body.contains(t));
    let else_in = positions
        .get(else_target)
        .is_some_and(|t| shape.body.contains(t));
    if then_in == else_in {
        return Err(refuse(
            header,
            "the header's condbr does not leave the loop exactly once",
        ));
    }
    let (exit_target, exit_args) = if then_in {
        (*else_target, else_args.clone())
    } else {
        (*then_target, then_args.clone())
    };
    let Some(Inst::ICmp {
        op,
        ty: cmp_ty,
        lhs,
        rhs,
    }) = defs.inst(*cond)
    else {
        return Err(refuse(header, "the exit condition is not an icmp"));
    };
    if defs_at.get(cond) != Some(&h) {
        return Err(refuse(
            header,
            "the exit condition is not computed in the header",
        ));
    }
    let mut pred = *op;
    if !then_in {
        pred = inverse(pred);
    }
    let params: Vec<ValueId> = hb.params.iter().map(|(v, _)| *v).collect();
    let (iv_value, bound, pred) = if params.contains(lhs) {
        (*lhs, *rhs, pred)
    } else if params.contains(rhs) {
        (*rhs, *lhs, swap(pred))
    } else {
        return Err(refuse(header, "the exit compare reads no header parameter"));
    };
    let exit = match pred {
        ICmpOp::Ult => Exit::Ult,
        ICmpOp::Slt => Exit::Slt,
        ICmpOp::Ne => Exit::Ne,
        _ => {
            return Err(refuse(
                header,
                "the loop does not continue on `<u`, `<s` or `!=`",
            ));
        }
    };
    let k = params.iter().position(|v| *v == iv_value).unwrap_or(0);
    let iv_ty = hb.params[k].1.clone();
    if cmp_ty != &iv_ty || int_shape(&iv_ty, pointer_bits).is_none() {
        return Err(refuse(
            header,
            "the induction variable is not an integer of the compare's type",
        ));
    }
    // ---- The arguments.
    let Some(Inst::Br { args: init, .. }) =
        cur.blocks[shape.preheader].body.last().map(|n| &n.inst)
    else {
        return Err(refuse(header, "the preheader lost its branch"));
    };
    let init = init.clone();
    let mut back: Option<Vec<ValueId>> = None;
    for &b in &shape.body {
        if let Some(last) = cur.blocks[b].body.last() {
            for args in edge_args(&last.inst, header) {
                back = Some(args);
            }
        }
    }
    let Some(back) = back else {
        return Err(refuse(header, "no back edge"));
    };
    if init.len() != params.len() || back.len() != params.len() {
        return Err(refuse(
            header,
            "an edge into the header passes the wrong arity",
        ));
    }
    let in_loop = |v: ValueId| in_body(v);
    let mut nodes: Nodes<'_> = HashMap::new();
    for node in cur.blocks.iter().flat_map(|b| &b.body) {
        for result in &node.results {
            nodes.insert(*result, (&node.inst, node.results.as_slice()));
        }
    }
    let invariant = |j: usize| through_copies(&defs, &nodes, &in_loop, back[j]) == params[j];
    // A value available at the end of the preheader standing for `v`.
    let outside = |v: ValueId| -> Option<ValueId> {
        if !in_body(v) && defs_at.contains_key(&v) {
            return Some(v);
        }
        let j = params.iter().position(|p| *p == v)?;
        invariant(j).then_some(init[j])
    };
    let bound = outside(bound).ok_or_else(|| refuse(header, "the bound varies in the loop"))?;
    let used = used_values(cur);
    let mut roles: Vec<Role> = Vec::new();
    for (j, (param, ty)) in hb.params.iter().enumerate() {
        if invariant(j) {
            roles.push(Role::Invariant);
            continue;
        }
        let rec = recurrence(
            &defs,
            &nodes,
            &in_loop,
            &outside,
            &used,
            pointer_bits,
            *param,
            ty,
            iv_value,
            &iv_ty,
            exit,
            back[j],
        )
        .ok_or_else(|| refuse(header, format!("%{param} is not an affine accumulator")))?;
        if j == k
            && !(rec.a.is_none()
                && !rec.subtract
                && matches!(&rec.b, Some(Coef::Const(Constant::Int(1)))))
        {
            return Err(refuse(
                header,
                "the induction variable does not step by + 1",
            ));
        }
        roles.push(Role::Accumulator(rec));
    }
    if roles[k] == Role::Invariant {
        return Err(refuse(header, "the induction variable does not step"));
    }
    // ---- Types: the closed form reads the bound, each accumulator's
    // initial value and its value coefficients at the types the loop reads
    // them; the interpreter faults on any other, and a coefficient the
    // source reads only inside the body is not read when the loop runs zero
    // times. A value this module cannot type is refused.
    let typed = |v: ValueId, ty: &Ty| type_of(&defs, &nodes, v).as_ref() == Some(ty);
    if !typed(bound, &iv_ty) {
        return Err(refuse(
            header,
            "the bound does not have the induction variable's type",
        ));
    }
    for (j, role) in roles.iter().enumerate() {
        let Role::Accumulator(rec) = role else {
            continue;
        };
        let ty = &hb.params[j].1;
        let mut need = vec![init[j]];
        if let Some((Coef::Value(v), _)) = &rec.a {
            need.push(*v);
        }
        if let Some(Coef::Value(v)) = &rec.b {
            need.push(*v);
        }
        if need.iter().any(|v| !typed(*v, ty)) {
            return Err(refuse(
                header,
                format!(
                    "%{}'s initial value or coefficient does not have its type",
                    params[j]
                ),
            ));
        }
    }
    // ---- Never poison: what the closed form inspects that the source loop
    // may not.
    let defined = never_poison(cur);
    for (j, role) in roles.iter().enumerate() {
        let Role::Accumulator(rec) = role else {
            continue;
        };
        let mut need: Vec<ValueId> = Vec::new();
        if j != k {
            need.push(init[j]);
        }
        if let Some((Coef::Value(v), _)) = &rec.a {
            need.push(*v);
        }
        if let Some(Coef::Value(v)) = &rec.b {
            need.push(*v);
        }
        if need.iter().any(|v| !defined.contains(v)) {
            return Err(refuse(
                header,
                format!(
                    "%{}'s initial value or coefficient may be poison",
                    params[j]
                ),
            ));
        }
    }
    // ---- The rewrite.
    let types: Vec<Ty> = hb.params.iter().map(|(_, t)| t.clone()).collect();
    let mut fresh = lp.values.iter().copied();
    let (nodes, finals) = closed_form(
        &mut fresh, exit, &iv_ty, init[k], bound, &roles, &types, &init, k,
    )
    .ok_or_else(|| refuse(header, "the witness defines too few values"))?;
    if fresh.next().is_some() {
        return Err(refuse(header, "the witness defines too many values"));
    }
    let removed_blocks: Vec<usize> = shape.body.iter().copied().filter(|b| *b != h).collect();
    let mut removed: HashSet<ValueId> = HashSet::new();
    for &b in &removed_blocks {
        let block = &cur.blocks[b];
        removed.extend(block.params.iter().map(|(v, _)| *v));
        for node in &block.body {
            removed.extend(node.results.iter().copied());
        }
    }
    let pre = &mut cur.blocks[shape.preheader].body;
    let at = pre.len() - 1;
    if let Some(Inst::Br { args, .. }) = pre.last_mut().map(|n| &mut n.inst) {
        *args = finals;
    }
    for (i, node) in nodes.into_iter().enumerate() {
        pre.insert(at + i, node);
    }
    if let Some(last) = cur.blocks[h].body.last_mut() {
        last.inst = Inst::Br {
            target: exit_target,
            args: exit_args,
        };
    }
    let mut order: Vec<usize> = removed_blocks;
    order.sort_unstable_by(|a, b| b.cmp(a));
    for b in order {
        cur.blocks.remove(b);
    }
    drop_names(cur, &removed);
    Ok(exact)
}

/// `pred` negated.
fn inverse(pred: ICmpOp) -> ICmpOp {
    match pred {
        ICmpOp::Eq => ICmpOp::Ne,
        ICmpOp::Ne => ICmpOp::Eq,
        ICmpOp::Ult => ICmpOp::Uge,
        ICmpOp::Uge => ICmpOp::Ult,
        ICmpOp::Ule => ICmpOp::Ugt,
        ICmpOp::Ugt => ICmpOp::Ule,
        ICmpOp::Slt => ICmpOp::Sge,
        ICmpOp::Sge => ICmpOp::Slt,
        ICmpOp::Sle => ICmpOp::Sgt,
        ICmpOp::Sgt => ICmpOp::Sle,
    }
}

/// `pred` with its operands swapped.
fn swap(pred: ICmpOp) -> ICmpOp {
    match pred {
        ICmpOp::Eq => ICmpOp::Eq,
        ICmpOp::Ne => ICmpOp::Ne,
        ICmpOp::Ult => ICmpOp::Ugt,
        ICmpOp::Ugt => ICmpOp::Ult,
        ICmpOp::Ule => ICmpOp::Uge,
        ICmpOp::Uge => ICmpOp::Ule,
        ICmpOp::Slt => ICmpOp::Sgt,
        ICmpOp::Sgt => ICmpOp::Slt,
        ICmpOp::Sle => ICmpOp::Sge,
        ICmpOp::Sge => ICmpOp::Sle,
    }
}

/// The recurrence of the accumulator `param` (type `ty`) whose back-edge
/// argument is `back` (module docs), or `None`.
#[allow(clippy::too_many_arguments)]
fn recurrence(
    defs: &Defs<'_>,
    nodes: &Nodes<'_>,
    in_loop: &dyn Fn(ValueId) -> bool,
    outside: &dyn Fn(ValueId) -> Option<ValueId>,
    used: &HashSet<ValueId>,
    pointer_bits: u32,
    param: ValueId,
    ty: &Ty,
    iv: ValueId,
    iv_ty: &Ty,
    exit: Exit,
    back: ValueId,
) -> Option<Recurrence> {
    let (bits, _) = int_shape(ty, pointer_bits)?;
    let (iv_bits, _) = int_shape(iv_ty, pointer_bits)?;
    // The trip count is extended to the accumulator's type, never truncated.
    if bits < iv_bits {
        return None;
    }
    let resolve = |v: ValueId| through_copies(defs, nodes, in_loop, v);
    let step = resolve(back);
    if !in_loop(step) {
        return None;
    }
    // The node defining `step` and whether it is its value result.
    let (subtract, term) = match defs.inst(step) {
        Some(Inst::BinOp {
            op: BinOp::Add,
            ty: t,
            lhs,
            rhs,
        }) if t == ty => {
            if resolve(*lhs) == param {
                (false, *rhs)
            } else if resolve(*rhs) == param {
                (false, *lhs)
            } else {
                return None;
            }
        }
        Some(Inst::BinOp {
            op: BinOp::Sub,
            ty: t,
            lhs,
            rhs,
        }) if t == ty && resolve(*lhs) == param => (true, *rhs),
        _ => overflow_step(nodes, used, step, ty, param, &resolve)?,
    };
    // A coefficient available in the preheader.
    // A constant of the accumulator's type is re-emitted (wherever it is
    // defined); any other value must be available outside the loop.
    let coef = |v: ValueId| -> Option<Coef> {
        let v = resolve(v);
        match defs.inst(v) {
            Some(Inst::Const {
                ty: t,
                value: value @ (Constant::Int(_) | Constant::U128(_)),
            }) if t == ty => Some(Coef::Const(value.clone())),
            _ => outside(v).map(Coef::Value),
        }
    };
    // The induction variable's form in `v`, at the accumulator's type.
    let xform = |v: ValueId| -> Option<Ext> {
        let v = resolve(v);
        if v == iv {
            return (ty == iv_ty).then_some(Ext::Same);
        }
        match defs.inst(v) {
            Some(Inst::Cast {
                op,
                src_ty,
                dst_ty,
                operand,
            }) if in_loop(v) && src_ty == iv_ty && dst_ty == ty && resolve(*operand) == iv => {
                match (op, exit) {
                    (CastOp::ZExt, Exit::Ult) if bits > iv_bits => Some(Ext::Zext),
                    (CastOp::SExt, Exit::Slt) if bits > iv_bits => Some(Ext::Sext),
                    _ => None,
                }
            }
            _ => None,
        }
    };
    let rterm = resolve(term);
    let (a, b) = if let Some(x) = xform(rterm) {
        (Some((Coef::One, x)), None)
    } else if let Some(c) = coef(rterm) {
        (None, Some(c))
    } else {
        match defs.inst(rterm) {
            Some(Inst::BinOp {
                op: BinOp::Mul,
                ty: t,
                lhs,
                rhs,
            }) if t == ty && in_loop(rterm) => {
                if let (Some(x), Some(c)) = (xform(*lhs), coef(*rhs)) {
                    (Some((c, x)), None)
                } else if let (Some(c), Some(x)) = (coef(*lhs), xform(*rhs)) {
                    (Some((c, x)), None)
                } else {
                    return None;
                }
            }
            _ => return None,
        }
    };
    Some(Recurrence { subtract, a, b })
}

/// `add.overflow` / `sub.overflow` of the accumulator whose value result is
/// `step` and whose flag nothing uses: `(subtract, term)`.
fn overflow_step(
    nodes: &Nodes<'_>,
    used: &HashSet<ValueId>,
    step: ValueId,
    ty: &Ty,
    param: ValueId,
    resolve: &dyn Fn(ValueId) -> ValueId,
) -> Option<(bool, ValueId)> {
    let (inst, results) = nodes.get(&step)?;
    let [value, flag] = results else {
        return None;
    };
    if *value != step || used.contains(flag) {
        return None;
    }
    match inst {
        Inst::Overflow {
            op: OverflowOp::AddOverflow,
            ty: t,
            lhs,
            rhs,
        } if t == ty => {
            if resolve(*lhs) == param {
                Some((false, *rhs))
            } else if resolve(*rhs) == param {
                Some((false, *lhs))
            } else {
                None
            }
        }
        Inst::Overflow {
            op: OverflowOp::SubOverflow,
            ty: t,
            lhs,
            rhs,
        } if t == ty && resolve(*lhs) == param => Some((true, *rhs)),
        _ => None,
    }
}

/// The closed form's instructions (in the order the module docs fix) and
/// the preheader's new arguments: the trip count from `i0` and `bound`, then
/// for each parameter in order its final value (an invariant parameter keeps
/// its argument). `None` when `fresh` runs out.
#[allow(clippy::too_many_arguments)]
fn closed_form(
    fresh: &mut dyn Iterator<Item = ValueId>,
    exit: Exit,
    iv_ty: &Ty,
    i0: ValueId,
    bound: ValueId,
    roles: &[Role],
    types: &[Ty],
    init: &[ValueId],
    k: usize,
) -> Option<(Vec<InstrNode>, Vec<ValueId>)> {
    let mut nodes: Vec<InstrNode> = Vec::new();
    let mut emit = |inst: Inst, fresh: &mut dyn Iterator<Item = ValueId>| -> Option<ValueId> {
        let v = fresh.next()?;
        nodes.push(InstrNode::new(inst).with_results([v]));
        Some(v)
    };
    let int = |v: i128| Constant::Int(v);
    let n = match exit {
        Exit::Ult | Exit::Slt => {
            let c = emit(
                Inst::ICmp {
                    op: if exit == Exit::Ult {
                        ICmpOp::Ult
                    } else {
                        ICmpOp::Slt
                    },
                    ty: iv_ty.clone(),
                    lhs: i0,
                    rhs: bound,
                },
                fresh,
            )?;
            let d = emit(binop(BinOp::Sub, iv_ty, bound, i0), fresh)?;
            let z = emit(
                Inst::Const {
                    ty: iv_ty.clone(),
                    value: int(0),
                },
                fresh,
            )?;
            emit(
                Inst::Select {
                    ty: iv_ty.clone(),
                    cond: c,
                    then_val: d,
                    else_val: z,
                },
                fresh,
            )?
        }
        Exit::Ne => emit(binop(BinOp::Sub, iv_ty, bound, i0), fresh)?,
    };
    let mut finals = Vec::with_capacity(roles.len());
    // `N` at each wider type and `S` at each type and extension, emitted
    // where first read and shared after.
    let mut widened: Vec<(Ty, ValueId)> = Vec::new();
    let mut sums: Vec<(Ty, Ext, ValueId)> = Vec::new();
    for (j, role) in roles.iter().enumerate() {
        let Role::Accumulator(rec) = role else {
            finals.push(init[j]);
            continue;
        };
        let ty = &types[j];
        if j == k {
            finals.push(emit(binop(BinOp::Add, ty, i0, n), fresh)?);
            continue;
        }
        let mut terms: Vec<ValueId> = Vec::new();
        if rec.a.is_some() || rec.b.is_some() {
            let na = if ty == iv_ty {
                n
            } else if let Some((_, v)) = widened.iter().find(|(t, _)| t == ty) {
                *v
            } else {
                let v = emit(cast(CastOp::ZExt, iv_ty, ty, n), fresh)?;
                widened.push((ty.clone(), v));
                v
            };
            if let Some((coef, ext)) = &rec.a {
                let sum = if let Some((_, _, v)) = sums.iter().find(|(t, e, _)| t == ty && e == ext)
                {
                    *v
                } else {
                    let x0 = match ext {
                        Ext::Same => i0,
                        Ext::Zext => emit(cast(CastOp::ZExt, iv_ty, ty, i0), fresh)?,
                        Ext::Sext => emit(cast(CastOp::SExt, iv_ty, ty, i0), fresh)?,
                    };
                    let one = emit(
                        Inst::Const {
                            ty: ty.clone(),
                            value: int(1),
                        },
                        fresh,
                    )?;
                    let odd = emit(binop(BinOp::And, ty, na, one), fresh)?;
                    let even = emit(binop(BinOp::Sub, ty, na, odd), fresh)?;
                    let half = emit(binop(BinOp::LShr, ty, even, one), fresh)?;
                    let less = emit(binop(BinOp::Sub, ty, na, one), fresh)?;
                    let other = emit(binop(BinOp::Add, ty, less, odd), fresh)?;
                    let tri = emit(binop(BinOp::Mul, ty, half, other), fresh)?;
                    let base = emit(binop(BinOp::Mul, ty, na, x0), fresh)?;
                    let sum = emit(binop(BinOp::Add, ty, base, tri), fresh)?;
                    sums.push((ty.clone(), *ext, sum));
                    sum
                };
                terms.push(scaled(&mut emit, fresh, ty, coef, sum)?);
            }
            if let Some(coef) = &rec.b {
                terms.push(scaled(&mut emit, fresh, ty, coef, na)?);
            }
        }
        let mut acc = init[j];
        for term in terms {
            let op = if rec.subtract { BinOp::Sub } else { BinOp::Add };
            acc = emit(binop(op, ty, acc, term), fresh)?;
        }
        finals.push(acc);
    }
    Some((nodes, finals))
}

/// `coef * v` at `ty` (`v` itself for [`Coef::One`] and the constant 1).
fn scaled(
    emit: &mut dyn FnMut(Inst, &mut dyn Iterator<Item = ValueId>) -> Option<ValueId>,
    fresh: &mut dyn Iterator<Item = ValueId>,
    ty: &Ty,
    coef: &Coef,
    v: ValueId,
) -> Option<ValueId> {
    let c = match coef {
        Coef::One | Coef::Const(Constant::Int(1)) => return Some(v),
        Coef::Value(c) => *c,
        Coef::Const(value) => emit(
            Inst::Const {
                ty: ty.clone(),
                value: value.clone(),
            },
            fresh,
        )?,
    };
    emit(binop(BinOp::Mul, ty, c, v), fresh)
}

fn binop(op: BinOp, ty: &Ty, lhs: ValueId, rhs: ValueId) -> Inst {
    Inst::BinOp {
        op,
        ty: ty.clone(),
        lhs,
        rhs,
    }
}

fn cast(op: CastOp, src: &Ty, dst: &Ty, operand: ValueId) -> Inst {
    Inst::Cast {
        op,
        src_ty: src.clone(),
        dst_ty: dst.clone(),
        operand,
    }
}

// ---------------------------------------------------------------------------
// Lemmas
// ---------------------------------------------------------------------------

/// One lemma of the closed form at a width, with its control.
#[cfg(test)]
#[derive(Debug, Clone)]
pub(crate) struct LoopLemma {
    pub name: &'static str,
    pub obligation: ProofObligation,
    pub control: ProofObligation,
}

#[cfg(test)]
fn obligation(
    name: String,
    claim: SmtExpr,
    inputs: Vec<(String, u32)>,
    preconditions: Vec<SmtExpr>,
) -> ProofObligation {
    ProofObligation {
        name,
        trust_ir_expr: SmtExpr::ite(claim, SmtExpr::bv_const(1, 1), SmtExpr::bv_const(0, 1)),
        aarch64_expr: SmtExpr::bv_const(1, 1),
        inputs,
        preconditions,
        fp_inputs: vec![],
        category: None,
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
    }
}

/// The closed form's lemmas at `bits` (`2 <= bits <= 32`), each with the
/// control that drops its side condition (or replaces the computation with
/// its naive form):
///
/// * `trip:ult` / `trip:slt` / `trip:ne`: with `N` the trip count, every
///   visit `k < N` continues (`i0 + k` compares as the exit says) and visit
///   `N` exits;
/// * `ext:zext` / `ext:sext`: under the `<u` (`<s`) exit, for `k < N` the
///   extension of `i0 + k` is the extension of `i0` plus `k` (at twice the
///   width);
/// * `tri:base` / `tri:step`: `T(0) = 0` and `T(k + 1) = T(k) + k` for
///   `k + 1` within the width, with `T` the halving form;
/// * `acc:step`: `C(k) = p0 + a (k x0 + T(k)) + b k` satisfies `C(k + 1) =
///   C(k) + a (x0 + k) + b`, so by induction on `k` (with `tri:base`) the
///   accumulator after `N` visits is `C(N)`.
#[cfg(test)]
pub(crate) fn loop_cf_lemmas(bits: u32) -> Vec<LoopLemma> {
    let v = |name: &str| SmtExpr::var(name, bits);
    let c = |k: u64| SmtExpr::bv_const(k, bits);
    let (i0, n, kk) = (v("i0"), v("n"), v("k"));
    let inputs = |names: &[&str]| -> Vec<(String, u32)> {
        names.iter().map(|s| ((*s).to_string(), bits)).collect()
    };
    let lemma = |name: &'static str,
                 claim: SmtExpr,
                 ins: Vec<(String, u32)>,
                 side: Vec<SmtExpr>,
                 control_claim: SmtExpr,
                 control_side: Vec<SmtExpr>| LoopLemma {
        name,
        obligation: obligation(
            format!("irmid loop lemma {name} at {bits} bits"),
            claim,
            ins.clone(),
            side,
        ),
        control: obligation(
            format!("irmid loop control {name} at {bits} bits"),
            control_claim,
            ins,
            control_side,
        ),
    };
    // The trip count of each exit.
    let trip = |exit: Exit| match exit {
        Exit::Ult => SmtExpr::ite(
            i0.clone().bvult(n.clone()),
            n.clone().bvsub(i0.clone()),
            c(0),
        ),
        Exit::Slt => SmtExpr::ite(
            i0.clone().bvslt(n.clone()),
            n.clone().bvsub(i0.clone()),
            c(0),
        ),
        Exit::Ne => n.clone().bvsub(i0.clone()),
    };
    let cont = |exit: Exit, x: SmtExpr| match exit {
        Exit::Ult => x.bvult(n.clone()),
        Exit::Slt => x.bvslt(n.clone()),
        Exit::Ne => x.eq_expr(n.clone()).not_expr(),
    };
    // Visit `k < N` continues and visit `N` exits.
    let trip_claim = |exit: Exit, count: SmtExpr| {
        let k_cont = cont(exit, i0.clone().bvadd(kk.clone()));
        let before = kk.clone().bvult(count.clone()).not_expr().or_expr(k_cont);
        let last = cont(exit, i0.clone().bvadd(count)).not_expr();
        before.and_expr(last)
    };
    // `T(x)`, the halving form, and its naive control `(x * (x - 1)) >> 1`.
    let tri = |x: SmtExpr| {
        let odd = x.clone().bvand(c(1));
        let half = x.clone().bvsub(odd.clone()).bvlshr(c(1));
        half.bvmul(x.bvsub(c(1)).bvadd(odd))
    };
    let naive = |x: SmtExpr| x.clone().bvmul(x.bvsub(c(1))).bvlshr(c(1));
    let no_top = kk.clone().bvult(c(u64::MAX >> (64 - bits)));
    let mut lemmas = Vec::new();
    for (name, exit) in [
        ("trip:ult", Exit::Ult),
        ("trip:slt", Exit::Slt),
        ("trip:ne", Exit::Ne),
    ] {
        // Control: the count without the guard, `n - i0`, under `<u`/`<s`;
        // for `!=`, the guarded count.
        let wrong = match exit {
            Exit::Ne => trip(Exit::Ult),
            _ => n.clone().bvsub(i0.clone()),
        };
        lemmas.push(lemma(
            name,
            trip_claim(exit, trip(exit)),
            inputs(&["i0", "k", "n"]),
            vec![],
            trip_claim(exit, wrong),
            vec![],
        ));
    }
    for (name, exit, signed) in [
        ("ext:zext", Exit::Ult, false),
        ("ext:sext", Exit::Slt, true),
    ] {
        let ext = |x: SmtExpr| {
            if signed {
                x.sign_ext(bits)
            } else {
                x.zero_ext(bits)
            }
        };
        let claim = ext(i0.clone().bvadd(kk.clone()))
            .eq_expr(ext(i0.clone()).bvadd(kk.clone().zero_ext(bits)));
        let within = kk.clone().bvult(trip(exit));
        // Control: the other exit's count (`!=` lets the variable wrap).
        let loose = kk.clone().bvult(trip(Exit::Ne));
        lemmas.push(lemma(
            name,
            claim.clone(),
            inputs(&["i0", "k", "n"]),
            vec![within],
            claim,
            vec![loose],
        ));
    }
    lemmas.push(lemma(
        "tri:base",
        tri(c(0)).eq_expr(c(0)),
        inputs(&["k"]),
        vec![],
        naive(c(0)).bvadd(c(1)).eq_expr(c(0)),
        vec![],
    ));
    let step_claim = |t: &dyn Fn(SmtExpr) -> SmtExpr| {
        t(kk.clone().bvadd(c(1))).eq_expr(t(kk.clone()).bvadd(kk.clone()))
    };
    lemmas.push(lemma(
        "tri:step",
        step_claim(&tri),
        inputs(&["k"]),
        vec![no_top.clone()],
        step_claim(&naive),
        vec![no_top.clone()],
    ));
    let (p0, a, b, x0) = (v("p0"), v("a"), v("b"), v("x0"));
    let closed = |k: SmtExpr, t: &dyn Fn(SmtExpr) -> SmtExpr| {
        let s = k.clone().bvmul(x0.clone()).bvadd(t(k.clone()));
        p0.clone()
            .bvadd(a.clone().bvmul(s))
            .bvadd(b.clone().bvmul(k))
    };
    let acc_claim = |t: &dyn Fn(SmtExpr) -> SmtExpr| {
        let next = closed(kk.clone().bvadd(c(1)), t);
        let stepped = closed(kk.clone(), t)
            .bvadd(a.clone().bvmul(x0.clone().bvadd(kk.clone())))
            .bvadd(b.clone());
        next.eq_expr(stepped)
    };
    lemmas.push(lemma(
        "acc:step",
        acc_claim(&tri),
        inputs(&["a", "b", "k", "p0", "x0"]),
        vec![no_top.clone()],
        acc_claim(&naive),
        vec![no_top],
    ));
    lemmas
}

#[cfg(test)]
#[path = "trust_ir_mid_tv_loop_tests.rs"]
mod tests;
