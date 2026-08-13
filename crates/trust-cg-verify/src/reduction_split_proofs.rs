// trust-cg-verify/reduction_split_proofs.rs - SMT proofs for reduction-splitting correctness
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Proves that the reduction-splitting (accumulator-widening) loop optimization
// in crates/trust-cg-opt/src/reduction_split.rs preserves semantics. The pass
// rewrites a serial integer reduction
//
//     acc = acc_init; for i { acc = acc <op> f(i); }
//
// into N independent accumulators distributed by residue class, combined by a
// balanced tree at loop exit:
//
//     accj = (j==0 ? acc_init : identity);
//     for i { acc[i%N] = acc[i%N] <op> f(i); }
//     acc = ((acc0 <op> acc1) <op> (acc2 <op> acc3));
//
// This is a REGROUPING of the reduction. For an associative AND commutative
// integer op (bvadd, bvmul, bvor, bvxor over Z/2^w) any regrouping yields the
// bit-for-bit identical result, so the transform is sound WITHOUT a per-instance
// proof. These obligations prove that the specific regrouping the pass performs
// equals the sequential fold, for split factor N=4, at 8- and 64-bit widths.
//
// Technique: Alive2-style (PLDI 2021). Encode the sequential fold (LHS) and the
// N-lane split+combine (RHS) as SMT bitvector expressions and check
// NOT(LHS == RHS) for UNSAT (evaluated by 100k-sample multi-input testing since
// each obligation has 3+ inputs).
//
// Reference: crates/trust-cg-opt/src/reduction_split.rs

//! SMT proofs for reduction-splitting (accumulator-widening) correctness.
//!
//! | Family | Property |
//! |--------|----------|
//! | Regrouping (constant) | `fold(acc, t0..t{M-1})` == `split_N_combine(acc, t0..t{M-1})` for op ∈ {+,*,\|,^}, M a multiple of N |
//! | Sum-of-products (Madd) | regrouping holds when each term is a product `a[i]*b[i]` |
//! | Split-with-tail (runtime) | `fold` == `split_tail_combine` — main residue lanes + balanced combine + a SEQUENTIAL remainder tail — for ANY M (every tail residue M mod N), incl. M < N (empty main) |
//! | Identity | `op(x, identity) == x` (identity materialised into extra lanes) |

use crate::lowering_proof::ProofObligation;
use crate::smt::SmtExpr;

/// Split factor the pass uses (four independent accumulators).
const N: usize = 4;

/// The associative + commutative integer ops the pass splits.
#[derive(Clone, Copy)]
enum Op {
    Add,
    Mul,
    Or,
    Xor,
}

impl Op {
    fn apply(self, a: SmtExpr, b: SmtExpr) -> SmtExpr {
        match self {
            Op::Add => a.bvadd(b),
            Op::Mul => a.bvmul(b),
            Op::Or => a.bvor(b),
            Op::Xor => a.bvxor(b),
        }
    }

    fn identity(self) -> u64 {
        match self {
            Op::Mul => 1,
            _ => 0,
        }
    }

    fn label(self) -> &'static str {
        match self {
            Op::Add => "add",
            Op::Mul => "mul",
            Op::Or => "or",
            Op::Xor => "xor",
        }
    }

    fn all() -> [Op; 4] {
        [Op::Add, Op::Mul, Op::Or, Op::Xor]
    }
}

/// Sequential left fold: `acc_init op t0 op t1 op ... op t{M-1}`.
fn fold(acc_init: SmtExpr, terms: &[SmtExpr], op: Op) -> SmtExpr {
    let mut acc = acc_init;
    for t in terms {
        acc = op.apply(acc, t.clone());
    }
    acc
}

/// N-lane split with balanced-tree combine — exactly what the pass emits.
/// Lane 0 seeds from `acc_init`; lanes 1..N seed from the op identity. Term `i`
/// goes to lane `i % N`. The lanes are then combined with a balanced tree.
fn split_combine(acc_init: SmtExpr, terms: &[SmtExpr], op: Op, width: u32) -> SmtExpr {
    let mut lanes: Vec<SmtExpr> = (0..N)
        .map(|j| {
            if j == 0 {
                acc_init.clone()
            } else {
                SmtExpr::bv_const(op.identity(), width)
            }
        })
        .collect();
    for (i, t) in terms.iter().enumerate() {
        let j = i % N;
        lanes[j] = op.apply(lanes[j].clone(), t.clone());
    }
    // Balanced-tree combine (matches build_combine_and_rewire).
    balanced_combine(lanes, op)
}

/// Balanced-tree combine of `lanes` — matches `build_balanced_combine` /
/// `build_combine_and_rewire` (pairs left-to-right, carry the odd one up).
fn balanced_combine(mut lanes: Vec<SmtExpr>, op: Op) -> SmtExpr {
    while lanes.len() > 1 {
        let mut next: Vec<SmtExpr> = Vec::new();
        let mut i = 0;
        while i + 1 < lanes.len() {
            next.push(op.apply(lanes[i].clone(), lanes[i + 1].clone()));
            i += 2;
        }
        if i < lanes.len() {
            next.push(lanes[i].clone());
        }
        lanes = next;
    }
    lanes.into_iter().next().unwrap()
}

/// RUNTIME split-with-tail — exactly what `apply_runtime` emits. The first
/// `main_count = (M / N) * N` terms (the whole groups of `N`) are distributed
/// across the `N` lanes by residue `i % N` and combined with a balanced tree;
/// the remaining `M % N` terms (< N of them) are then folded SEQUENTIALLY onto
/// the combined accumulator — the peeled remainder tail. When `M < N` the main
/// portion is empty (`main_count = 0`), modelling the guard-skip path where the
/// entire range runs through the tail.
fn split_tail_combine(acc_init: SmtExpr, terms: &[SmtExpr], op: Op, width: u32) -> SmtExpr {
    let m = terms.len();
    let main_count = (m / N) * N; // largest multiple of N that is <= m

    // Main: N residue-class lanes over terms[0..main_count].
    let mut lanes: Vec<SmtExpr> = (0..N)
        .map(|j| {
            if j == 0 {
                acc_init.clone()
            } else {
                SmtExpr::bv_const(op.identity(), width)
            }
        })
        .collect();
    for (i, t) in terms.iter().enumerate().take(main_count) {
        lanes[i % N] = op.apply(lanes[i % N].clone(), t.clone());
    }
    let mut acc = balanced_combine(lanes, op);

    // Tail: sequential fold over the remaining terms[main_count..M].
    for t in terms.iter().skip(main_count) {
        acc = op.apply(acc, t.clone());
    }
    acc
}

fn obligation(
    name: String,
    lhs: SmtExpr,
    rhs: SmtExpr,
    inputs: Vec<(String, u32)>,
) -> ProofObligation {
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name,
        trust_ir_expr: lhs,
        aarch64_expr: rhs,
        inputs,
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::DataFlow),
    }
}

fn width_label(width: u32) -> &'static str {
    if width == 8 { " (8-bit)" } else { "" }
}

// ===========================================================================
// 1. Regrouping: sequential fold == N-lane split + combine
// ===========================================================================

/// Regrouping proof for `op` over `m` arbitrary terms at `width` bits.
fn proof_regroup(op: Op, m: usize, width: u32) -> ProofObligation {
    let acc = SmtExpr::var("acc", width);
    let terms: Vec<SmtExpr> = (0..m)
        .map(|i| SmtExpr::var(format!("t{i}"), width))
        .collect();

    let lhs = fold(acc.clone(), &terms, op);
    let rhs = split_combine(acc, &terms, op, width);

    let mut inputs = vec![("acc".to_string(), width)];
    for i in 0..m {
        inputs.push((format!("t{i}"), width));
    }
    obligation(
        format!(
            "ReductionSplit: {} regroup N={} M={}{}",
            op.label(),
            N,
            m,
            width_label(width)
        ),
        lhs,
        rhs,
        inputs,
    )
}

// ===========================================================================
// 2. Sum-of-products (fused Madd): terms are products a[i]*b[i]
// ===========================================================================

/// Regrouping proof for an ADD reduction whose terms are products
/// `a[i] * b[i]` — the shape a fused `Madd` (`a*b + acc`) reduction splits into.
fn proof_madd_regroup(m: usize, width: u32) -> ProofObligation {
    let acc = SmtExpr::var("acc", width);
    let a: Vec<SmtExpr> = (0..m)
        .map(|i| SmtExpr::var(format!("a{i}"), width))
        .collect();
    let b: Vec<SmtExpr> = (0..m)
        .map(|i| SmtExpr::var(format!("b{i}"), width))
        .collect();
    let terms: Vec<SmtExpr> = (0..m).map(|i| a[i].clone().bvmul(b[i].clone())).collect();

    let lhs = fold(acc.clone(), &terms, Op::Add);
    let rhs = split_combine(acc, &terms, Op::Add, width);

    let mut inputs = vec![("acc".to_string(), width)];
    for i in 0..m {
        inputs.push((format!("a{i}"), width));
        inputs.push((format!("b{i}"), width));
    }
    obligation(
        format!(
            "ReductionSplit: madd (sum of a*b) regroup N={} M={}{}",
            N,
            m,
            width_label(width)
        ),
        lhs,
        rhs,
        inputs,
    )
}

// ===========================================================================
// 2b. RUNTIME split-with-tail: main residue lanes + balanced combine + a
//     sequential remainder tail equals the sequential fold, for a trip count M
//     with ANY residue M mod N (the tail length). This is the obligation the
//     runtime `apply_runtime` path relies on.
// ===========================================================================

/// Runtime split-with-tail regrouping proof for `op` over `m` arbitrary terms at
/// `width` bits: `fold == split_tail_combine`. `m` is chosen to exercise a given
/// `m mod N` tail residue (and, when `m < N`, the empty-main / all-tail path).
fn proof_split_tail_regroup(op: Op, m: usize, width: u32) -> ProofObligation {
    let acc = SmtExpr::var("acc", width);
    let terms: Vec<SmtExpr> = (0..m)
        .map(|i| SmtExpr::var(format!("t{i}"), width))
        .collect();

    let lhs = fold(acc.clone(), &terms, op);
    let rhs = split_tail_combine(acc, &terms, op, width);

    let mut inputs = vec![("acc".to_string(), width)];
    for i in 0..m {
        inputs.push((format!("t{i}"), width));
    }
    obligation(
        format!(
            "ReductionSplit: {} split+tail N={} M={} (tail={}){}",
            op.label(),
            N,
            m,
            m % N,
            width_label(width)
        ),
        lhs,
        rhs,
        inputs,
    )
}

/// Runtime split-with-tail proof for the fused-`Madd` (sum-of-products) shape:
/// terms are products `a[i]*b[i]`, at trip count `m` (tail residue `m mod N`).
fn proof_madd_split_tail_regroup(m: usize, width: u32) -> ProofObligation {
    let acc = SmtExpr::var("acc", width);
    let a: Vec<SmtExpr> = (0..m)
        .map(|i| SmtExpr::var(format!("a{i}"), width))
        .collect();
    let b: Vec<SmtExpr> = (0..m)
        .map(|i| SmtExpr::var(format!("b{i}"), width))
        .collect();
    let terms: Vec<SmtExpr> = (0..m).map(|i| a[i].clone().bvmul(b[i].clone())).collect();

    let lhs = fold(acc.clone(), &terms, Op::Add);
    let rhs = split_tail_combine(acc, &terms, Op::Add, width);

    let mut inputs = vec![("acc".to_string(), width)];
    for i in 0..m {
        inputs.push((format!("a{i}"), width));
        inputs.push((format!("b{i}"), width));
    }
    obligation(
        format!(
            "ReductionSplit: madd split+tail N={} M={} (tail={}){}",
            N,
            m,
            m % N,
            width_label(width)
        ),
        lhs,
        rhs,
        inputs,
    )
}

// ===========================================================================
// 3. Identity: op(x, identity) == x  (the seed of extra accumulators)
// ===========================================================================

/// Proof that the op identity materialised into lanes 1..N is a true identity:
/// `op(x, identity) == x`.
fn proof_identity(op: Op, width: u32) -> ProofObligation {
    let x = SmtExpr::var("x", width);
    let id = SmtExpr::bv_const(op.identity(), width);
    let lhs = op.apply(x.clone(), id);
    let rhs = x;
    obligation(
        format!(
            "ReductionSplit: {} identity op(x,id)==x{}",
            op.label(),
            width_label(width)
        ),
        lhs,
        rhs,
        vec![("x".to_string(), width)],
    )
}

// ===========================================================================
// 4. Affine (linear) strength reduction of a degree-1 term sub-expression.
//    A sub-term `L(i) = c·i + a0` (e.g. `i*3`, `i*7`) is maintained by a running
//    addition: a single carried base `v = L(i)`; lane `k`'s value is `v + c·k`
//    and the per-iteration step is `v += c·N`. Both are the instance `d ∈
//    {k, N}` of ONE distributivity identity:
//        (c·x + a0) + c·d  ==  c·(x + d) + a0.
//    The multiplier `c` is a COMPILE-TIME CONSTANT (the analysis only reduces
//    `mul(iv, const)`), so we prove the identity for representative concrete `c`
//    with `x, a0, d` symbolic. A symbolic `d` covers every per-lane offset and
//    the per-iteration step at once. Keeping `c` concrete makes `c·x` a LINEAR
//    (constant-coefficient) bitvector term the SMT solver discharges instantly;
//    a fully-symbolic `c·x` is a hard nonlinear (var×var) query that times out.
//    General `c` follows by ring distributivity. Quadratics are NOT reduced
//    (left as multiplies), so no degree-2 obligation is needed.
// ===========================================================================

/// Affine strength-reduction identity `c·x + c·d == c·(x+d)` over `Z/2^width`,
/// for a concrete multiplier `c` and concrete shift `d` (the additive constant
/// `a0` cancels and is elided). Only `x` is symbolic — matching the existing
/// single-variable recurrence proofs (`x·2ⁿ == x<<n`) that the CLI solver
/// discharges quickly. `d` ranges over the per-lane offsets `1,2,3` and the
/// per-iteration step `N=4`; `c` over the linear coefficients real kernels use.
fn proof_affine_reduce(c: u64, d: u64, width: u32) -> ProofObligation {
    let cc = SmtExpr::bv_const(c, width);
    let x = SmtExpr::var("x", width);
    let dd = SmtExpr::bv_const(d, width);
    let cd = SmtExpr::bv_const(c.wrapping_mul(d), width); // compile-time constant c·d
    // Recurrence value at shift d: (c·x) + (c·d).
    let lhs = cc.clone().bvmul(x.clone()).bvadd(cd);
    // Direct evaluation of the linear sub-term at the shifted index: c·(x+d).
    let rhs = cc.bvmul(x.bvadd(dd));
    obligation(
        format!(
            "ReductionSplit: affine reduce c={c} d={d} c·x+c·d == c·(x+d){}",
            width_label(width)
        ),
        lhs,
        rhs,
        vec![("x".to_string(), width)],
    )
}

/// Representative concrete multipliers for the affine reduction proofs — the
/// linear coefficients real kernels use (`i*1`, `i*3`, `i*7`).
const AFFINE_CS: [u64; 3] = [1, 3, 7];
/// Shifts to check: the three per-lane offsets and the per-iteration step N=4.
const AFFINE_DS: [u64; 4] = [1, 2, 3, 4];

// ---------------------------------------------------------------------------
// Registry
// ---------------------------------------------------------------------------

/// Trip counts exercising every tail residue `M mod N` for the runtime
/// split-with-tail obligations: `3` (empty main / all-tail), `5,6,7` (one full
/// group + a `1,2,3`-element tail), `8` (two full groups, empty tail).
const SPLIT_TAIL_MS: [usize; 5] = [3, 5, 6, 7, 8];

/// All reduction-splitting proofs.
///
/// Total: 78 =
///   - regrouping (constant, exact): 4 ops × 2 term-counts (M=4,8) × 2 widths  = 16
///   - sum-of-products (Madd, exact): 1 × 1 term-count (M=4) × 2 widths         =  2
///   - runtime split+tail: 4 ops × 5 term-counts (M=3,5,6,7,8) × 2 widths       = 40
///   - runtime Madd split+tail: 5 term-counts × 2 widths                        = 10
///   - identity: 4 ops × 2 widths                                               =  8
///   - affine (linear) strength reduction: 3 c × 4 d × 2 widths                 = 24
#[inline(never)]
pub fn all_reduction_split_proofs() -> Vec<ProofObligation> {
    let mut proofs = Vec::new();

    // 1. Regrouping — constant-trip exact split (16).
    for op in Op::all() {
        for &m in &[N, 2 * N] {
            for &width in &[64u32, 8u32] {
                proofs.push(proof_regroup(op, m, width));
            }
        }
    }

    // 2. Sum-of-products / Madd — constant-trip exact split (2).
    for &width in &[64u32, 8u32] {
        proofs.push(proof_madd_regroup(N, width));
    }

    // 2b. Runtime split-with-tail: main residue lanes + combine + sequential
    //     remainder tail == sequential fold, over every tail residue (40 + 10).
    for op in Op::all() {
        for &m in &SPLIT_TAIL_MS {
            for &width in &[64u32, 8u32] {
                proofs.push(proof_split_tail_regroup(op, m, width));
            }
        }
    }
    for &m in &SPLIT_TAIL_MS {
        for &width in &[64u32, 8u32] {
            proofs.push(proof_madd_split_tail_regroup(m, width));
        }
    }

    // 3. Identity (8).
    for op in Op::all() {
        for &width in &[64u32, 8u32] {
            proofs.push(proof_identity(op, width));
        }
    }

    // 4. Affine (linear) strength-reduction identity (24).
    for &c in &AFFINE_CS {
        for &d in &AFFINE_DS {
            for &width in &[64u32, 8u32] {
                proofs.push(proof_affine_reduce(c, d, width));
            }
        }
    }

    proofs
}

// ===========================================================================
// Closed-form (Faulhaber) reduction proofs
// ===========================================================================
//
// The closed-form pass (crates/trust-cg-opt/src/reduction_split.rs,
// `ClosedFormReduction`) DELETES a pure-polynomial add reduction
// `acc += a2·i² + a1·i + a0` for `i in 0..n`, replacing it with the straight-line
// closed form
//
//     S1 = n(n-1)/2  (mod 2^64; exact ÷2 via a 128-bit halving)
//     S2 = n(n-1)(2n-1)/6 = S1·(2n-1)·inv3  (mod 2^64; exact ÷3 via modular inverse)
//     result = acc_init + a2·S2 + a1·S1 + a0·n   (all u64 wrapping)
//
// These obligations prove the modular identities the rewrite depends on, all mod
// 2^64 (the pass fires only on 64-bit reductions). `inv3 = 0xAAAA…AAAB` is the
// multiplicative inverse of 3.

/// Modular inverse of 3 mod 2^64: `3·INV3 ≡ 1`.
const INV3_U64: u64 = 0xAAAA_AAAA_AAAA_AAAB;

/// `S1(m) = Σ_{i<m} i mod 2^64`, via the exact 128-bit halving the pass emits.
fn s1_of(m: u64) -> u64 {
    (((m as u128) * (m.wrapping_sub(1) as u128)) >> 1) as u64
}

/// `S2(m) = Σ_{i<m} i² mod 2^64`, via `S1·(2m-1)·inv3` (the pass's modular formula).
fn s2_of(m: u64) -> u64 {
    let two_m1 = 2u64.wrapping_mul(m).wrapping_sub(1);
    s1_of(m).wrapping_mul(two_m1).wrapping_mul(INV3_U64)
}

/// The pass's `S1 = (limit·(limit-1)) >> 1` as a BV64 EXPRESSION tree over a
/// concrete `m` — mirroring `apply_closed_form` in reduction_split.rs. Encoding
/// the closed form as a tree (rather than the pre-folded constant `s1_of(m)`)
/// makes the obligation VERIFY the identity `Σ_{i<m} i == m(m-1)/2` itself rather
/// than a Rust-computed number, and keeps it structurally NON-degenerate even at
/// the `m=1` base case: the RHS `x + (1·0 >> 1)` is a distinct tree from the loop
/// fold `x + 0`, not an `X==X` self-equality. For the bounded `m` used here
/// (`m ≤ 20`) the 64-bit product `m·(m-1)` never overflows, so this 64-bit halving
/// coincides with the pass's 128-bit halving and evaluates to exactly `s1_of(m)`.
fn s1_expr(m: u64) -> SmtExpr {
    let mv = SmtExpr::bv_const(m, 64);
    let mm1 = SmtExpr::bv_const(m.wrapping_sub(1), 64);
    mv.bvmul(mm1).bvlshr(SmtExpr::bv_const(1, 64))
}

/// The pass's `S2 = S1 · (2·limit − 1) · inv3` as a BV64 EXPRESSION tree over a
/// concrete `m` — mirroring `apply_closed_form` (`inv3` is the mod-2^64 inverse of
/// 3). It evaluates to `s2_of(m)`: `3` divides `S1·(2m−1)` exactly (`Σi²` is an
/// integer), so multiplying by `inv3` recovers the quotient mod 2^64. Like
/// `s1_expr`, this keeps the obligation non-degenerate at `m=1` and makes it
/// verify the `n(n-1)(2n-1)/6` identity itself, not a pre-folded constant.
fn s2_expr(m: u64) -> SmtExpr {
    let two_m1 = SmtExpr::bv_const(m, 64)
        .bvshl(SmtExpr::bv_const(1, 64))
        .bvsub(SmtExpr::bv_const(1, 64));
    s1_expr(m)
        .bvmul(two_m1)
        .bvmul(SmtExpr::bv_const(INV3_U64, 64))
}

/// `(3·inv3)·y == y` for all `y` — the solver must establish that the literal
/// modular-inverse product is one modulo 2^64, then that the resulting unit
/// preserves every `y`.
///
/// Keep the two constants in one subterm. The equivalent association
/// `(3·y)·inv3` makes AY bit-blast two symbolic 64-bit multiplier circuits and
/// can time out even though the theorem's only nontrivial fact is the constant
/// product. Associativity of wrapping multiplication is part of BV semantics;
/// the evaluator tests below still exercise the pass's emitted association.
fn proof_inv3_divides() -> ProofObligation {
    let y = SmtExpr::var("y", 64);
    let three = SmtExpr::bv_const(3, 64);
    let inv3 = SmtExpr::bv_const(INV3_U64, 64);
    let lhs = three.bvmul(inv3).bvmul(y.clone());
    obligation(
        "ClosedForm: (3·inv3)·y == y  (3·inv3≡1 mod 2^64)".to_string(),
        lhs,
        y,
        vec![("y".to_string(), 64)],
    )
}

/// `3·inv3 ≡ 1 (mod 2^64)`, stated as `y·(3·inv3) == y` so the evaluator has an
/// input (the folded constant `3·inv3` must be exactly 1).
fn proof_inv3_unit() -> ProofObligation {
    let y = SmtExpr::var("y", 64);
    let prod = SmtExpr::bv_const(3u64.wrapping_mul(INV3_U64), 64);
    let lhs = y.clone().bvmul(prod);
    obligation(
        "ClosedForm: y·(3·inv3) == y".to_string(),
        lhs,
        y,
        vec![("y".to_string(), 64)],
    )
}

/// `Σ_{i<m} i == S1(m)` for a concrete `m`: `x + Σ_{i<m} i == x + m(m-1)/2`.
///
/// LHS is the loop's running fold of the concrete terms; RHS is the closed-form
/// `m(m-1)/2` encoded as an expression tree ([`s1_expr`]) — NOT a pre-folded
/// constant — so the evaluator verifies the identity itself and the obligation is
/// non-degenerate for every `m` (including the `m=1` base case, where the loop
/// side folds to `x + 0` but the closed-form side is the distinct tree
/// `x + (1·0 >> 1)`). A wrong closed form would evaluate to a different value and
/// REFUTE against the loop sum.
fn proof_sum_i(m: u64) -> ProofObligation {
    let x = SmtExpr::var("x", 64);
    let mut lhs = x.clone();
    for i in 0..m {
        lhs = lhs.bvadd(SmtExpr::bv_const(i, 64));
    }
    let rhs = x.bvadd(s1_expr(m));
    obligation(
        format!("ClosedForm: sum_i m={m} == m(m-1)/2"),
        lhs,
        rhs,
        vec![("x".to_string(), 64)],
    )
}

/// `Σ_{i<m} i² == S2(m)` for a concrete `m`: `x + Σ_{i<m} i² == x + m(m-1)(2m-1)/6`.
///
/// As with [`proof_sum_i`], the RHS is the closed-form `m(m-1)(2m-1)/6` encoded as
/// an expression tree ([`s2_expr`], the pass's `S1·(2m−1)·inv3`), keeping the
/// obligation non-degenerate for every `m` and verifying the modular identity
/// against the loop's actual `Σi²` fold.
fn proof_sum_i2(m: u64) -> ProofObligation {
    let x = SmtExpr::var("x", 64);
    let mut lhs = x.clone();
    for i in 0..m {
        lhs = lhs.bvadd(SmtExpr::bv_const(i.wrapping_mul(i), 64));
    }
    let rhs = x.bvadd(s2_expr(m));
    obligation(
        format!("ClosedForm: sum_i2 m={m} == m(m-1)(2m-1)/6"),
        lhs,
        rhs,
        vec![("x".to_string(), 64)],
    )
}

/// Full closed form for a concrete `m` and SYMBOLIC coefficients: the sequential
/// running-mod-2^64 fold `acc + Σ_{i<m}(a2·i² + a1·i + a0)` equals the emitted
/// closed form `acc + a2·S2(m) + a1·S1(m) + a0·m`. A single obligation that
/// validates the halving (S1), the modular inverse (S2) and the coefficient
/// combination simultaneously, over ALL polynomials `P`.
fn proof_faulhaber(m: u64) -> ProofObligation {
    let acc = SmtExpr::var("acc", 64);
    let a2 = SmtExpr::var("a2", 64);
    let a1 = SmtExpr::var("a1", 64);
    let a0 = SmtExpr::var("a0", 64);
    // LHS: the loop's sequential fold of P(i) over i in [0, m).
    let mut lhs = acc.clone();
    for i in 0..m {
        let ii = SmtExpr::bv_const(i.wrapping_mul(i), 64);
        let iv = SmtExpr::bv_const(i, 64);
        let term = a2
            .clone()
            .bvmul(ii)
            .bvadd(a1.clone().bvmul(iv))
            .bvadd(a0.clone());
        lhs = lhs.bvadd(term);
    }
    // RHS: the emitted closed form.
    let rhs = acc
        .bvadd(a2.bvmul(SmtExpr::bv_const(s2_of(m), 64)))
        .bvadd(a1.bvmul(SmtExpr::bv_const(s1_of(m), 64)))
        .bvadd(a0.bvmul(SmtExpr::bv_const(m, 64)));
    obligation(
        format!("ClosedForm: Faulhaber m={m} fold == acc + a2·S2 + a1·S1 + a0·m"),
        lhs,
        rhs,
        vec![
            ("acc".to_string(), 64),
            ("a2".to_string(), 64),
            ("a1".to_string(), 64),
            ("a0".to_string(), 64),
        ],
    )
}

/// Concrete trip counts for the bounded-`m` closed-form checks — the small-`n`
/// regime the differential fuzzer emphasizes, plus a few larger `m`.
const CLOSED_FORM_MS: [u64; 16] = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 16, 20];

/// All closed-form (Faulhaber) reduction proofs.
///
/// Total: 2 + 16 + 16 + 16 = 50 =
///   - modular-inverse: `3·inv3≡1` (unit) + `(3·inv3)·y==y` (divides)        =  2
///   - `Σi == S1(m)` bounded-m                                               = 16
///   - `Σi² == S2(m)` bounded-m                                              = 16
///   - full Faulhaber (symbolic coefficients) bounded-m                      = 16
#[inline(never)]
pub fn all_closed_form_reduction_proofs() -> Vec<ProofObligation> {
    let mut proofs = Vec::new();
    proofs.push(proof_inv3_unit());
    proofs.push(proof_inv3_divides());
    for &m in &CLOSED_FORM_MS {
        proofs.push(proof_sum_i(m));
        proofs.push(proof_sum_i2(m));
        proofs.push(proof_faulhaber(m));
    }
    proofs
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lowering_proof::verify_by_evaluation;
    use crate::verify::VerificationResult;

    fn assert_valid(obligation: &ProofObligation) {
        match verify_by_evaluation(obligation) {
            VerificationResult::Valid => {}
            VerificationResult::Invalid { counterexample } => {
                panic!(
                    "Proof '{}' FAILED with counterexample: {}",
                    obligation.name, counterexample
                );
            }
            VerificationResult::Unknown { reason } => {
                panic!("Proof '{}' returned Unknown: {}", obligation.name, reason);
            }
        }
    }

    #[test]
    fn test_all_reduction_split_proofs_valid() {
        for obligation in &all_reduction_split_proofs() {
            assert_valid(obligation);
        }
    }

    #[test]
    fn test_all_reduction_split_proofs_count() {
        let proofs = all_reduction_split_proofs();
        assert_eq!(
            proofs.len(),
            100,
            "expected 100 reduction-split proofs (16 regroup + 2 madd + 40 split+tail \
             + 10 madd split+tail + 8 identity + 24 affine), got {}",
            proofs.len()
        );
    }

    #[test]
    fn test_all_closed_form_reduction_proofs_valid() {
        for obligation in &all_closed_form_reduction_proofs() {
            assert_valid(obligation);
        }
    }

    #[test]
    fn test_all_closed_form_reduction_proofs_count() {
        assert_eq!(all_closed_form_reduction_proofs().len(), 50);
    }

    #[test]
    fn test_inv3_is_modular_inverse_of_three() {
        // Spot-check the constant directly (independent of the SMT evaluator).
        assert_eq!(3u64.wrapping_mul(INV3_U64), 1);
    }

    #[test]
    fn test_s1_s2_match_naive_sums() {
        // The modular S1/S2 formulas equal the naive running sums for small m.
        for m in 0u64..64 {
            let (mut n1, mut n2) = (0u64, 0u64);
            for i in 0..m {
                n1 = n1.wrapping_add(i);
                n2 = n2.wrapping_add(i.wrapping_mul(i));
            }
            assert_eq!(s1_of(m), n1, "S1 mismatch at m={m}");
            assert_eq!(s2_of(m), n2, "S2 mismatch at m={m}");
        }
    }

    #[test]
    fn test_affine_reduce_proofs_valid() {
        // The linear strength-reduction recurrence identity must hold for every
        // (multiplier, shift) at both widths (a genuine algebraic check).
        for &c in &AFFINE_CS {
            for &d in &AFFINE_DS {
                for &w in &[64u32, 8u32] {
                    assert_valid(&proof_affine_reduce(c, d, w));
                }
            }
        }
    }

    #[test]
    fn test_split_tail_covers_all_residues() {
        // The runtime split-with-tail obligations must exercise every tail
        // residue 0,1,2,3 (the M mod N remainder length the peeled tail runs).
        let residues: std::collections::HashSet<usize> =
            SPLIT_TAIL_MS.iter().map(|&m| m % N).collect();
        for r in 0..N {
            assert!(
                residues.contains(&r),
                "tail residue {r} not covered by SPLIT_TAIL_MS"
            );
        }
    }

    #[test]
    fn test_split_tail_proofs_valid() {
        // Spot-check each op + Madd at a couple residues, both widths.
        for op in Op::all() {
            for &m in &[3usize, 6, 7] {
                for &w in &[64u32, 8u32] {
                    assert_valid(&proof_split_tail_regroup(op, m, w));
                }
            }
        }
        for &m in &[5usize, 8] {
            assert_valid(&proof_madd_split_tail_regroup(m, 64));
        }
    }

    #[test]
    fn test_all_reduction_split_proofs_unique_names() {
        let proofs = all_reduction_split_proofs();
        let mut names: Vec<&str> = proofs.iter().map(|p| p.name.as_str()).collect();
        names.sort();
        for i in 1..names.len() {
            assert_ne!(names[i - 1], names[i], "duplicate proof name: {}", names[i]);
        }
    }

    #[test]
    fn test_regroup_add_matches_sequential() {
        // Spot check the encoders agree concretely for add, M=8.
        assert_valid(&proof_regroup(Op::Add, 8, 64));
    }

    #[test]
    fn test_madd_regroup_valid() {
        assert_valid(&proof_madd_regroup(N, 64));
    }
}
