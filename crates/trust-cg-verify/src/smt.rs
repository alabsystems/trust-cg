// trust-cg-verify/smt.rs - SMT expression AST and bitvector evaluator
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Self-contained SMT expression AST for verification of lowering rules.
// When ay-bindings becomes a direct dependency, these types will serialize
// to the ay Expr/Sort API. Until then, we evaluate locally using Rust
// wrapping arithmetic (two's complement bitvector semantics).

//! SMT bitvector expression AST and concrete evaluator.
//!
//! This module defines a lightweight expression tree for bitvector operations
//! matching SMT-LIB2 QF_BV semantics. Expressions can be:
//!
//! 1. **Symbolically constructed** to describe proof obligations
//! 2. **Concretely evaluated** via [`SmtExpr::eval`] for testing/verification

use std::collections::HashMap;
use std::fmt;
use std::sync::Arc;
use thiserror::Error;
use trust_cg_lower::types::Type;

/// The variable environment for the hot proof-evaluation sampling loop, backed by
/// a tiny LINEAR-SCAN map. `verify_by_evaluation` walks each obligation at up to
/// 100k sample points per instruction, and a real proof obligation has only a
/// handful of free variables (typically 1–3: `base`, `value`, `shift`, …). For so
/// few keys a linear scan over a `Vec` is faster than ANY hashed map — there is no
/// hash to compute at all — which is why this replaced the `HashMap` env (the
/// per-`Var` hashing was co-dominant with the eval tree-walk in profiles). It
/// exposes the same `default/insert/get/get_mut/contains_key` surface the sampler
/// already used, so the sampling code is unchanged. VERDICT-PRESERVING: `get_var`
/// returns exactly the value a `HashMap` would; only the lookup mechanism differs.
#[derive(Default, Clone, Debug)]
pub struct EvalEnv {
    vars: Vec<(String, u64)>,
}

impl EvalEnv {
    #[inline]
    pub fn insert(&mut self, key: String, val: u64) -> Option<u64> {
        for (name, slot) in &mut self.vars {
            if *name == key {
                let old = *slot;
                *slot = val;
                return Some(old);
            }
        }
        self.vars.push((key, val));
        None
    }
    #[inline]
    pub fn get(&self, key: &str) -> Option<&u64> {
        self.vars
            .iter()
            .find(|(name, _)| name == key)
            .map(|(_, v)| v)
    }
    #[inline]
    pub fn get_mut(&mut self, key: &str) -> Option<&mut u64> {
        self.vars
            .iter_mut()
            .find(|(name, _)| name == key)
            .map(|(_, v)| v)
    }
    #[inline]
    pub fn contains_key(&self, key: &str) -> bool {
        self.vars.iter().any(|(name, _)| name == key)
    }
    /// The value at insertion slot `slot`. Keys are inserted in a fixed order on
    /// the sampling path, so the compiled evaluator resolves each `Var` to its
    /// slot once at compile time and reads it here without the name scan.
    #[inline]
    pub fn value_at(&self, slot: usize) -> u64 {
        self.vars[slot].1
    }

    /// Overwrite the value at insertion slot `slot`, leaving the key untouched.
    ///
    /// The exhaustive enumerator binds the SAME variable names at every one of
    /// its up to 2^16 points. Rebuilding the environment per point meant a fresh
    /// allocation plus a `String` clone per input per point; with the keys fixed
    /// after the first bind, only the values need to change.
    #[inline]
    pub fn set_at(&mut self, slot: usize, val: u64) {
        self.vars[slot].1 = val;
    }
}

/// The operations `SmtExpr::try_eval` needs from a variable environment: read a
/// variable's value, and (for bounded-quantifier expansion) clone + bind a fresh
/// variable. Implemented for both the hot-path [`EvalEnv`] (linear scan) and the
/// `String`-keyed `HashMap` the rest of the crate / external callers pass, so the
/// public `eval`/`try_eval` stay generic and no caller is disturbed.
pub trait EnvOps: Clone {
    fn get_var(&self, name: &str) -> Option<u64>;
    fn set_var(&mut self, name: String, val: u64);
}

impl EnvOps for EvalEnv {
    #[inline]
    fn get_var(&self, name: &str) -> Option<u64> {
        self.get(name).copied()
    }
    #[inline]
    fn set_var(&mut self, name: String, val: u64) {
        self.insert(name, val);
    }
}

impl<S: std::hash::BuildHasher + Clone> EnvOps for HashMap<String, u64, S> {
    #[inline]
    fn get_var(&self, name: &str) -> Option<u64> {
        self.get(name).copied()
    }
    #[inline]
    fn set_var(&mut self, name: String, val: u64) {
        self.insert(name, val);
    }
}

/// A compiled, index-resolved form of the **≤64-bit scalar subset** of `SmtExpr`,
/// for the hot `verify_by_evaluation` sampling loop. Each `Var` is resolved to an
/// env slot ONCE at compile time, so evaluation does no name hashing/scan and no
/// `SmtExpr` tree re-match (the two co-dominant per-sample costs in profiles).
///
/// SOUNDNESS: [`CExpr::compile`] returns `None` for anything outside the subset
/// (div/rem/trap, arrays/memory, FP, UF, quantifiers, any width > 64, or a `Var`
/// not found in `inputs`), and the caller FALLS BACK to `SmtExpr::try_eval`. So
/// the compiled path can only ever be a faster way to compute *exactly* what
/// `try_eval` would, and a property test (`compiled_matches_interpreter`)
/// cross-checks `CExpr::eval == SmtExpr::try_eval` over every DB obligation ×
/// many random + edge inputs. Each arm mirrors the corresponding ≤64-bit
/// `try_eval` arm byte-for-byte.
pub enum CExpr {
    Const(u64), // Bv, already width-masked
    BoolConst(bool),
    Var(usize, u32), // (slot, width)
    Add(Box<CExpr>, Box<CExpr>, u32),
    Sub(Box<CExpr>, Box<CExpr>, u32),
    Mul(Box<CExpr>, Box<CExpr>, u32),
    And(Box<CExpr>, Box<CExpr>, u32),
    Or(Box<CExpr>, Box<CExpr>, u32),
    Xor(Box<CExpr>, Box<CExpr>, u32),
    Shl(Box<CExpr>, Box<CExpr>, u32),
    Lshr(Box<CExpr>, Box<CExpr>, u32),
    Ashr(Box<CExpr>, Box<CExpr>, u32),
    Neg(Box<CExpr>, u32),
    Eq(Box<CExpr>, Box<CExpr>),
    LogicalNot(Box<CExpr>),
    Slt(Box<CExpr>, Box<CExpr>, u32),
    Sge(Box<CExpr>, Box<CExpr>, u32),
    Uge(Box<CExpr>, Box<CExpr>),
    Sgt(Box<CExpr>, Box<CExpr>, u32),
    Sle(Box<CExpr>, Box<CExpr>, u32),
    Ult(Box<CExpr>, Box<CExpr>),
    Ugt(Box<CExpr>, Box<CExpr>),
    Ule(Box<CExpr>, Box<CExpr>),
    LogicalAnd(Box<CExpr>, Box<CExpr>),
    LogicalOr(Box<CExpr>, Box<CExpr>),
    Ite(Box<CExpr>, Box<CExpr>, Box<CExpr>),
    Extract(Box<CExpr>, u32 /*low*/, u32 /*width*/),
    Concat(
        Box<CExpr>,
        Box<CExpr>,
        u32, /*lo_width*/
        u32, /*width*/
    ),
    ZExt(Box<CExpr>, u32 /*width*/),
    SExt(Box<CExpr>, u32 /*src_width*/, u32 /*width*/),
}

impl CExpr {
    /// Compile `expr` into the indexed scalar form, resolving each `Var` against
    /// `inputs` (its name -> slot). Returns `None` for any unsupported op/width or
    /// an out-of-`inputs` variable (caller falls back to `try_eval`).
    pub fn compile(expr: &SmtExpr, inputs: &[(String, u32)]) -> Option<CExpr> {
        let c = |e: &SmtExpr| CExpr::compile(e, inputs).map(Box::new);
        Some(match expr {
            SmtExpr::Var { name, width } if *width <= 64 => {
                let slot = inputs.iter().position(|(n, _)| n == name)?;
                CExpr::Var(slot, *width)
            }
            SmtExpr::BvConst { value, width } if *width <= 64 => CExpr::Const(mask(*value, *width)),
            SmtExpr::BoolConst(b) => CExpr::BoolConst(*b),
            SmtExpr::BvAdd { lhs, rhs, width } if *width <= 64 => {
                CExpr::Add(c(lhs)?, c(rhs)?, *width)
            }
            SmtExpr::BvSub { lhs, rhs, width } if *width <= 64 => {
                CExpr::Sub(c(lhs)?, c(rhs)?, *width)
            }
            SmtExpr::BvMul { lhs, rhs, width } if *width <= 64 => {
                CExpr::Mul(c(lhs)?, c(rhs)?, *width)
            }
            SmtExpr::BvAnd { lhs, rhs, width } if *width <= 64 => {
                CExpr::And(c(lhs)?, c(rhs)?, *width)
            }
            SmtExpr::BvOr { lhs, rhs, width } if *width <= 64 => {
                CExpr::Or(c(lhs)?, c(rhs)?, *width)
            }
            SmtExpr::BvXor { lhs, rhs, width } if *width <= 64 => {
                CExpr::Xor(c(lhs)?, c(rhs)?, *width)
            }
            SmtExpr::BvShl { lhs, rhs, width } if *width <= 64 => {
                CExpr::Shl(c(lhs)?, c(rhs)?, *width)
            }
            SmtExpr::BvLshr { lhs, rhs, width } if *width <= 64 => {
                CExpr::Lshr(c(lhs)?, c(rhs)?, *width)
            }
            SmtExpr::BvAshr { lhs, rhs, width } if *width <= 64 => {
                CExpr::Ashr(c(lhs)?, c(rhs)?, *width)
            }
            SmtExpr::BvNeg { operand, width } if *width <= 64 => CExpr::Neg(c(operand)?, *width),
            SmtExpr::Eq { lhs, rhs } => CExpr::Eq(c(lhs)?, c(rhs)?),
            SmtExpr::Not { operand } => CExpr::LogicalNot(c(operand)?),
            SmtExpr::BvSlt { lhs, rhs, width } if *width <= 64 => {
                CExpr::Slt(c(lhs)?, c(rhs)?, *width)
            }
            SmtExpr::BvSge { lhs, rhs, width } if *width <= 64 => {
                CExpr::Sge(c(lhs)?, c(rhs)?, *width)
            }
            SmtExpr::BvUge { lhs, rhs, .. } => CExpr::Uge(c(lhs)?, c(rhs)?),
            SmtExpr::BvSgt { lhs, rhs, width } if *width <= 64 => {
                CExpr::Sgt(c(lhs)?, c(rhs)?, *width)
            }
            SmtExpr::BvSle { lhs, rhs, width } if *width <= 64 => {
                CExpr::Sle(c(lhs)?, c(rhs)?, *width)
            }
            SmtExpr::BvUlt { lhs, rhs, .. } => CExpr::Ult(c(lhs)?, c(rhs)?),
            SmtExpr::BvUgt { lhs, rhs, .. } => CExpr::Ugt(c(lhs)?, c(rhs)?),
            SmtExpr::BvUle { lhs, rhs, .. } => CExpr::Ule(c(lhs)?, c(rhs)?),
            SmtExpr::And { lhs, rhs } => CExpr::LogicalAnd(c(lhs)?, c(rhs)?),
            SmtExpr::Or { lhs, rhs } => CExpr::LogicalOr(c(lhs)?, c(rhs)?),
            SmtExpr::Ite {
                cond,
                then_expr,
                else_expr,
            } => CExpr::Ite(c(cond)?, c(then_expr)?, c(else_expr)?),
            SmtExpr::Extract {
                low,
                operand,
                width,
                ..
            } if *width <= 64 => CExpr::Extract(c(operand)?, *low, *width),
            SmtExpr::Concat { hi, lo, width } if *width <= 64 => {
                CExpr::Concat(c(hi)?, c(lo)?, lo.bv_width(), *width)
            }
            SmtExpr::ZeroExtend { operand, width, .. } if *width <= 64 => {
                CExpr::ZExt(c(operand)?, *width)
            }
            SmtExpr::SignExtend {
                operand,
                extra_bits,
                width,
            } if *width <= 64 => CExpr::SExt(c(operand)?, *width - *extra_bits, *width),
            // Anything else (div/rem/trap, arrays/memory, FP, UF, quantifiers,
            // any width > 64) is out of subset -> fall back to `try_eval`.
            _ => return None,
        })
    }

    /// Evaluate against an [`EvalEnv`] whose values are at the slots `compile`
    /// resolved. Each arm mirrors the corresponding ≤64-bit `SmtExpr::try_eval`
    /// arm exactly. Returns `EvalResult::Bv` / `EvalResult::Bool`.
    pub fn eval(&self, env: &EvalEnv) -> EvalResult {
        use CExpr::*;
        match self {
            Const(v) => EvalResult::Bv(*v),
            BoolConst(b) => EvalResult::Bool(*b),
            Var(slot, width) => EvalResult::Bv(mask(env.value_at(*slot), *width)),
            Add(a, b, w) => EvalResult::Bv(mask(
                a.eval(env).as_u64().wrapping_add(b.eval(env).as_u64()),
                *w,
            )),
            Sub(a, b, w) => EvalResult::Bv(mask(
                a.eval(env).as_u64().wrapping_sub(b.eval(env).as_u64()),
                *w,
            )),
            Mul(a, b, w) => EvalResult::Bv(mask(
                a.eval(env).as_u64().wrapping_mul(b.eval(env).as_u64()),
                *w,
            )),
            And(a, b, w) => EvalResult::Bv(mask(a.eval(env).as_u64() & b.eval(env).as_u64(), *w)),
            Or(a, b, w) => EvalResult::Bv(mask(a.eval(env).as_u64() | b.eval(env).as_u64(), *w)),
            Xor(a, b, w) => EvalResult::Bv(mask(a.eval(env).as_u64() ^ b.eval(env).as_u64(), *w)),
            Shl(a, b, w) => {
                let av = a.eval(env).as_u64();
                let bv = b.eval(env).as_u64();
                if bv >= *w as u64 {
                    EvalResult::Bv(0)
                } else {
                    EvalResult::Bv(mask(av << bv, *w))
                }
            }
            Lshr(a, b, w) => {
                let av = a.eval(env).as_u64();
                let bv = b.eval(env).as_u64();
                if bv >= *w as u64 {
                    EvalResult::Bv(0)
                } else {
                    EvalResult::Bv(mask(av >> bv, *w))
                }
            }
            Ashr(a, b, w) => {
                let av = sign_extend(a.eval(env).as_u64(), *w);
                let bv = b.eval(env).as_u64();
                if bv >= *w as u64 {
                    if av < 0 {
                        EvalResult::Bv(mask(u64::MAX, *w))
                    } else {
                        EvalResult::Bv(0)
                    }
                } else {
                    EvalResult::Bv(mask((av >> bv) as u64, *w))
                }
            }
            Neg(a, w) => EvalResult::Bv(mask((!a.eval(env).as_u64()).wrapping_add(1), *w)),
            Eq(a, b) => EvalResult::Bool(a.eval(env) == b.eval(env)),
            LogicalNot(a) => EvalResult::Bool(!a.eval(env).as_bool()),
            Slt(a, b, w) => EvalResult::Bool(
                sign_extend(a.eval(env).as_u64(), *w) < sign_extend(b.eval(env).as_u64(), *w),
            ),
            Sge(a, b, w) => EvalResult::Bool(
                sign_extend(a.eval(env).as_u64(), *w) >= sign_extend(b.eval(env).as_u64(), *w),
            ),
            Uge(a, b) => EvalResult::Bool(a.eval(env).as_u64() >= b.eval(env).as_u64()),
            Sgt(a, b, w) => EvalResult::Bool(
                sign_extend(a.eval(env).as_u64(), *w) > sign_extend(b.eval(env).as_u64(), *w),
            ),
            Sle(a, b, w) => EvalResult::Bool(
                sign_extend(a.eval(env).as_u64(), *w) <= sign_extend(b.eval(env).as_u64(), *w),
            ),
            Ult(a, b) => EvalResult::Bool(a.eval(env).as_u64() < b.eval(env).as_u64()),
            Ugt(a, b) => EvalResult::Bool(a.eval(env).as_u64() > b.eval(env).as_u64()),
            Ule(a, b) => EvalResult::Bool(a.eval(env).as_u64() <= b.eval(env).as_u64()),
            LogicalAnd(a, b) => EvalResult::Bool(a.eval(env).as_bool() && b.eval(env).as_bool()),
            LogicalOr(a, b) => EvalResult::Bool(a.eval(env).as_bool() || b.eval(env).as_bool()),
            Ite(cond, then_e, else_e) => {
                if cond.eval(env).as_bool() {
                    then_e.eval(env)
                } else {
                    else_e.eval(env)
                }
            }
            Extract(op, low, width) => {
                let v = op.eval(env).as_u64() as u128;
                EvalResult::Bv(((v >> low) & mask128(u128::MAX, *width)) as u64)
            }
            Concat(hi, lo, lo_width, width) => {
                let hv = hi.eval(env).as_u64() as u128;
                let lv = lo.eval(env).as_u64() as u128;
                EvalResult::Bv(mask128((hv << lo_width) | lv, *width) as u64)
            }
            ZExt(op, width) => EvalResult::Bv(mask(op.eval(env).as_u64(), *width)),
            SExt(op, src_width, width) => EvalResult::Bv(mask(
                sign_extend(op.eval(env).as_u64(), *src_width) as u64,
                *width,
            )),
        }
    }
}

// ---------------------------------------------------------------------------
// FlatProg — the compile-once LINEAR TAPE eval-tier fast path (division subset)
// ---------------------------------------------------------------------------

/// A compact, `Copy` scalar value carried by the [`FlatProg`] tape. It mirrors
/// [`EvalResult`] for EXACTLY the four variants an integer / division proof
/// obligation can ever produce (`Bv`/`Bv128`/`Bool`/`Poison`); it deliberately
/// OMITS the fat `Float` and `Array` variants (the latter holds a `HashMap`), so
/// a tape slot is a small `Copy` value rather than a heap-carrying enum.
///
/// SOUNDNESS: the projections below are copied BYTE-FOR-BYTE from the matching
/// [`EvalResult`] projections (`as_u64`/`as_u128`/`as_bool`, smt.rs) restricted
/// to these four variants, and `SVal` DERIVES `PartialEq` so an intermediate
/// [`FlatOp::Eq`] node compares two `SVal`s exactly as the interpreter compares
/// two `EvalResult`s with its derived `==` (cross-variant `Bv` vs `Bv128` are
/// UNEQUAL even when numerically equal; `Poison == Poison` is `true`). The ROOT
/// verdict is still decided by the unchanged [`EvalResult::semantically_equal`]
/// after [`SVal::to_eval`] (where `Poison != everything`).
#[derive(Clone, Copy, PartialEq, Debug)]
pub enum SVal {
    Bv(u64),
    Bv128(u128),
    Bool(bool),
    Poison,
}

impl SVal {
    #[inline]
    fn as_u64(self) -> u64 {
        match self {
            SVal::Bv(v) => v,
            SVal::Bv128(v) => v as u64,
            SVal::Bool(b) => b as u64,
            SVal::Poison => u64::MAX,
        }
    }
    #[inline]
    fn as_u128(self) -> u128 {
        match self {
            SVal::Bv(v) => v as u128,
            SVal::Bv128(v) => v,
            SVal::Bool(b) => b as u128,
            SVal::Poison => u128::MAX,
        }
    }
    #[inline]
    fn as_bool(self) -> bool {
        match self {
            SVal::Bool(b) => b,
            SVal::Bv(v) => v != 0,
            SVal::Bv128(v) => v != 0,
            SVal::Poison => false,
        }
    }
    #[inline]
    fn to_eval(self) -> EvalResult {
        match self {
            SVal::Bv(v) => EvalResult::Bv(v),
            SVal::Bv128(v) => EvalResult::Bv128(v),
            SVal::Bool(b) => EvalResult::Bool(b),
            SVal::Poison => EvalResult::Poison,
        }
    }
}

/// One node of a [`FlatProg`] tape. Operands are `usize` indices into the
/// EARLIER part of the tape (topological order guarantees they are already
/// evaluated), so evaluation is a straight-line pass with no recursion, no
/// `Box` deref, and no per-sample `SmtExpr` re-match. `Hash`/`Eq` back the
/// hash-cons dedup that collapses shared subexpressions to a single slot.
#[derive(Hash, PartialEq, Eq, Clone, Copy)]
enum FlatOp {
    Const(u64),
    Const128(u128),
    BoolConst(bool),
    Var(usize, u32),
    Add(usize, usize, u32),
    Sub(usize, usize, u32),
    Mul(usize, usize, u32),
    And(usize, usize, u32),
    Or(usize, usize, u32),
    Xor(usize, usize, u32),
    Shl(usize, usize, u32),
    Lshr(usize, usize, u32),
    Ashr(usize, usize, u32),
    SDiv(usize, usize, u32),
    UDiv(usize, usize, u32),
    URem(usize, usize, u32),
    Neg(usize, u32),
    Trap(usize /*guard*/, usize /*value*/),
    Eq(usize, usize),
    Not(usize),
    Slt(usize, usize, u32),
    Sge(usize, usize, u32),
    Uge(usize, usize),
    Sgt(usize, usize, u32),
    Sle(usize, usize, u32),
    Ult(usize, usize),
    Ugt(usize, usize),
    Ule(usize, usize),
    BAnd(usize, usize),
    BOr(usize, usize),
    Ite(usize, usize, usize),
    Extract(usize, u32 /*low*/, u32 /*width*/),
    Concat(usize, usize, u32 /*lo_width*/, u32 /*width*/),
    ZExt(usize, u32 /*width*/),
    SExt(usize, u32 /*src_width*/, u32 /*width*/),
    MemLoad(
        usize, /* address */
        u32,   /* load width */
        bool,  /* signed */
        u32,   /* result width */
    ),
}

/// A compiled, hash-consed, topologically-ordered LINEAR TAPE form of the
/// integer/bitvector subset of [`SmtExpr`] — the eval-tier fast path for the hot
/// `verify_by_evaluation` sampling loop, EXTENDED past [`CExpr`] to cover the
/// DIVISION subset (`bvsdiv`/`bvudiv`/`bvurem`, [`SmtExpr::TrapIfZero`], and EVERY
/// op at width > 64) and scalar reads from finite store chains that `CExpr`
/// excludes and that otherwise pay the fully-interpreted `SmtExpr::try_eval`
/// tax on every one of ~100k samples.
///
/// # Soundness
///
/// [`FlatProg::compile`] is ALL-OR-NOTHING: it returns `None` for ANY node
/// outside the total, pure integer subset (all FP, general arrays, `UF`/`UFDecl`,
/// `ForAll`/`Exists`, and — defensively — `bvurem` at width > 64, which
/// `trust_ir` never emits), and the caller FALLS BACK to the interpreter, exactly
/// as with `CExpr`. A scalar `select` over `store`/`ite`/`const-array` is compiled
/// by the read-over-write identity into ordinary `Eq`/`Ite` tape nodes; no array
/// value or per-sample map allocation enters the tape. When compilation succeeds,
/// every arm
/// of [`FlatProg::eval`] is a 1:1 transcription of the corresponding
/// `SmtExpr::try_eval` arm (same module-private helpers `mask`/`mask128`/
/// `sign_extend`/`sign_extend128`, same `> 64` vs `<= 64` branch, same div-by-zero
/// sentinels and `INT_MIN / -1` overflow gates), so the tape computes EXACTLY what
/// the interpreter would — proven arm-for-arm by the differential property test
/// [`flatprog_matches_interpreter_differential_fuzz`] over the reconstructed x86
/// division obligations (all widths × signedness, incl. divisor=0 trap and
/// `INT_MIN/-1` overflow), scalarized store/select memory expressions, and random
/// subset expressions.
///
/// EAGER-EVAL SAFETY: the tape evaluates ALL operands (no `try_eval`
/// short-circuit of `Ite`/`And`/`Or`/`Trap`). This is verdict-identical because
/// every subset op is TOTAL and PURE — div-by-zero returns a defined sentinel,
/// shifts are guarded by `>= width -> 0`, extract/concat use `u128` — so an
/// eagerly-computed sub-result that a guard/branch does not select is simply
/// discarded, never observed. The whitelist in `compile` is what guarantees the
/// totality: a general array `Select` that could error is EXCLUDED, while the
/// accepted const/store/ite read is reduced completely to scalar operations.
pub struct FlatProg {
    ops: Vec<FlatOp>,
    root: usize,
}

impl FlatProg {
    /// Compile `expr` into the linear tape, resolving each `Var` to its `inputs`
    /// slot and hash-consing shared subexpressions. Returns `None` (caller falls
    /// back to `try_eval`) for any out-of-subset node or a `Var` absent from
    /// `inputs`.
    pub fn compile(expr: &SmtExpr, inputs: &[(String, u32)]) -> Option<FlatProg> {
        let mut ops: Vec<FlatOp> = Vec::new();
        let mut dedup: HashMap<FlatOp, usize> = HashMap::new();
        let root = Self::go(expr, inputs, &mut ops, &mut dedup)?;
        Some(FlatProg { ops, root })
    }

    /// Hash-cons `op`: return its existing slot if an identical node was already
    /// emitted, else push it and record the slot. Because children are emitted
    /// bottom-up, two structurally-equal subtrees produce the SAME `FlatOp` (same
    /// child slots) and collapse to one slot — materializing the DAG.
    #[inline]
    fn push(ops: &mut Vec<FlatOp>, dedup: &mut HashMap<FlatOp, usize>, op: FlatOp) -> usize {
        if let Some(&i) = dedup.get(&op) {
            return i;
        }
        let i = ops.len();
        ops.push(op);
        dedup.insert(op, i);
        i
    }

    fn go(
        e: &SmtExpr,
        inputs: &[(String, u32)],
        ops: &mut Vec<FlatOp>,
        dedup: &mut HashMap<FlatOp, usize>,
    ) -> Option<usize> {
        // One arm per in-subset variant; children are compiled to slots FIRST
        // (guaranteeing topological order), then this node is hash-consed.
        // Every not-listed variant (all FP, Select/Store/ConstArray/MemLoad,
        // UF/UFDecl, ForAll/Exists) falls through to `_ => return None`.
        let op = match e {
            SmtExpr::Var { name, width } => {
                let slot = inputs.iter().position(|(n, _)| n == name)?;
                FlatOp::Var(slot, *width)
            }
            SmtExpr::BvConst { value, width } => {
                // Mirror try_eval: width > 64 -> a 128-bit constant.
                if *width > 64 {
                    FlatOp::Const128(*value as u128)
                } else {
                    FlatOp::Const(mask(*value, *width))
                }
            }
            SmtExpr::BoolConst(b) => FlatOp::BoolConst(*b),
            SmtExpr::BvAdd { lhs, rhs, width } => {
                let a = Self::go(lhs, inputs, ops, dedup)?;
                let b = Self::go(rhs, inputs, ops, dedup)?;
                FlatOp::Add(a, b, *width)
            }
            SmtExpr::BvSub { lhs, rhs, width } => {
                let a = Self::go(lhs, inputs, ops, dedup)?;
                let b = Self::go(rhs, inputs, ops, dedup)?;
                FlatOp::Sub(a, b, *width)
            }
            SmtExpr::BvMul { lhs, rhs, width } => {
                let a = Self::go(lhs, inputs, ops, dedup)?;
                let b = Self::go(rhs, inputs, ops, dedup)?;
                FlatOp::Mul(a, b, *width)
            }
            SmtExpr::BvAnd { lhs, rhs, width } => {
                let a = Self::go(lhs, inputs, ops, dedup)?;
                let b = Self::go(rhs, inputs, ops, dedup)?;
                FlatOp::And(a, b, *width)
            }
            SmtExpr::BvOr { lhs, rhs, width } => {
                let a = Self::go(lhs, inputs, ops, dedup)?;
                let b = Self::go(rhs, inputs, ops, dedup)?;
                FlatOp::Or(a, b, *width)
            }
            SmtExpr::BvXor { lhs, rhs, width } => {
                let a = Self::go(lhs, inputs, ops, dedup)?;
                let b = Self::go(rhs, inputs, ops, dedup)?;
                FlatOp::Xor(a, b, *width)
            }
            SmtExpr::BvShl { lhs, rhs, width } => {
                let a = Self::go(lhs, inputs, ops, dedup)?;
                let b = Self::go(rhs, inputs, ops, dedup)?;
                FlatOp::Shl(a, b, *width)
            }
            SmtExpr::BvLshr { lhs, rhs, width } => {
                let a = Self::go(lhs, inputs, ops, dedup)?;
                let b = Self::go(rhs, inputs, ops, dedup)?;
                FlatOp::Lshr(a, b, *width)
            }
            SmtExpr::BvAshr { lhs, rhs, width } => {
                let a = Self::go(lhs, inputs, ops, dedup)?;
                let b = Self::go(rhs, inputs, ops, dedup)?;
                FlatOp::Ashr(a, b, *width)
            }
            SmtExpr::BvSDiv { lhs, rhs, width } => {
                let a = Self::go(lhs, inputs, ops, dedup)?;
                let b = Self::go(rhs, inputs, ops, dedup)?;
                FlatOp::SDiv(a, b, *width)
            }
            SmtExpr::BvUDiv { lhs, rhs, width } => {
                let a = Self::go(lhs, inputs, ops, dedup)?;
                let b = Self::go(rhs, inputs, ops, dedup)?;
                FlatOp::UDiv(a, b, *width)
            }
            SmtExpr::BvURem { lhs, rhs, width } => {
                // try_eval's BvURem has NO width > 64 branch (always u64). Rather
                // than transcribe a lossy >64 path, fail closed for width > 64 so
                // the whole obligation routes to the interpreter. trust_ir composes
                // Urem as `a - udiv*b` and never emits a bare bvurem, so this is
                // purely defensive.
                if *width > 64 {
                    return None;
                }
                let a = Self::go(lhs, inputs, ops, dedup)?;
                let b = Self::go(rhs, inputs, ops, dedup)?;
                FlatOp::URem(a, b, *width)
            }
            SmtExpr::TrapIfZero { guard, value, .. } => {
                let g = Self::go(guard, inputs, ops, dedup)?;
                let v = Self::go(value, inputs, ops, dedup)?;
                FlatOp::Trap(g, v)
            }
            SmtExpr::BvNeg { operand, width } => {
                let o = Self::go(operand, inputs, ops, dedup)?;
                FlatOp::Neg(o, *width)
            }
            SmtExpr::Eq { lhs, rhs } => {
                let a = Self::go(lhs, inputs, ops, dedup)?;
                let b = Self::go(rhs, inputs, ops, dedup)?;
                FlatOp::Eq(a, b)
            }
            SmtExpr::Not { operand } => {
                let o = Self::go(operand, inputs, ops, dedup)?;
                FlatOp::Not(o)
            }
            SmtExpr::BvSlt { lhs, rhs, width } => {
                let a = Self::go(lhs, inputs, ops, dedup)?;
                let b = Self::go(rhs, inputs, ops, dedup)?;
                FlatOp::Slt(a, b, *width)
            }
            SmtExpr::BvSge { lhs, rhs, width } => {
                let a = Self::go(lhs, inputs, ops, dedup)?;
                let b = Self::go(rhs, inputs, ops, dedup)?;
                FlatOp::Sge(a, b, *width)
            }
            SmtExpr::BvUge { lhs, rhs, .. } => {
                let a = Self::go(lhs, inputs, ops, dedup)?;
                let b = Self::go(rhs, inputs, ops, dedup)?;
                FlatOp::Uge(a, b)
            }
            SmtExpr::BvSgt { lhs, rhs, width } => {
                let a = Self::go(lhs, inputs, ops, dedup)?;
                let b = Self::go(rhs, inputs, ops, dedup)?;
                FlatOp::Sgt(a, b, *width)
            }
            SmtExpr::BvSle { lhs, rhs, width } => {
                let a = Self::go(lhs, inputs, ops, dedup)?;
                let b = Self::go(rhs, inputs, ops, dedup)?;
                FlatOp::Sle(a, b, *width)
            }
            SmtExpr::BvUlt { lhs, rhs, .. } => {
                let a = Self::go(lhs, inputs, ops, dedup)?;
                let b = Self::go(rhs, inputs, ops, dedup)?;
                FlatOp::Ult(a, b)
            }
            SmtExpr::BvUgt { lhs, rhs, .. } => {
                let a = Self::go(lhs, inputs, ops, dedup)?;
                let b = Self::go(rhs, inputs, ops, dedup)?;
                FlatOp::Ugt(a, b)
            }
            SmtExpr::BvUle { lhs, rhs, .. } => {
                let a = Self::go(lhs, inputs, ops, dedup)?;
                let b = Self::go(rhs, inputs, ops, dedup)?;
                FlatOp::Ule(a, b)
            }
            SmtExpr::And { lhs, rhs } => {
                let a = Self::go(lhs, inputs, ops, dedup)?;
                let b = Self::go(rhs, inputs, ops, dedup)?;
                FlatOp::BAnd(a, b)
            }
            SmtExpr::Or { lhs, rhs } => {
                let a = Self::go(lhs, inputs, ops, dedup)?;
                let b = Self::go(rhs, inputs, ops, dedup)?;
                FlatOp::BOr(a, b)
            }
            SmtExpr::Ite {
                cond,
                then_expr,
                else_expr,
            } => {
                let c = Self::go(cond, inputs, ops, dedup)?;
                let t = Self::go(then_expr, inputs, ops, dedup)?;
                let el = Self::go(else_expr, inputs, ops, dedup)?;
                FlatOp::Ite(c, t, el)
            }
            SmtExpr::Extract {
                low,
                operand,
                width,
                ..
            } => {
                let o = Self::go(operand, inputs, ops, dedup)?;
                FlatOp::Extract(o, *low, *width)
            }
            SmtExpr::Concat { hi, lo, width } => {
                // lo_width is structural (matches try_eval's `lo.bv_width()`).
                let lo_width = lo.bv_width();
                let h = Self::go(hi, inputs, ops, dedup)?;
                let l = Self::go(lo, inputs, ops, dedup)?;
                FlatOp::Concat(h, l, lo_width, *width)
            }
            SmtExpr::ZeroExtend { operand, width, .. } => {
                let o = Self::go(operand, inputs, ops, dedup)?;
                FlatOp::ZExt(o, *width)
            }
            SmtExpr::SignExtend {
                operand,
                extra_bits,
                width,
            } => {
                let o = Self::go(operand, inputs, ops, dedup)?;
                FlatOp::SExt(o, *width - *extra_bits, *width)
            }
            SmtExpr::Select { array, index } => {
                // The concrete evaluator keys arrays by the selected index's
                // low u64. Restrict this fast path to the real memory-model
                // surface (<=64-bit indices), where ordinary bitvector equality
                // is exactly that key equality. Wider or exotic arrays retain
                // the interpreter path unchanged.
                if index.bv_width() > 64 {
                    return None;
                }
                let selected_index = Self::go(index, inputs, ops, dedup)?;
                return Self::go_select(array, selected_index, inputs, ops, dedup);
            }
            SmtExpr::MemLoad {
                addr,
                load_bits,
                signed,
                result_width,
            } => {
                let address = Self::go(addr, inputs, ops, dedup)?;
                FlatOp::MemLoad(address, *load_bits, *signed, *result_width)
            }
            // Out of subset (all FP, a Store/ConstArray not consumed by Select,
            // general arrays, UF/UFDecl, ForAll/Exists) -> interpreter fallback.
            _ => return None,
        };
        Some(Self::push(ops, dedup, op))
    }

    /// Compile a scalar `select(array, selected_index)` without materializing an
    /// array value. This is the McCarthy read-over-write rule:
    ///
    /// `select(store(a, i, v), j) = ite(i == j, v, select(a, j))`.
    ///
    /// Array-valued `ite` is distributed over the read and a constant array
    /// yields its default. The resulting tape remains scalar, total, and pure,
    /// so the eager-evaluation argument for [`FlatProg`] still applies. Any
    /// other array producer fails compilation and preserves interpreter fallback.
    fn go_select(
        array: &SmtExpr,
        selected_index: usize,
        inputs: &[(String, u32)],
        ops: &mut Vec<FlatOp>,
        dedup: &mut HashMap<FlatOp, usize>,
    ) -> Option<usize> {
        match array {
            SmtExpr::ConstArray { value, .. } => Self::go(value, inputs, ops, dedup),
            SmtExpr::Store {
                array,
                index,
                value,
            } => {
                if index.bv_width() > 64 {
                    return None;
                }
                let store_index = Self::go(index, inputs, ops, dedup)?;
                let stored_value = Self::go(value, inputs, ops, dedup)?;
                let prior_value = Self::go_select(array, selected_index, inputs, ops, dedup)?;
                let same_index = Self::push(ops, dedup, FlatOp::Eq(store_index, selected_index));
                Some(Self::push(
                    ops,
                    dedup,
                    FlatOp::Ite(same_index, stored_value, prior_value),
                ))
            }
            SmtExpr::Ite {
                cond,
                then_expr,
                else_expr,
            } => {
                let condition = Self::go(cond, inputs, ops, dedup)?;
                let then_value = Self::go_select(then_expr, selected_index, inputs, ops, dedup)?;
                let else_value = Self::go_select(else_expr, selected_index, inputs, ops, dedup)?;
                Some(Self::push(
                    ops,
                    dedup,
                    FlatOp::Ite(condition, then_value, else_value),
                ))
            }
            _ => None,
        }
    }

    /// Evaluate the tape front-to-back into `scratch` (cleared then filled, one
    /// `SVal` per op), returning the root as an [`EvalResult`]. `scratch` is a
    /// per-sample-loop scratch buffer reused across samples (zero per-sample
    /// allocation). Each arm is a 1:1 transcription of the matching
    /// `SmtExpr::try_eval` arm.
    pub fn eval(&self, env: &EvalEnv, scratch: &mut Vec<SVal>) -> EvalResult {
        scratch.clear();
        for op in &self.ops {
            let v = match *op {
                FlatOp::Const(v) => SVal::Bv(v),
                FlatOp::Const128(v) => SVal::Bv128(v),
                FlatOp::BoolConst(b) => SVal::Bool(b),
                FlatOp::Var(slot, w) => SVal::Bv(mask(env.value_at(slot), w)),
                FlatOp::Add(a, b, w) => {
                    if w > 64 {
                        SVal::Bv128(mask128(
                            scratch[a].as_u128().wrapping_add(scratch[b].as_u128()),
                            w,
                        ))
                    } else {
                        SVal::Bv(mask(
                            scratch[a].as_u64().wrapping_add(scratch[b].as_u64()),
                            w,
                        ))
                    }
                }
                FlatOp::Sub(a, b, w) => {
                    if w > 64 {
                        SVal::Bv128(mask128(
                            scratch[a].as_u128().wrapping_sub(scratch[b].as_u128()),
                            w,
                        ))
                    } else {
                        SVal::Bv(mask(
                            scratch[a].as_u64().wrapping_sub(scratch[b].as_u64()),
                            w,
                        ))
                    }
                }
                FlatOp::Mul(a, b, w) => {
                    if w > 64 {
                        SVal::Bv128(mask128(
                            scratch[a].as_u128().wrapping_mul(scratch[b].as_u128()),
                            w,
                        ))
                    } else {
                        SVal::Bv(mask(
                            scratch[a].as_u64().wrapping_mul(scratch[b].as_u64()),
                            w,
                        ))
                    }
                }
                FlatOp::And(a, b, w) => {
                    if w > 64 {
                        SVal::Bv128(mask128(scratch[a].as_u128() & scratch[b].as_u128(), w))
                    } else {
                        SVal::Bv(mask(scratch[a].as_u64() & scratch[b].as_u64(), w))
                    }
                }
                FlatOp::Or(a, b, w) => {
                    if w > 64 {
                        SVal::Bv128(mask128(scratch[a].as_u128() | scratch[b].as_u128(), w))
                    } else {
                        SVal::Bv(mask(scratch[a].as_u64() | scratch[b].as_u64(), w))
                    }
                }
                FlatOp::Xor(a, b, w) => {
                    if w > 64 {
                        SVal::Bv128(mask128(scratch[a].as_u128() ^ scratch[b].as_u128(), w))
                    } else {
                        SVal::Bv(mask(scratch[a].as_u64() ^ scratch[b].as_u64(), w))
                    }
                }
                FlatOp::Shl(a, b, w) => {
                    if w > 64 {
                        let av = scratch[a].as_u128();
                        let bv = scratch[b].as_u128();
                        if bv >= w as u128 {
                            SVal::Bv128(0)
                        } else {
                            SVal::Bv128(mask128(av << bv, w))
                        }
                    } else {
                        let av = scratch[a].as_u64();
                        let bv = scratch[b].as_u64();
                        if bv >= w as u64 {
                            SVal::Bv(0)
                        } else {
                            SVal::Bv(mask(av << bv, w))
                        }
                    }
                }
                FlatOp::Lshr(a, b, w) => {
                    if w > 64 {
                        let av = scratch[a].as_u128();
                        let bv = scratch[b].as_u128();
                        if bv >= w as u128 {
                            SVal::Bv128(0)
                        } else {
                            SVal::Bv128(mask128(av >> bv, w))
                        }
                    } else {
                        let av = scratch[a].as_u64();
                        let bv = scratch[b].as_u64();
                        if bv >= w as u64 {
                            SVal::Bv(0)
                        } else {
                            SVal::Bv(mask(av >> bv, w))
                        }
                    }
                }
                FlatOp::Ashr(a, b, w) => {
                    if w > 64 {
                        let av = sign_extend128(scratch[a].as_u128(), w);
                        let bv = scratch[b].as_u128();
                        if bv >= w as u128 {
                            if av < 0 {
                                SVal::Bv128(mask128(u128::MAX, w))
                            } else {
                                SVal::Bv128(0)
                            }
                        } else {
                            SVal::Bv128(mask128((av >> bv) as u128, w))
                        }
                    } else {
                        let av = sign_extend(scratch[a].as_u64(), w);
                        let bv = scratch[b].as_u64();
                        if bv >= w as u64 {
                            if av < 0 {
                                SVal::Bv(mask(u64::MAX, w))
                            } else {
                                SVal::Bv(0)
                            }
                        } else {
                            SVal::Bv(mask((av >> bv) as u64, w))
                        }
                    }
                }
                FlatOp::SDiv(a, b, w) => {
                    // Mirrors try_eval BvSDiv: 128-bit i128 path for width > 64
                    // (double-width x86 IDIV dividend) and the u64/i64 path
                    // otherwise, incl. the exact b==0 sentinels and the
                    // INT_MIN/-1 overflow gates keyed on w>=128 / w==64.
                    if w > 64 {
                        let a = sign_extend128(scratch[a].as_u128(), w);
                        let b = sign_extend128(scratch[b].as_u128(), w);
                        if b == 0 {
                            SVal::Bv128(0)
                        } else if a == i128::MIN && b == -1 && w >= 128 {
                            SVal::Bv128(mask128(a as u128, w))
                        } else {
                            SVal::Bv128(mask128(a.wrapping_div(b) as u128, w))
                        }
                    } else {
                        let a = sign_extend(scratch[a].as_u64(), w);
                        let b = sign_extend(scratch[b].as_u64(), w);
                        if b == 0 {
                            SVal::Bv(0)
                        } else if a == i64::MIN && b == -1 && w == 64 {
                            SVal::Bv(mask(a as u64, w))
                        } else {
                            SVal::Bv(mask(a.wrapping_div(b) as u64, w))
                        }
                    }
                }
                FlatOp::UDiv(a, b, w) => {
                    if w > 64 {
                        let a = scratch[a].as_u128();
                        let b = scratch[b].as_u128();
                        SVal::Bv128(a.checked_div(b).map(|q| mask128(q, w)).unwrap_or(0))
                    } else {
                        let a = scratch[a].as_u64();
                        let b = scratch[b].as_u64();
                        SVal::Bv(a.checked_div(b).map(|q| mask(q, w)).unwrap_or(0))
                    }
                }
                FlatOp::URem(a, b, w) => {
                    // No width > 64 branch (compile fails closed for that); mirrors
                    // try_eval BvURem: b==0 -> the (masked) dividend.
                    let a = scratch[a].as_u64();
                    let b = scratch[b].as_u64();
                    if b == 0 {
                        SVal::Bv(mask(a, w))
                    } else {
                        SVal::Bv(mask(a % b, w))
                    }
                }
                FlatOp::Neg(a, w) => {
                    if w > 64 {
                        SVal::Bv128(mask128((!scratch[a].as_u128()).wrapping_add(1), w))
                    } else {
                        SVal::Bv(mask((!scratch[a].as_u64()).wrapping_add(1), w))
                    }
                }
                FlatOp::Trap(g, val) => {
                    let gv = scratch[g];
                    if matches!(gv, SVal::Poison) || gv.as_u128() == 0 {
                        SVal::Poison
                    } else {
                        scratch[val]
                    }
                }
                FlatOp::Eq(a, b) => SVal::Bool(scratch[a] == scratch[b]),
                FlatOp::Not(a) => SVal::Bool(!scratch[a].as_bool()),
                FlatOp::Slt(a, b, w) => SVal::Bool(
                    sign_extend(scratch[a].as_u64(), w) < sign_extend(scratch[b].as_u64(), w),
                ),
                FlatOp::Sge(a, b, w) => SVal::Bool(
                    sign_extend(scratch[a].as_u64(), w) >= sign_extend(scratch[b].as_u64(), w),
                ),
                FlatOp::Sgt(a, b, w) => SVal::Bool(
                    sign_extend(scratch[a].as_u64(), w) > sign_extend(scratch[b].as_u64(), w),
                ),
                FlatOp::Sle(a, b, w) => SVal::Bool(
                    sign_extend(scratch[a].as_u64(), w) <= sign_extend(scratch[b].as_u64(), w),
                ),
                FlatOp::Uge(a, b) => SVal::Bool(scratch[a].as_u64() >= scratch[b].as_u64()),
                FlatOp::Ult(a, b) => SVal::Bool(scratch[a].as_u64() < scratch[b].as_u64()),
                FlatOp::Ugt(a, b) => SVal::Bool(scratch[a].as_u64() > scratch[b].as_u64()),
                FlatOp::Ule(a, b) => SVal::Bool(scratch[a].as_u64() <= scratch[b].as_u64()),
                FlatOp::BAnd(a, b) => SVal::Bool(scratch[a].as_bool() && scratch[b].as_bool()),
                FlatOp::BOr(a, b) => SVal::Bool(scratch[a].as_bool() || scratch[b].as_bool()),
                FlatOp::Ite(c, t, el) => {
                    if scratch[c].as_bool() {
                        scratch[t]
                    } else {
                        scratch[el]
                    }
                }
                FlatOp::Extract(o, low, width) => {
                    let v = scratch[o].as_u128();
                    SVal::Bv(((v >> low) & mask128(u128::MAX, width)) as u64)
                }
                FlatOp::Concat(hi, lo, lo_width, width) => {
                    let hv = scratch[hi].as_u128();
                    let lv = scratch[lo].as_u128();
                    let result = mask128((hv << lo_width) | lv, width);
                    if width <= 64 {
                        SVal::Bv(result as u64)
                    } else {
                        SVal::Bv128(result)
                    }
                }
                FlatOp::ZExt(o, width) => {
                    let v = scratch[o].as_u128();
                    if width > 64 {
                        SVal::Bv128(mask128(v, width))
                    } else {
                        SVal::Bv(mask(v as u64, width))
                    }
                }
                FlatOp::SExt(o, src_width, width) => {
                    if width > 64 {
                        let v = scratch[o].as_u128();
                        SVal::Bv128(mask128(sign_extend128(v, src_width) as u128, width))
                    } else {
                        let v = scratch[o].as_u64();
                        SVal::Bv(mask(sign_extend(v, src_width) as u64, width))
                    }
                }
                FlatOp::MemLoad(address, load_bits, signed, result_width) => {
                    let raw = mask(mem_load_mix(scratch[address].as_u64()), load_bits);
                    let value = if signed {
                        mask(sign_extend(raw, load_bits) as u64, result_width)
                    } else {
                        mask(raw, result_width)
                    };
                    SVal::Bv(value)
                }
            };
            scratch.push(v);
        }
        scratch[self.root].to_eval()
    }
}

/// True if `expr` contains any division/remainder or trap node
/// (`bvsdiv`/`bvudiv`/`bvurem`/`TrapIfZero`) — the subset [`FlatProg`] adds over
/// [`CExpr`]. Used by the DB soundness gate to count how many obligations now
/// exercise the new division arms of the compiled fast path.
pub fn expr_contains_division(expr: &SmtExpr) -> bool {
    if matches!(
        expr,
        SmtExpr::BvSDiv { .. }
            | SmtExpr::BvUDiv { .. }
            | SmtExpr::BvURem { .. }
            | SmtExpr::TrapIfZero { .. }
    ) {
        return true;
    }
    let mut found = false;
    expr.for_each_child(&mut |child| {
        if !found {
            found = expr_contains_division(child);
        }
    });
    found
}

#[cfg(feature = "trust-types-bridge")]
pub mod trust_formula_adapter;

// ---------------------------------------------------------------------------
// RoundingMode (IEEE 754)
// ---------------------------------------------------------------------------

/// IEEE 754 rounding mode for floating-point operations.
///
/// Maps to SMT-LIB2 rounding modes in the QF_FP theory.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum RoundingMode {
    /// Round to nearest, ties to even (default).
    RNE,
    /// Round to nearest, ties away from zero.
    RNA,
    /// Round toward positive infinity.
    RTP,
    /// Round toward negative infinity.
    RTN,
    /// Round toward zero (truncation).
    RTZ,
}

// ---------------------------------------------------------------------------
// OutOfRangeMode (float -> signed int conversion)
// ---------------------------------------------------------------------------

/// Out-of-range / NaN / +-Inf behaviour for a float-to-signed-int conversion
/// (`FPToSBv`). The IEEE rounded value is the same in every mode; the modes
/// differ ONLY in what is returned when the source is NaN / +-Inf, or the
/// rounded magnitude falls outside the signed destination range.
///
/// (An ENUM — not a bool — so a third policy could be added without churning
/// every call site, and so the two distinct hardware semantics are NAMED at
/// each encoder rather than encoded as an unlabelled `true`/`false`.)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum OutOfRangeMode {
    /// Clamp to the destination INT_MAX/INT_MIN and map NaN -> 0. This is the
    /// DEFINED behaviour of wasm `i32.trunc_sat_f*` / AArch64 `FCVTZS` /
    /// RISC-V `FCVT.W/L.S/D` (canonical out-of-range result) / the Rust `as`
    /// cast. The historical (and DEFAULT) `FPToSBv` behaviour.
    Saturate,
    /// Return the x86 "integer indefinite" value (sign bit set, all other bits
    /// zero, i.e. INT_MIN for the destination width) on NaN / +-Inf / out-of-
    /// range. This is the Intel SDM behaviour of `CVT[T]SS2SI`/`CVT[T]SD2SI`.
    IntegerIndefinite,
}

// ---------------------------------------------------------------------------
// SmtError
// ---------------------------------------------------------------------------

/// Errors arising from SMT expression construction or evaluation.
#[derive(Debug, Error)]
pub enum SmtError {
    /// A type cannot be represented in the SMT bitvector domain.
    #[error("unsupported type for SMT encoding: {0}")]
    UnsupportedType(String),

    /// `bv_width()` called on a Bool-sorted expression.
    #[error("bv_width called on Bool-sorted expression")]
    BoolHasNoWidth,

    /// ConstArray index sort must be a bitvector sort.
    #[error("ConstArray index sort must be BitVec, got: {0}")]
    InvalidArrayIndexSort(String),

    /// Store/Select operation on a non-array expression.
    #[error("expected array sort, got: {0}")]
    NotAnArraySort(String),

    /// Variable not found during concrete evaluation.
    #[error("variable '{0}' not found in evaluation environment")]
    UndefinedVariable(String),

    /// Recursive evaluation failed.
    #[error("evaluation error: {0}")]
    EvalError(String),
}

// ---------------------------------------------------------------------------
// SmtSort
// ---------------------------------------------------------------------------

/// SMT sort (type) for bitvector verification.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum SmtSort {
    /// Fixed-width bitvector.  Width must be > 0.
    BitVec(u32),
    /// Boolean (used for comparison results, preconditions).
    Bool,
    /// Array sort: `(Array index_sort element_sort)`.
    ///
    /// Maps to SMT-LIB2 QF_ABV (arrays of bitvectors) or QF_AUFBV.
    Array(Box<SmtSort>, Box<SmtSort>),
    /// IEEE 754 floating-point sort: `(_ FloatingPoint eb sb)`.
    ///
    /// `eb` = exponent bits, `sb` = significand bits (including implicit bit).
    /// Maps to SMT-LIB2 QF_FP theory.
    FloatingPoint(u32, u32),
}

impl SmtSort {
    /// Bitvector width, or `None` for non-bitvector sorts.
    pub fn bv_width(&self) -> Option<u32> {
        match self {
            SmtSort::BitVec(w) => Some(*w),
            _ => None,
        }
    }

    /// IEEE 754 half-precision: `(_ FloatingPoint 5 11)`.
    pub fn fp16() -> Self {
        SmtSort::FloatingPoint(5, 11)
    }

    /// IEEE 754 single-precision: `(_ FloatingPoint 8 24)`.
    pub fn fp32() -> Self {
        SmtSort::FloatingPoint(8, 24)
    }

    /// IEEE 754 double-precision: `(_ FloatingPoint 11 53)`.
    pub fn fp64() -> Self {
        SmtSort::FloatingPoint(11, 53)
    }

    /// Convenience: array from bitvectors to bitvectors.
    pub fn bv_array(index_width: u32, element_width: u32) -> Self {
        SmtSort::Array(
            Box::new(SmtSort::BitVec(index_width)),
            Box::new(SmtSort::BitVec(element_width)),
        )
    }
}

impl TryFrom<Type> for SmtSort {
    type Error = SmtError;

    fn try_from(ty: Type) -> Result<Self, SmtError> {
        match ty {
            Type::B1 => Ok(SmtSort::BitVec(1)),
            Type::I8 => Ok(SmtSort::BitVec(8)),
            Type::I16 => Ok(SmtSort::BitVec(16)),
            Type::I32 => Ok(SmtSort::BitVec(32)),
            Type::I64 => Ok(SmtSort::BitVec(64)),
            Type::I128 => Ok(SmtSort::BitVec(128)),
            Type::F16 => Ok(SmtSort::fp16()),
            Type::F32 => Ok(SmtSort::fp32()),
            Type::F64 => Ok(SmtSort::fp64()),
            Type::Struct(_) => Err(SmtError::UnsupportedType(
                "struct type verification not yet supported".to_string(),
            )),
            Type::Enum { .. } => Err(SmtError::UnsupportedType(
                "enum type verification not yet supported".to_string(),
            )),
            Type::V128 => Ok(SmtSort::BitVec(128)),
            Type::V64 => Ok(SmtSort::BitVec(64)),
            Type::Array(elem_ty, count) => {
                let elem_sort = SmtSort::try_from(*elem_ty)?;
                // Index sort: bitvector wide enough to address `count` elements.
                let index_bits = if count == 0 {
                    1
                } else {
                    32u32.max((count as f64).log2().ceil() as u32).max(1)
                };
                Ok(SmtSort::Array(
                    Box::new(SmtSort::BitVec(index_bits)),
                    Box::new(elem_sort),
                ))
            }
        }
    }
}

// ---------------------------------------------------------------------------
// SmtExpr
// ---------------------------------------------------------------------------

/// A bitvector SMT expression.
///
/// All bitvector operations use wrapping (two's complement) semantics.
/// The `width` field on BV nodes tracks the bitvector width for masking.
///
/// `Hash` is derived (consistently with the derived `PartialEq`) so proof
/// obligations can be used as STRUCTURAL, content-complete cache keys — the
/// PROOF-2 memo-key soundness fix requires verdict memos to be keyed by the
/// actual expression trees (which bake operand immediates/displacements),
/// never by an obligation's name alone.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum SmtExpr {
    /// Symbolic variable: `(declare-const name (_ BitVec width))`
    Var { name: String, width: u32 },

    /// Bitvector constant.
    BvConst { value: u64, width: u32 },

    /// Boolean constant.
    BoolConst(bool),

    // -- Bitvector arithmetic --
    /// `bvadd(lhs, rhs)` -- wrapping addition.
    BvAdd {
        lhs: Arc<SmtExpr>,
        rhs: Arc<SmtExpr>,
        width: u32,
    },

    /// `bvsub(lhs, rhs)` -- wrapping subtraction.
    BvSub {
        lhs: Arc<SmtExpr>,
        rhs: Arc<SmtExpr>,
        width: u32,
    },

    /// `bvmul(lhs, rhs)` -- wrapping multiplication.
    BvMul {
        lhs: Arc<SmtExpr>,
        rhs: Arc<SmtExpr>,
        width: u32,
    },

    /// `bvsdiv(lhs, rhs)` -- signed division (truncates toward zero).
    BvSDiv {
        lhs: Arc<SmtExpr>,
        rhs: Arc<SmtExpr>,
        width: u32,
    },

    /// `bvudiv(lhs, rhs)` -- unsigned division.
    BvUDiv {
        lhs: Arc<SmtExpr>,
        rhs: Arc<SmtExpr>,
        width: u32,
    },

    /// `bvurem(lhs, rhs)` -- unsigned remainder.
    BvURem {
        lhs: Arc<SmtExpr>,
        rhs: Arc<SmtExpr>,
        width: u32,
    },

    /// A HARDWARE-TRAPPING result: the `value` bitvector, but POISON whenever
    /// `guard == 0`. This is the FAITHFUL model of x86 `IDIV`/`DIV`, which raise
    /// `#DE` (divide error) and have NO defined result when the divisor is zero —
    /// in contrast to trust_ir's `Sdiv`/`Udiv`, whose div-by-zero contract returns
    /// a defined sentinel, and to AArch64 `SDIV`/`UDIV`, which return 0. Because
    /// the source side and the machine side DISAGREE at `guard == 0` (defined
    /// sentinel vs. Poison, which is unequal to everything), the `divisor != 0`
    /// precondition is genuinely LOAD-BEARING: dropping it makes the native
    /// evaluator sample the trap point and REFUTE (closes the D survivor, #79).
    ///
    /// `width` is the bit width of `value` (the sort of the whole node). In the
    /// SMT lane this lowers to `ite(guard == 0, <fresh unconstrained poison>,
    /// value)`, so the solver likewise sees an arbitrary/undefined value at the
    /// trap and cannot prove equality without the precondition.
    TrapIfZero {
        guard: Arc<SmtExpr>,
        value: Arc<SmtExpr>,
        width: u32,
    },

    /// `bvneg(operand)` -- two's complement negation.
    BvNeg { operand: Arc<SmtExpr>, width: u32 },

    // -- Bitvector comparison (result is Bool) --
    /// `bveq(lhs, rhs)` -- equality.
    Eq {
        lhs: Arc<SmtExpr>,
        rhs: Arc<SmtExpr>,
    },

    /// `not(operand)` -- boolean negation.
    Not { operand: Arc<SmtExpr> },

    /// `bvslt(lhs, rhs)` -- signed less-than.
    BvSlt {
        lhs: Arc<SmtExpr>,
        rhs: Arc<SmtExpr>,
        width: u32,
    },

    /// `bvsge(lhs, rhs)` -- signed greater-or-equal.
    BvSge {
        lhs: Arc<SmtExpr>,
        rhs: Arc<SmtExpr>,
        width: u32,
    },

    /// `bvuge(lhs, rhs)` -- unsigned greater-or-equal.
    BvUge {
        lhs: Arc<SmtExpr>,
        rhs: Arc<SmtExpr>,
        width: u32,
    },

    /// `and(lhs, rhs)` -- boolean AND.
    And {
        lhs: Arc<SmtExpr>,
        rhs: Arc<SmtExpr>,
    },

    /// `or(lhs, rhs)` -- boolean OR.
    Or {
        lhs: Arc<SmtExpr>,
        rhs: Arc<SmtExpr>,
    },

    /// `bvsgt(lhs, rhs)` -- signed greater-than.
    BvSgt {
        lhs: Arc<SmtExpr>,
        rhs: Arc<SmtExpr>,
        width: u32,
    },

    /// `bvsle(lhs, rhs)` -- signed less-or-equal.
    BvSle {
        lhs: Arc<SmtExpr>,
        rhs: Arc<SmtExpr>,
        width: u32,
    },

    /// `bvult(lhs, rhs)` -- unsigned less-than.
    BvUlt {
        lhs: Arc<SmtExpr>,
        rhs: Arc<SmtExpr>,
        width: u32,
    },

    /// `bvugt(lhs, rhs)` -- unsigned greater-than.
    BvUgt {
        lhs: Arc<SmtExpr>,
        rhs: Arc<SmtExpr>,
        width: u32,
    },

    /// `bvule(lhs, rhs)` -- unsigned less-or-equal.
    BvUle {
        lhs: Arc<SmtExpr>,
        rhs: Arc<SmtExpr>,
        width: u32,
    },

    /// `ite(cond, then_expr, else_expr)` -- if-then-else.
    Ite {
        cond: Arc<SmtExpr>,
        then_expr: Arc<SmtExpr>,
        else_expr: Arc<SmtExpr>,
    },

    /// `extract(high, low, operand)` -- bit extraction `operand[high:low]`.
    Extract {
        high: u32,
        low: u32,
        operand: Arc<SmtExpr>,
        width: u32,
    },

    // -- Bitwise operations --
    /// `bvand(lhs, rhs)` -- bitwise AND.
    BvAnd {
        lhs: Arc<SmtExpr>,
        rhs: Arc<SmtExpr>,
        width: u32,
    },

    /// `bvor(lhs, rhs)` -- bitwise OR.
    BvOr {
        lhs: Arc<SmtExpr>,
        rhs: Arc<SmtExpr>,
        width: u32,
    },

    /// `bvxor(lhs, rhs)` -- bitwise XOR.
    BvXor {
        lhs: Arc<SmtExpr>,
        rhs: Arc<SmtExpr>,
        width: u32,
    },

    // -- Shift operations --
    /// `bvshl(lhs, rhs)` -- logical shift left.
    BvShl {
        lhs: Arc<SmtExpr>,
        rhs: Arc<SmtExpr>,
        width: u32,
    },

    /// `bvlshr(lhs, rhs)` -- logical shift right.
    BvLshr {
        lhs: Arc<SmtExpr>,
        rhs: Arc<SmtExpr>,
        width: u32,
    },

    /// `bvashr(lhs, rhs)` -- arithmetic shift right.
    BvAshr {
        lhs: Arc<SmtExpr>,
        rhs: Arc<SmtExpr>,
        width: u32,
    },

    /// `concat(hi, lo)` -- bitvector concatenation.
    ///
    /// Produces a bitvector of width `hi.width + lo.width` where the high bits
    /// come from `hi` and the low bits come from `lo`.
    /// SMT-LIB2: `(concat hi lo)`.
    Concat {
        hi: Arc<SmtExpr>,
        lo: Arc<SmtExpr>,
        width: u32,
    },

    /// `zero_extend(operand, extra_bits)` -- zero-extend by `extra_bits` bits.
    ///
    /// Produces a bitvector of width `operand.width + extra_bits`.
    /// SMT-LIB2: `((_ zero_extend extra_bits) operand)`.
    ZeroExtend {
        operand: Arc<SmtExpr>,
        extra_bits: u32,
        width: u32,
    },

    /// `sign_extend(operand, extra_bits)` -- sign-extend by `extra_bits` bits.
    ///
    /// Produces a bitvector of width `operand.width + extra_bits`.
    /// SMT-LIB2: `((_ sign_extend extra_bits) operand)`.
    SignExtend {
        operand: Arc<SmtExpr>,
        extra_bits: u32,
        width: u32,
    },

    // -- Array operations (QF_ABV theory) --
    /// `(select array index)` -- read element at index.
    Select {
        array: Arc<SmtExpr>,
        index: Arc<SmtExpr>,
    },

    /// `(store array index value)` -- write element at index, producing new array.
    Store {
        array: Arc<SmtExpr>,
        index: Arc<SmtExpr>,
        value: Arc<SmtExpr>,
    },

    /// `((as const (Array idx_sort elem_sort)) value)` -- constant array.
    ConstArray {
        index_sort: SmtSort,
        value: Arc<SmtExpr>,
    },

    // -- Memory load as a deterministic uninterpreted function of the address --
    /// `MemLoad(addr, load_bits, signed, result_width)` -- the value read by a
    /// `load_bits`-wide memory access at the effective address `addr`, then
    /// sign- or zero-extended to `result_width`.
    ///
    /// This is the McCarthy/array read axiom with a CONCRETE, DETERMINISTIC
    /// instance of the "memory contents" function `f`: the bytes at address `A`
    /// are a fixed function of `A` alone. Concretely `eval` computes
    /// `f(A) = mix(A)` (a bijective integer avalanche hash of the FULL address),
    /// truncates to `load_bits`, then extends to `result_width` per `signed`.
    ///
    /// Soundness for REFUTATION (the whole point):
    /// * `mix` is a bijection, so `A1 != A2 => mix(A1) != mix(A2)`; over the
    ///   sampler's address inputs a wrong effective address (wrong base / index /
    ///   scale / displacement) produces a different loaded value ⇒ REFUTE.
    /// * Two loads with the SAME `(addr, load_bits, signed)` always agree
    ///   (`f` is a function), so a correct lowering whose machine EA equals the
    ///   IR EA discharges Valid: `load(ea_machine) == load(ea_ir) <=> ea_machine
    ///   == ea_ir` over all inputs.
    /// * `load_bits` participates in the value, so an 8-bit-for-32-bit width
    ///   mismatch diverges whenever `mix(A)` has a set bit in `[8, 32)` ⇒ REFUTE.
    /// * `signed` participates via the extend, so a zero-for-sign mismatch
    ///   diverges whenever the top loaded bit is set ⇒ REFUTE.
    ///
    /// `addr` is a `BitVec` of any width (typically 64); the node's own sort is a
    /// `BitVec(result_width)`. The `index`/`width`/`sign` triple is exactly the
    /// (effective-address, width, signedness) the task's memory model keys on.
    MemLoad {
        addr: Arc<SmtExpr>,
        /// Width in bits of the memory access itself (8/16/32/64).
        load_bits: u32,
        /// Sign-extend (`true`) vs zero-extend (`false`) to `result_width`.
        signed: bool,
        /// Width in bits of the produced (destination-register) value.
        result_width: u32,
    },

    // -- Floating-point operations (QF_FP theory) --
    /// `(fp.add rm a b)` -- floating-point addition.
    FPAdd {
        rm: RoundingMode,
        lhs: Arc<SmtExpr>,
        rhs: Arc<SmtExpr>,
    },

    /// `(fp.mul rm a b)` -- floating-point multiplication.
    FPMul {
        rm: RoundingMode,
        lhs: Arc<SmtExpr>,
        rhs: Arc<SmtExpr>,
    },

    /// `(fp.sub rm a b)` -- floating-point subtraction.
    FPSub {
        rm: RoundingMode,
        lhs: Arc<SmtExpr>,
        rhs: Arc<SmtExpr>,
    },

    /// `(fp.div rm a b)` -- floating-point division.
    FPDiv {
        rm: RoundingMode,
        lhs: Arc<SmtExpr>,
        rhs: Arc<SmtExpr>,
    },

    /// `(fp.neg a)` -- floating-point negation.
    FPNeg { operand: Arc<SmtExpr> },

    /// `(fp.eq a b)` -- floating-point equality (returns Bool).
    FPEq {
        lhs: Arc<SmtExpr>,
        rhs: Arc<SmtExpr>,
    },

    /// `(fp.lt a b)` -- floating-point less-than (returns Bool).
    FPLt {
        lhs: Arc<SmtExpr>,
        rhs: Arc<SmtExpr>,
    },

    /// `(fp.gt a b)` -- floating-point greater-than (returns Bool).
    FPGt {
        lhs: Arc<SmtExpr>,
        rhs: Arc<SmtExpr>,
    },

    /// `(fp.geq a b)` -- floating-point greater-or-equal (returns Bool).
    FPGe {
        lhs: Arc<SmtExpr>,
        rhs: Arc<SmtExpr>,
    },

    /// `(fp.leq a b)` -- floating-point less-or-equal (returns Bool).
    FPLe {
        lhs: Arc<SmtExpr>,
        rhs: Arc<SmtExpr>,
    },

    /// Floating-point constant from f64 bits.
    ///
    /// `eb` = exponent bits, `sb` = significand bits.
    /// The `bits` field holds the IEEE 754 bit pattern.
    FPConst { bits: u64, eb: u32, sb: u32 },

    /// `(fp.sqrt rm a)` -- floating-point square root.
    FPSqrt {
        rm: RoundingMode,
        operand: Arc<SmtExpr>,
    },

    /// `(fp.roundToIntegral rm a)` -- round to the nearest floating-point value
    /// that is an integer, in the direction given by the rounding mode. The
    /// result has the same FP sort as the operand. With `rm = RTN` this is
    /// floor, `RTP` is ceil, and `RTZ` is truncation.
    FPRoundToIntegral {
        rm: RoundingMode,
        operand: Arc<SmtExpr>,
    },

    /// `(fp.abs a)` -- floating-point absolute value.
    FPAbs { operand: Arc<SmtExpr> },

    /// `(fp.fma rm a b c)` -- floating-point fused multiply-add: `a * b + c`.
    FPFma {
        rm: RoundingMode,
        a: Arc<SmtExpr>,
        b: Arc<SmtExpr>,
        c: Arc<SmtExpr>,
    },

    /// `(fp.isNaN a)` -- true if the argument is NaN (returns Bool).
    FPIsNaN { operand: Arc<SmtExpr> },

    /// `(fp.isInfinite a)` -- true if the argument is +/- infinity (returns Bool).
    FPIsInf { operand: Arc<SmtExpr> },

    /// `(fp.isZero a)` -- true if the argument is +/- zero (returns Bool).
    FPIsZero { operand: Arc<SmtExpr> },

    /// `(fp.isNormal a)` -- true if the argument is a normal FP number (returns Bool).
    FPIsNormal { operand: Arc<SmtExpr> },

    /// `((_ fp.to_sbv width) rm a)` -- convert FP to signed bitvector.
    ///
    /// `mode` selects the out-of-range / NaN / +-Inf behaviour: `Saturate`
    /// (wasm trunc_sat / AArch64 FCVTZS / RISC-V FCVT / Rust `as`) vs
    /// `IntegerIndefinite` (x86 CVT[T]*2SI). The rounded value is identical in
    /// every mode; only the out-of-range result differs.
    FPToSBv {
        rm: RoundingMode,
        operand: Arc<SmtExpr>,
        width: u32,
        mode: OutOfRangeMode,
    },

    /// `((_ fp.to_ubv width) rm a)` -- convert FP to unsigned bitvector.
    FPToUBv {
        rm: RoundingMode,
        operand: Arc<SmtExpr>,
        width: u32,
    },

    /// `((_ to_fp eb sb) rm bv)` -- convert bitvector to FP with rounding.
    BvToFP {
        rm: RoundingMode,
        operand: Arc<SmtExpr>,
        eb: u32,
        sb: u32,
    },

    /// `((_ to_fp eb sb) rm fp)` -- convert between FP formats with rounding.
    FPToFP {
        rm: RoundingMode,
        operand: Arc<SmtExpr>,
        eb: u32,
        sb: u32,
    },

    /// `((_ to_fp eb sb) bv)` -- REINTERPRET an `(eb+sb)`-bit bitvector's raw
    /// bits as an IEEE-754 FloatingPoint(eb, sb) value (the single-argument,
    /// rounding-mode-free SMT-LIB `to_fp` form — a bit cast, NOT a numeric
    /// conversion). The lane-split entry point for the NEON FP per-lane
    /// obligations: a 32/64-bit lane sliced from a Q register becomes the FP
    /// leaf the per-lane IEEE op consumes.
    BvBitsToFP {
        operand: Arc<SmtExpr>,
        eb: u32,
        sb: u32,
    },

    // -- Uninterpreted functions (QF_UF theory) --
    /// `(name arg1 arg2 ...)` -- uninterpreted function application.
    UF {
        name: String,
        args: Vec<SmtExpr>,
        ret_sort: SmtSort,
    },

    /// `(declare-fun name (arg_sorts...) ret_sort)` -- function declaration.
    ///
    /// This is not an expression per se but a declaration node used in
    /// query generation to emit the function signature.
    UFDecl {
        name: String,
        arg_sorts: Vec<SmtSort>,
        ret_sort: SmtSort,
    },

    // -- Bounded quantifiers --
    /// `(forall ((var (_ BitVec w))) (=> (and (bvuge var lo) (bvult var hi)) body))`
    ///
    /// Bounded universal quantifier: for all values of `var` in `[lower, upper)`,
    /// `body` holds. The bound variable has bitvector width `var_width`.
    ///
    /// Concrete evaluation: unrolls the quantifier for small ranges (upper - lower <= 256)
    /// and checks that `body` evaluates to true for every value in the range.
    ForAll {
        var: String,
        var_width: u32,
        lower: Arc<SmtExpr>,
        upper: Arc<SmtExpr>,
        body: Arc<SmtExpr>,
    },

    /// `(exists ((var (_ BitVec w))) (and (bvuge var lo) (bvult var hi) body))`
    ///
    /// Bounded existential quantifier: there exists a value of `var` in `[lower, upper)`
    /// such that `body` holds. The bound variable has bitvector width `var_width`.
    ///
    /// Concrete evaluation: unrolls the quantifier for small ranges (upper - lower <= 256)
    /// and checks that `body` evaluates to true for at least one value in the range.
    Exists {
        var: String,
        var_width: u32,
        lower: Arc<SmtExpr>,
        upper: Arc<SmtExpr>,
        body: Arc<SmtExpr>,
    },
}

// ---------------------------------------------------------------------------
// Array sort validation helper
// ---------------------------------------------------------------------------

/// Validate that an expression has an Array sort, when statically determinable.
///
/// Expressions whose sort is statically known to be non-Array (e.g., `BvConst`,
/// `BoolConst`, comparison results) cause an error. Expressions whose sort
/// cannot be cheaply determined at construction time (e.g., `Var`, `Ite`) are
/// allowed through — runtime validation occurs in `try_eval`.
fn validate_array_sort(expr: &SmtExpr) -> Result<(), SmtError> {
    match expr {
        // Known array-sorted expressions: always OK.
        SmtExpr::ConstArray { .. } | SmtExpr::Store { .. } => Ok(()),
        // Expressions whose sort is ambiguous at construction time: allow.
        // Var, Select (returns element sort), Ite, UF — we can't cheaply
        // determine array sort without recursion, so defer to eval.
        SmtExpr::Var { .. } | SmtExpr::Ite { .. } | SmtExpr::Select { .. } | SmtExpr::UF { .. } => {
            Ok(())
        }
        // Everything else is statically known to NOT be array-sorted.
        other => {
            let sort = other.sort();
            if matches!(sort, SmtSort::Array(_, _)) {
                Ok(())
            } else {
                Err(SmtError::NotAnArraySort(format!("{}", sort)))
            }
        }
    }
}

// ---------------------------------------------------------------------------
// SmtExpr constructors (ergonomic builder API)
// ---------------------------------------------------------------------------

impl SmtExpr {
    /// Symbolic variable of given width.
    pub fn var(name: impl Into<String>, width: u32) -> Self {
        SmtExpr::Var {
            name: name.into(),
            width,
        }
    }

    /// Bitvector constant.
    pub fn bv_const(value: u64, width: u32) -> Self {
        SmtExpr::BvConst {
            value: mask(value, width),
            width,
        }
    }

    /// Boolean constant.
    pub fn bool_const(value: bool) -> Self {
        SmtExpr::BoolConst(value)
    }

    /// `bvadd`
    pub fn bvadd(self, other: Self) -> Self {
        let w = self.bv_width();
        SmtExpr::BvAdd {
            lhs: Arc::new(self),
            rhs: Arc::new(other),
            width: w,
        }
    }

    /// `bvsub`
    pub fn bvsub(self, other: Self) -> Self {
        let w = self.bv_width();
        SmtExpr::BvSub {
            lhs: Arc::new(self),
            rhs: Arc::new(other),
            width: w,
        }
    }

    /// `bvmul`
    pub fn bvmul(self, other: Self) -> Self {
        let w = self.bv_width();
        SmtExpr::BvMul {
            lhs: Arc::new(self),
            rhs: Arc::new(other),
            width: w,
        }
    }

    /// `bvsdiv`
    pub fn bvsdiv(self, other: Self) -> Self {
        let w = self.bv_width();
        SmtExpr::BvSDiv {
            lhs: Arc::new(self),
            rhs: Arc::new(other),
            width: w,
        }
    }

    /// `bvudiv`
    pub fn bvudiv(self, other: Self) -> Self {
        let w = self.bv_width();
        SmtExpr::BvUDiv {
            lhs: Arc::new(self),
            rhs: Arc::new(other),
            width: w,
        }
    }

    /// `bvurem`
    pub fn bvurem(self, other: Self) -> Self {
        let w = self.bv_width();
        SmtExpr::BvURem {
            lhs: Arc::new(self),
            rhs: Arc::new(other),
            width: w,
        }
    }

    /// `trap_if_zero`: wrap `self` (the defined hardware result) so that it
    /// evaluates to POISON whenever `guard` is zero — the faithful model of an
    /// x86 `IDIV`/`DIV` `#DE` trap on a zero divisor. The node's sort is `self`'s
    /// bitvector width. See [`SmtExpr::TrapIfZero`].
    pub fn trap_if_zero(self, guard: Self) -> Self {
        let w = self.bv_width();
        SmtExpr::TrapIfZero {
            guard: Arc::new(guard),
            value: Arc::new(self),
            width: w,
        }
    }

    /// `bvneg`
    pub fn bvneg(self) -> Self {
        let w = self.bv_width();
        SmtExpr::BvNeg {
            operand: Arc::new(self),
            width: w,
        }
    }

    /// `=` (equality)
    pub fn eq_expr(self, other: Self) -> Self {
        SmtExpr::Eq {
            lhs: Arc::new(self),
            rhs: Arc::new(other),
        }
    }

    /// `not`
    pub fn not_expr(self) -> Self {
        SmtExpr::Not {
            operand: Arc::new(self),
        }
    }

    /// `bvslt` (signed less-than)
    pub fn bvslt(self, other: Self) -> Self {
        let w = self.bv_width();
        SmtExpr::BvSlt {
            lhs: Arc::new(self),
            rhs: Arc::new(other),
            width: w,
        }
    }

    /// `bvsge` (signed greater-or-equal)
    pub fn bvsge(self, other: Self) -> Self {
        let w = self.bv_width();
        SmtExpr::BvSge {
            lhs: Arc::new(self),
            rhs: Arc::new(other),
            width: w,
        }
    }

    /// `bvuge` (unsigned greater-or-equal)
    pub fn bvuge(self, other: Self) -> Self {
        let w = self.bv_width();
        SmtExpr::BvUge {
            lhs: Arc::new(self),
            rhs: Arc::new(other),
            width: w,
        }
    }

    /// `and`
    pub fn and_expr(self, other: Self) -> Self {
        SmtExpr::And {
            lhs: Arc::new(self),
            rhs: Arc::new(other),
        }
    }

    /// `or`
    pub fn or_expr(self, other: Self) -> Self {
        SmtExpr::Or {
            lhs: Arc::new(self),
            rhs: Arc::new(other),
        }
    }

    /// `bvsgt` (signed greater-than)
    pub fn bvsgt(self, other: Self) -> Self {
        let w = self.bv_width();
        SmtExpr::BvSgt {
            lhs: Arc::new(self),
            rhs: Arc::new(other),
            width: w,
        }
    }

    /// `bvsle` (signed less-or-equal)
    pub fn bvsle(self, other: Self) -> Self {
        let w = self.bv_width();
        SmtExpr::BvSle {
            lhs: Arc::new(self),
            rhs: Arc::new(other),
            width: w,
        }
    }

    /// `bvult` (unsigned less-than)
    pub fn bvult(self, other: Self) -> Self {
        let w = self.bv_width();
        SmtExpr::BvUlt {
            lhs: Arc::new(self),
            rhs: Arc::new(other),
            width: w,
        }
    }

    /// `bvugt` (unsigned greater-than)
    pub fn bvugt(self, other: Self) -> Self {
        let w = self.bv_width();
        SmtExpr::BvUgt {
            lhs: Arc::new(self),
            rhs: Arc::new(other),
            width: w,
        }
    }

    /// `bvule` (unsigned less-or-equal)
    pub fn bvule(self, other: Self) -> Self {
        let w = self.bv_width();
        SmtExpr::BvUle {
            lhs: Arc::new(self),
            rhs: Arc::new(other),
            width: w,
        }
    }

    /// `ite` (if-then-else)
    pub fn ite(cond: Self, then_expr: Self, else_expr: Self) -> Self {
        SmtExpr::Ite {
            cond: Arc::new(cond),
            then_expr: Arc::new(then_expr),
            else_expr: Arc::new(else_expr),
        }
    }

    /// `bvand` -- bitwise AND.
    pub fn bvand(self, other: Self) -> Self {
        let w = self.bv_width();
        SmtExpr::BvAnd {
            lhs: Arc::new(self),
            rhs: Arc::new(other),
            width: w,
        }
    }

    /// `bvor` -- bitwise OR.
    pub fn bvor(self, other: Self) -> Self {
        let w = self.bv_width();
        SmtExpr::BvOr {
            lhs: Arc::new(self),
            rhs: Arc::new(other),
            width: w,
        }
    }

    /// `bvxor` -- bitwise XOR.
    pub fn bvxor(self, other: Self) -> Self {
        let w = self.bv_width();
        SmtExpr::BvXor {
            lhs: Arc::new(self),
            rhs: Arc::new(other),
            width: w,
        }
    }

    /// `bvshl` -- logical shift left.
    pub fn bvshl(self, other: Self) -> Self {
        let w = self.bv_width();
        SmtExpr::BvShl {
            lhs: Arc::new(self),
            rhs: Arc::new(other),
            width: w,
        }
    }

    /// `bvlshr` -- logical shift right.
    pub fn bvlshr(self, other: Self) -> Self {
        let w = self.bv_width();
        SmtExpr::BvLshr {
            lhs: Arc::new(self),
            rhs: Arc::new(other),
            width: w,
        }
    }

    /// `bvashr` -- arithmetic shift right.
    pub fn bvashr(self, other: Self) -> Self {
        let w = self.bv_width();
        SmtExpr::BvAshr {
            lhs: Arc::new(self),
            rhs: Arc::new(other),
            width: w,
        }
    }

    /// `extract(high, low)` -- bit extraction.
    pub fn extract(self, high: u32, low: u32) -> Self {
        let result_width = high - low + 1;
        SmtExpr::Extract {
            high,
            low,
            operand: Arc::new(self),
            width: result_width,
        }
    }

    /// `concat(hi, lo)` -- bitvector concatenation.
    ///
    /// The result has width `hi.width + lo.width`, with `hi` in the upper bits.
    pub fn concat(self, lo: Self) -> Self {
        let w = self.bv_width() + lo.bv_width();
        SmtExpr::Concat {
            hi: Arc::new(self),
            lo: Arc::new(lo),
            width: w,
        }
    }

    /// `zero_extend(extra_bits)` -- zero-extend this bitvector.
    pub fn zero_ext(self, extra_bits: u32) -> Self {
        let w = self.bv_width() + extra_bits;
        SmtExpr::ZeroExtend {
            operand: Arc::new(self),
            extra_bits,
            width: w,
        }
    }

    /// `sign_extend(extra_bits)` -- sign-extend this bitvector.
    pub fn sign_ext(self, extra_bits: u32) -> Self {
        let w = self.bv_width() + extra_bits;
        SmtExpr::SignExtend {
            operand: Arc::new(self),
            extra_bits,
            width: w,
        }
    }

    // -- Array constructors --

    /// `(select array index)` -- read from array.
    ///
    /// Validates that `array` has an `Array` sort when statically determinable
    /// (i.e., for `ConstArray` and `Store` expressions). For `Var` expressions
    /// whose sort cannot be determined at construction time, validation is
    /// deferred to evaluation via [`try_eval`].
    pub fn select(array: Self, index: Self) -> Self {
        Self::try_select(array, index)
            .expect("select: first argument must have Array sort; use try_select() for fallible construction")
    }

    /// Fallible `(select array index)`.
    ///
    /// Returns `Err(SmtError::NotAnArraySort)` if the array expression's sort
    /// is statically known to not be an Array sort.
    pub fn try_select(array: Self, index: Self) -> Result<Self, SmtError> {
        validate_array_sort(&array)?;
        Ok(SmtExpr::Select {
            array: Arc::new(array),
            index: Arc::new(index),
        })
    }

    /// `(store array index value)` -- write to array.
    ///
    /// Validates that `array` has an `Array` sort when statically determinable.
    pub fn store(array: Self, index: Self, value: Self) -> Self {
        Self::try_store(array, index, value).expect(
            "store: first argument must have Array sort; use try_store() for fallible construction",
        )
    }

    /// Fallible `(store array index value)`.
    ///
    /// Returns `Err(SmtError::NotAnArraySort)` if the array expression's sort
    /// is statically known to not be an Array sort.
    pub fn try_store(array: Self, index: Self, value: Self) -> Result<Self, SmtError> {
        validate_array_sort(&array)?;
        Ok(SmtExpr::Store {
            array: Arc::new(array),
            index: Arc::new(index),
            value: Arc::new(value),
        })
    }

    /// `((as const ...) value)` -- constant array filled with `value`.
    ///
    /// # Panics
    ///
    /// Panics if `index_sort` is not `SmtSort::BitVec`. Use [`try_const_array`]
    /// for fallible construction.
    pub fn const_array(index_sort: SmtSort, value: Self) -> Self {
        Self::try_const_array(index_sort, value)
            .expect("const_array: index_sort must be BitVec; use try_const_array() for fallible construction")
    }

    /// Fallible `((as const ...) value)` -- constant array filled with `value`.
    ///
    /// Returns `Err(SmtError::InvalidArrayIndexSort)` if `index_sort` is not
    /// `SmtSort::BitVec`.
    pub fn try_const_array(index_sort: SmtSort, value: Self) -> Result<Self, SmtError> {
        if !matches!(index_sort, SmtSort::BitVec(_)) {
            return Err(SmtError::InvalidArrayIndexSort(format!("{}", index_sort)));
        }
        Ok(SmtExpr::ConstArray {
            index_sort,
            value: Arc::new(value),
        })
    }

    /// `MemLoad(addr, load_bits, signed, result_width)` -- deterministic memory
    /// read of a `load_bits`-wide access at effective address `addr`, sign/zero-
    /// extended to `result_width`. See the [`SmtExpr::MemLoad`] variant docs for
    /// the memory model and its refutation soundness. `load_bits` must be
    /// `<= result_width`.
    pub fn mem_load(addr: Self, load_bits: u32, signed: bool, result_width: u32) -> Self {
        debug_assert!(
            load_bits > 0 && load_bits <= result_width,
            "mem_load: load_bits ({load_bits}) must be in (0, result_width={result_width}]"
        );
        SmtExpr::MemLoad {
            addr: Arc::new(addr),
            load_bits,
            signed,
            result_width,
        }
    }

    // -- Floating-point constructors --

    /// Floating-point constant from raw IEEE 754 bits.
    pub fn fp_const(bits: u64, eb: u32, sb: u32) -> Self {
        SmtExpr::FPConst { bits, eb, sb }
    }

    /// FP32 constant from an f32 value.
    pub fn fp32_const(v: f32) -> Self {
        SmtExpr::FPConst {
            bits: v.to_bits() as u64,
            eb: 8,
            sb: 24,
        }
    }

    /// FP64 constant from an f64 value.
    pub fn fp64_const(v: f64) -> Self {
        SmtExpr::FPConst {
            bits: v.to_bits(),
            eb: 11,
            sb: 53,
        }
    }

    /// `(fp.add rm a b)` -- floating-point addition.
    pub fn fp_add(rm: RoundingMode, a: Self, b: Self) -> Self {
        SmtExpr::FPAdd {
            rm,
            lhs: Arc::new(a),
            rhs: Arc::new(b),
        }
    }

    /// `(fp.sub rm a b)` -- floating-point subtraction.
    pub fn fp_sub(rm: RoundingMode, a: Self, b: Self) -> Self {
        SmtExpr::FPSub {
            rm,
            lhs: Arc::new(a),
            rhs: Arc::new(b),
        }
    }

    /// `(fp.mul rm a b)` -- floating-point multiplication.
    pub fn fp_mul(rm: RoundingMode, a: Self, b: Self) -> Self {
        SmtExpr::FPMul {
            rm,
            lhs: Arc::new(a),
            rhs: Arc::new(b),
        }
    }

    /// `(fp.div rm a b)` -- floating-point division.
    pub fn fp_div(rm: RoundingMode, a: Self, b: Self) -> Self {
        SmtExpr::FPDiv {
            rm,
            lhs: Arc::new(a),
            rhs: Arc::new(b),
        }
    }

    /// `(fp.neg a)` -- floating-point negation.
    pub fn fp_neg(self) -> Self {
        SmtExpr::FPNeg {
            operand: Arc::new(self),
        }
    }

    /// `(fp.eq a b)` -- floating-point equality (returns Bool).
    pub fn fp_eq(self, other: Self) -> Self {
        SmtExpr::FPEq {
            lhs: Arc::new(self),
            rhs: Arc::new(other),
        }
    }

    /// `(fp.lt a b)` -- floating-point less-than (returns Bool).
    pub fn fp_lt(self, other: Self) -> Self {
        SmtExpr::FPLt {
            lhs: Arc::new(self),
            rhs: Arc::new(other),
        }
    }

    /// `(fp.gt a b)` -- floating-point greater-than (returns Bool).
    pub fn fp_gt(self, other: Self) -> Self {
        SmtExpr::FPGt {
            lhs: Arc::new(self),
            rhs: Arc::new(other),
        }
    }

    /// IEEE `minimumNumber` / Rust `f{32,64}::min` modeled with existing
    /// primitives: `isNaN(a) ? b : isNaN(b) ? a : (a < b ? a : b)`. A lone NaN
    /// yields the number; an ordered pair yields the smaller. This is the
    /// min-flavored side that DIVERGES from [`fp_max_ieee`] (`fp_lt` vs `fp_gt`),
    /// so lowering `Fmin` to FMAXNM refutes. The exact `-0`/`+0` tie and qNaN
    /// payload are pinned by the on-host execution test, not this model.
    pub fn fp_min_ieee(a: Self, b: Self) -> Self {
        let ordered = Self::ite(a.clone().fp_lt(b.clone()), a.clone(), b.clone());
        Self::ite(
            a.clone().fp_is_nan(),
            b.clone(),
            Self::ite(b.fp_is_nan(), a, ordered),
        )
    }

    /// IEEE `maximumNumber` / Rust `f{32,64}::max`. Mirror of [`fp_min_ieee`]
    /// with `fp_gt`.
    pub fn fp_max_ieee(a: Self, b: Self) -> Self {
        let ordered = Self::ite(a.clone().fp_gt(b.clone()), a.clone(), b.clone());
        Self::ite(
            a.clone().fp_is_nan(),
            b.clone(),
            Self::ite(b.fp_is_nan(), a, ordered),
        )
    }

    /// `(fp.geq a b)` -- floating-point greater-or-equal (returns Bool).
    pub fn fp_ge(self, other: Self) -> Self {
        SmtExpr::FPGe {
            lhs: Arc::new(self),
            rhs: Arc::new(other),
        }
    }

    /// `(fp.leq a b)` -- floating-point less-or-equal (returns Bool).
    pub fn fp_le(self, other: Self) -> Self {
        SmtExpr::FPLe {
            lhs: Arc::new(self),
            rhs: Arc::new(other),
        }
    }

    /// `(fp.sqrt rm a)` -- floating-point square root.
    pub fn fp_sqrt(rm: RoundingMode, a: Self) -> Self {
        SmtExpr::FPSqrt {
            rm,
            operand: Arc::new(a),
        }
    }

    /// `(fp.roundToIntegral rm a)` -- round to integral value (floor/ceil/trunc
    /// depending on `rm`).
    pub fn fp_round_to_integral(rm: RoundingMode, a: Self) -> Self {
        SmtExpr::FPRoundToIntegral {
            rm,
            operand: Arc::new(a),
        }
    }

    /// `(fp.abs a)` -- floating-point absolute value.
    pub fn fp_abs(self) -> Self {
        SmtExpr::FPAbs {
            operand: Arc::new(self),
        }
    }

    /// `(fp.fma rm a b c)` -- floating-point fused multiply-add: `a * b + c`.
    pub fn fp_fma(rm: RoundingMode, a: Self, b: Self, c: Self) -> Self {
        SmtExpr::FPFma {
            rm,
            a: Arc::new(a),
            b: Arc::new(b),
            c: Arc::new(c),
        }
    }

    /// `(fp.isNaN a)` -- true if the argument is NaN (returns Bool).
    pub fn fp_is_nan(self) -> Self {
        SmtExpr::FPIsNaN {
            operand: Arc::new(self),
        }
    }

    /// `(fp.isInfinite a)` -- true if the argument is infinity (returns Bool).
    pub fn fp_is_inf(self) -> Self {
        SmtExpr::FPIsInf {
            operand: Arc::new(self),
        }
    }

    /// `(fp.isZero a)` -- true if the argument is +/- zero (returns Bool).
    pub fn fp_is_zero(self) -> Self {
        SmtExpr::FPIsZero {
            operand: Arc::new(self),
        }
    }

    /// `(fp.isNormal a)` -- true if the argument is a normal FP number (returns Bool).
    pub fn fp_is_normal(self) -> Self {
        SmtExpr::FPIsNormal {
            operand: Arc::new(self),
        }
    }

    /// `((_ fp.to_sbv width) rm a)` -- convert FP to signed bitvector with the
    /// DEFAULT (`Saturate`) out-of-range behaviour (wasm/AArch64/RISC-V/Rust).
    pub fn fp_to_sbv(rm: RoundingMode, a: Self, width: u32) -> Self {
        SmtExpr::FPToSBv {
            rm,
            operand: Arc::new(a),
            width,
            mode: OutOfRangeMode::Saturate,
        }
    }

    /// `((_ fp.to_sbv width) rm a)` -- convert FP to signed bitvector with an
    /// EXPLICIT out-of-range `mode` (x86 CVT[T]*2SI passes
    /// `OutOfRangeMode::IntegerIndefinite`).
    pub fn fp_to_sbv_mode(rm: RoundingMode, a: Self, width: u32, mode: OutOfRangeMode) -> Self {
        SmtExpr::FPToSBv {
            rm,
            operand: Arc::new(a),
            width,
            mode,
        }
    }

    /// `((_ fp.to_ubv width) rm a)` -- convert FP to unsigned bitvector.
    pub fn fp_to_ubv(rm: RoundingMode, a: Self, width: u32) -> Self {
        SmtExpr::FPToUBv {
            rm,
            operand: Arc::new(a),
            width,
        }
    }

    /// `((_ to_fp eb sb) rm bv)` -- convert signed bitvector to FP.
    pub fn bv_to_fp(rm: RoundingMode, bv: Self, eb: u32, sb: u32) -> Self {
        SmtExpr::BvToFP {
            rm,
            operand: Arc::new(bv),
            eb,
            sb,
        }
    }

    /// `((_ to_fp eb sb) rm fp)` -- convert between FP formats.
    pub fn fp_to_fp(rm: RoundingMode, fp: Self, eb: u32, sb: u32) -> Self {
        SmtExpr::FPToFP {
            rm,
            operand: Arc::new(fp),
            eb,
            sb,
        }
    }

    /// `((_ to_fp eb sb) bv)` -- reinterpret raw bits as FloatingPoint(eb, sb).
    /// The operand must be an `(eb+sb)`-wide bitvector.
    pub fn bv_bits_to_fp(bv: Self, eb: u32, sb: u32) -> Self {
        SmtExpr::BvBitsToFP {
            operand: Arc::new(bv),
            eb,
            sb,
        }
    }

    // -- Uninterpreted function constructors --

    /// Uninterpreted function application.
    pub fn uf(name: impl Into<String>, args: Vec<Self>, ret_sort: SmtSort) -> Self {
        SmtExpr::UF {
            name: name.into(),
            args,
            ret_sort,
        }
    }

    /// Uninterpreted function declaration.
    pub fn uf_decl(name: impl Into<String>, arg_sorts: Vec<SmtSort>, ret_sort: SmtSort) -> Self {
        SmtExpr::UFDecl {
            name: name.into(),
            arg_sorts,
            ret_sort,
        }
    }

    // -- Bounded quantifier constructors --

    /// Bounded universal quantifier: `forall var in [lower, upper). body`.
    ///
    /// The bound variable has bitvector width `var_width`. During concrete evaluation,
    /// the quantifier is unrolled: for each value `v` in `[lower, upper)`, `body` is
    /// evaluated with `var` bound to `v`. All must be true for the result to be true.
    ///
    /// Maximum unrolling bound: 256 iterations. Exceeding this returns an eval error.
    pub fn forall(
        var: impl Into<String>,
        var_width: u32,
        lower: Self,
        upper: Self,
        body: Self,
    ) -> Self {
        SmtExpr::ForAll {
            var: var.into(),
            var_width,
            lower: Arc::new(lower),
            upper: Arc::new(upper),
            body: Arc::new(body),
        }
    }

    /// Bounded existential quantifier: `exists var in [lower, upper). body`.
    ///
    /// The bound variable has bitvector width `var_width`. During concrete evaluation,
    /// the quantifier is unrolled: for each value `v` in `[lower, upper)`, `body` is
    /// evaluated with `var` bound to `v`. At least one must be true for the result to be true.
    ///
    /// Maximum unrolling bound: 256 iterations. Exceeding this returns an eval error.
    pub fn exists(
        var: impl Into<String>,
        var_width: u32,
        lower: Self,
        upper: Self,
        body: Self,
    ) -> Self {
        SmtExpr::Exists {
            var: var.into(),
            var_width,
            lower: Arc::new(lower),
            upper: Arc::new(upper),
            body: Arc::new(body),
        }
    }

    /// Return the bitvector width of this expression, or an error for Bool-sorted expressions.
    pub fn try_bv_width(&self) -> Result<u32, SmtError> {
        match self {
            SmtExpr::Var { width, .. } => Ok(*width),
            SmtExpr::BvConst { width, .. } => Ok(*width),
            SmtExpr::BvAdd { width, .. } => Ok(*width),
            SmtExpr::BvSub { width, .. } => Ok(*width),
            SmtExpr::BvMul { width, .. } => Ok(*width),
            SmtExpr::BvSDiv { width, .. } => Ok(*width),
            SmtExpr::BvUDiv { width, .. } => Ok(*width),
            SmtExpr::BvURem { width, .. } => Ok(*width),
            SmtExpr::TrapIfZero { width, .. } => Ok(*width),
            SmtExpr::BvNeg { width, .. } => Ok(*width),
            SmtExpr::Extract { width, .. } => Ok(*width),
            SmtExpr::BvAnd { width, .. } => Ok(*width),
            SmtExpr::BvOr { width, .. } => Ok(*width),
            SmtExpr::BvXor { width, .. } => Ok(*width),
            SmtExpr::BvShl { width, .. } => Ok(*width),
            SmtExpr::BvLshr { width, .. } => Ok(*width),
            SmtExpr::BvAshr { width, .. } => Ok(*width),
            SmtExpr::Concat { width, .. } => Ok(*width),
            SmtExpr::ZeroExtend { width, .. } => Ok(*width),
            SmtExpr::SignExtend { width, .. } => Ok(*width),
            SmtExpr::Ite { then_expr, .. } => then_expr.try_bv_width(),
            // Array select returns the element sort; if it's BV, extract width.
            SmtExpr::Select { array, .. } => {
                if let SmtSort::Array(_, elem_sort) = array.sort() {
                    elem_sort.bv_width().ok_or(SmtError::BoolHasNoWidth)
                } else {
                    Err(SmtError::BoolHasNoWidth)
                }
            }
            // UF returns its declared sort.
            SmtExpr::UF { ret_sort, .. } => ret_sort.bv_width().ok_or(SmtError::BoolHasNoWidth),
            // A memory load produces a value of the destination (result) width.
            SmtExpr::MemLoad { result_width, .. } => Ok(*result_width),
            // FP-to-BV conversions produce bitvectors.
            SmtExpr::FPToSBv { width, .. } | SmtExpr::FPToUBv { width, .. } => Ok(*width),
            SmtExpr::BoolConst(_)
            | SmtExpr::Eq { .. }
            | SmtExpr::Not { .. }
            | SmtExpr::BvSlt { .. }
            | SmtExpr::BvSge { .. }
            | SmtExpr::BvSgt { .. }
            | SmtExpr::BvSle { .. }
            | SmtExpr::BvUlt { .. }
            | SmtExpr::BvUge { .. }
            | SmtExpr::BvUgt { .. }
            | SmtExpr::BvUle { .. }
            | SmtExpr::And { .. }
            | SmtExpr::Or { .. }
            | SmtExpr::FPEq { .. }
            | SmtExpr::FPLt { .. }
            | SmtExpr::FPGt { .. }
            | SmtExpr::FPGe { .. }
            | SmtExpr::FPLe { .. }
            | SmtExpr::FPIsNaN { .. }
            | SmtExpr::FPIsInf { .. }
            | SmtExpr::FPIsZero { .. }
            | SmtExpr::FPIsNormal { .. }
            | SmtExpr::ForAll { .. }
            | SmtExpr::Exists { .. } => Err(SmtError::BoolHasNoWidth),
            // FP / array / UF decl nodes have no BV width.
            SmtExpr::FPAdd { .. }
            | SmtExpr::FPSub { .. }
            | SmtExpr::FPMul { .. }
            | SmtExpr::FPDiv { .. }
            | SmtExpr::FPNeg { .. }
            | SmtExpr::FPAbs { .. }
            | SmtExpr::FPSqrt { .. }
            | SmtExpr::FPRoundToIntegral { .. }
            | SmtExpr::FPFma { .. }
            | SmtExpr::FPConst { .. }
            | SmtExpr::BvToFP { .. }
            | SmtExpr::FPToFP { .. }
            | SmtExpr::BvBitsToFP { .. }
            | SmtExpr::Store { .. }
            | SmtExpr::ConstArray { .. }
            | SmtExpr::UFDecl { .. } => Err(SmtError::BoolHasNoWidth),
        }
    }

    /// Return the bitvector width of this expression.
    ///
    /// # Panics
    ///
    /// Panics if called on a Bool-sorted expression (comparisons, logical ops).
    /// Callers that may encounter Bool expressions should use [`try_bv_width`]
    /// instead.
    pub fn bv_width(&self) -> u32 {
        self.try_bv_width().expect(
            "bv_width called on Bool-sorted expression; use try_bv_width() for fallible access",
        )
    }

    /// Return the sort of this expression.
    pub fn sort(&self) -> SmtSort {
        match self {
            SmtExpr::BoolConst(_)
            | SmtExpr::Eq { .. }
            | SmtExpr::Not { .. }
            | SmtExpr::BvSlt { .. }
            | SmtExpr::BvSge { .. }
            | SmtExpr::BvSgt { .. }
            | SmtExpr::BvSle { .. }
            | SmtExpr::BvUlt { .. }
            | SmtExpr::BvUge { .. }
            | SmtExpr::BvUgt { .. }
            | SmtExpr::BvUle { .. }
            | SmtExpr::And { .. }
            | SmtExpr::Or { .. }
            | SmtExpr::FPEq { .. }
            | SmtExpr::FPLt { .. }
            | SmtExpr::FPGt { .. }
            | SmtExpr::FPGe { .. }
            | SmtExpr::FPLe { .. }
            | SmtExpr::FPIsNaN { .. }
            | SmtExpr::FPIsInf { .. }
            | SmtExpr::FPIsZero { .. }
            | SmtExpr::FPIsNormal { .. }
            | SmtExpr::ForAll { .. }
            | SmtExpr::Exists { .. } => SmtSort::Bool,
            // Floating-point expressions
            SmtExpr::FPAdd { lhs, .. }
            | SmtExpr::FPSub { lhs, .. }
            | SmtExpr::FPMul { lhs, .. }
            | SmtExpr::FPDiv { lhs, .. } => lhs.sort(),
            SmtExpr::FPSqrt { operand, .. }
            | SmtExpr::FPRoundToIntegral { operand, .. }
            | SmtExpr::FPAbs { operand }
            | SmtExpr::FPNeg { operand } => operand.sort(),
            SmtExpr::FPFma { a, .. } => a.sort(),
            SmtExpr::FPConst { eb, sb, .. } => SmtSort::FloatingPoint(*eb, *sb),
            SmtExpr::BvToFP { eb, sb, .. }
            | SmtExpr::FPToFP { eb, sb, .. }
            | SmtExpr::BvBitsToFP { eb, sb, .. } => SmtSort::FloatingPoint(*eb, *sb),
            // FP-to-BV conversions produce bitvectors.
            SmtExpr::FPToSBv { width, .. } | SmtExpr::FPToUBv { width, .. } => {
                SmtSort::BitVec(*width)
            }
            // Array expressions
            SmtExpr::Store { array, .. } => array.sort(),
            SmtExpr::ConstArray { index_sort, value } => {
                SmtSort::Array(Box::new(index_sort.clone()), Box::new(value.sort()))
            }
            SmtExpr::Select { array, .. } => {
                // Element sort of the array
                if let SmtSort::Array(_, elem_sort) = array.sort() {
                    *elem_sort
                } else {
                    // Fallback: shouldn't happen for well-typed expressions.
                    SmtSort::Bool
                }
            }
            // Uninterpreted functions
            SmtExpr::UF { ret_sort, .. } => ret_sort.clone(),
            SmtExpr::UFDecl { ret_sort, .. } => ret_sort.clone(),
            // All BV expressions
            _ => SmtSort::BitVec(self.bv_width()),
        }
    }

    /// Collect all free variable names referenced in this expression.
    pub fn free_vars(&self) -> Vec<String> {
        let mut vars = Vec::new();
        self.collect_vars(&mut vars);
        vars.sort();
        vars.dedup();
        vars
    }

    fn collect_vars(&self, vars: &mut Vec<String>) {
        match self {
            SmtExpr::Var { name, .. } => vars.push(name.clone()),
            SmtExpr::BvConst { .. } | SmtExpr::BoolConst(_) | SmtExpr::FPConst { .. } => {}
            SmtExpr::BvAdd { lhs, rhs, .. }
            | SmtExpr::BvSub { lhs, rhs, .. }
            | SmtExpr::BvMul { lhs, rhs, .. }
            | SmtExpr::BvSDiv { lhs, rhs, .. }
            | SmtExpr::BvUDiv { lhs, rhs, .. }
            | SmtExpr::BvURem { lhs, rhs, .. }
            | SmtExpr::BvAnd { lhs, rhs, .. }
            | SmtExpr::BvOr { lhs, rhs, .. }
            | SmtExpr::BvXor { lhs, rhs, .. }
            | SmtExpr::BvShl { lhs, rhs, .. }
            | SmtExpr::BvLshr { lhs, rhs, .. }
            | SmtExpr::BvAshr { lhs, rhs, .. }
            | SmtExpr::Eq { lhs, rhs }
            | SmtExpr::BvSlt { lhs, rhs, .. }
            | SmtExpr::BvSge { lhs, rhs, .. }
            | SmtExpr::BvSgt { lhs, rhs, .. }
            | SmtExpr::BvSle { lhs, rhs, .. }
            | SmtExpr::BvUlt { lhs, rhs, .. }
            | SmtExpr::BvUge { lhs, rhs, .. }
            | SmtExpr::BvUgt { lhs, rhs, .. }
            | SmtExpr::BvUle { lhs, rhs, .. }
            | SmtExpr::And { lhs, rhs }
            | SmtExpr::Or { lhs, rhs }
            | SmtExpr::FPEq { lhs, rhs }
            | SmtExpr::FPLt { lhs, rhs }
            | SmtExpr::FPGt { lhs, rhs }
            | SmtExpr::FPGe { lhs, rhs }
            | SmtExpr::FPLe { lhs, rhs } => {
                lhs.collect_vars(vars);
                rhs.collect_vars(vars);
            }
            SmtExpr::FPAdd { lhs, rhs, .. }
            | SmtExpr::FPSub { lhs, rhs, .. }
            | SmtExpr::FPMul { lhs, rhs, .. }
            | SmtExpr::FPDiv { lhs, rhs, .. } => {
                lhs.collect_vars(vars);
                rhs.collect_vars(vars);
            }
            SmtExpr::FPFma { a, b, c, .. } => {
                a.collect_vars(vars);
                b.collect_vars(vars);
                c.collect_vars(vars);
            }
            SmtExpr::BvNeg { operand, .. }
            | SmtExpr::Not { operand }
            | SmtExpr::Extract { operand, .. }
            | SmtExpr::ZeroExtend { operand, .. }
            | SmtExpr::SignExtend { operand, .. }
            | SmtExpr::FPNeg { operand }
            | SmtExpr::FPAbs { operand }
            | SmtExpr::FPSqrt { operand, .. }
            | SmtExpr::FPRoundToIntegral { operand, .. }
            | SmtExpr::FPIsNaN { operand }
            | SmtExpr::FPIsInf { operand }
            | SmtExpr::FPIsZero { operand }
            | SmtExpr::FPIsNormal { operand }
            | SmtExpr::FPToSBv { operand, .. }
            | SmtExpr::FPToUBv { operand, .. }
            | SmtExpr::BvToFP { operand, .. }
            | SmtExpr::FPToFP { operand, .. }
            | SmtExpr::BvBitsToFP { operand, .. } => {
                operand.collect_vars(vars);
            }
            SmtExpr::Concat { hi, lo, .. } => {
                hi.collect_vars(vars);
                lo.collect_vars(vars);
            }
            SmtExpr::TrapIfZero { guard, value, .. } => {
                guard.collect_vars(vars);
                value.collect_vars(vars);
            }
            SmtExpr::Ite {
                cond,
                then_expr,
                else_expr,
            } => {
                cond.collect_vars(vars);
                then_expr.collect_vars(vars);
                else_expr.collect_vars(vars);
            }
            SmtExpr::Select { array, index } => {
                array.collect_vars(vars);
                index.collect_vars(vars);
            }
            SmtExpr::MemLoad { addr, .. } => {
                addr.collect_vars(vars);
            }
            SmtExpr::Store {
                array,
                index,
                value,
            } => {
                array.collect_vars(vars);
                index.collect_vars(vars);
                value.collect_vars(vars);
            }
            SmtExpr::ConstArray { value, .. } => {
                value.collect_vars(vars);
            }
            SmtExpr::UF { args, .. } => {
                for arg in args {
                    arg.collect_vars(vars);
                }
            }
            SmtExpr::UFDecl { .. } => {}
            SmtExpr::ForAll {
                var,
                lower,
                upper,
                body,
                ..
            }
            | SmtExpr::Exists {
                var,
                lower,
                upper,
                body,
                ..
            } => {
                lower.collect_vars(vars);
                upper.collect_vars(vars);
                // Collect vars from body, but the bound variable is not free.
                let mut body_vars = Vec::new();
                body.collect_vars(&mut body_vars);
                for v in body_vars {
                    if v != *var {
                        vars.push(v);
                    }
                }
            }
        }
    }

    /// Apply `f` to each immediate sub-expression. Used by structural walkers
    /// (e.g. [`collect_trap_poison_decls`]) that need to recurse without
    /// re-matching the whole variant surface at every call site.
    pub fn for_each_child(&self, f: &mut dyn FnMut(&SmtExpr)) {
        match self {
            SmtExpr::Var { .. }
            | SmtExpr::BvConst { .. }
            | SmtExpr::BoolConst(_)
            | SmtExpr::FPConst { .. }
            | SmtExpr::UFDecl { .. } => {}
            SmtExpr::BvAdd { lhs, rhs, .. }
            | SmtExpr::BvSub { lhs, rhs, .. }
            | SmtExpr::BvMul { lhs, rhs, .. }
            | SmtExpr::BvSDiv { lhs, rhs, .. }
            | SmtExpr::BvUDiv { lhs, rhs, .. }
            | SmtExpr::BvURem { lhs, rhs, .. }
            | SmtExpr::BvAnd { lhs, rhs, .. }
            | SmtExpr::BvOr { lhs, rhs, .. }
            | SmtExpr::BvXor { lhs, rhs, .. }
            | SmtExpr::BvShl { lhs, rhs, .. }
            | SmtExpr::BvLshr { lhs, rhs, .. }
            | SmtExpr::BvAshr { lhs, rhs, .. }
            | SmtExpr::Eq { lhs, rhs }
            | SmtExpr::BvSlt { lhs, rhs, .. }
            | SmtExpr::BvSge { lhs, rhs, .. }
            | SmtExpr::BvSgt { lhs, rhs, .. }
            | SmtExpr::BvSle { lhs, rhs, .. }
            | SmtExpr::BvUlt { lhs, rhs, .. }
            | SmtExpr::BvUge { lhs, rhs, .. }
            | SmtExpr::BvUgt { lhs, rhs, .. }
            | SmtExpr::BvUle { lhs, rhs, .. }
            | SmtExpr::And { lhs, rhs }
            | SmtExpr::Or { lhs, rhs }
            | SmtExpr::FPEq { lhs, rhs }
            | SmtExpr::FPLt { lhs, rhs }
            | SmtExpr::FPGt { lhs, rhs }
            | SmtExpr::FPGe { lhs, rhs }
            | SmtExpr::FPLe { lhs, rhs } => {
                f(lhs);
                f(rhs);
            }
            SmtExpr::FPAdd { lhs, rhs, .. }
            | SmtExpr::FPSub { lhs, rhs, .. }
            | SmtExpr::FPMul { lhs, rhs, .. }
            | SmtExpr::FPDiv { lhs, rhs, .. } => {
                f(lhs);
                f(rhs);
            }
            SmtExpr::FPFma { a, b, c, .. } => {
                f(a);
                f(b);
                f(c);
            }
            SmtExpr::BvNeg { operand, .. }
            | SmtExpr::Not { operand }
            | SmtExpr::Extract { operand, .. }
            | SmtExpr::ZeroExtend { operand, .. }
            | SmtExpr::SignExtend { operand, .. }
            | SmtExpr::FPNeg { operand }
            | SmtExpr::FPAbs { operand }
            | SmtExpr::FPSqrt { operand, .. }
            | SmtExpr::FPRoundToIntegral { operand, .. }
            | SmtExpr::FPIsNaN { operand }
            | SmtExpr::FPIsInf { operand }
            | SmtExpr::FPIsZero { operand }
            | SmtExpr::FPIsNormal { operand }
            | SmtExpr::FPToSBv { operand, .. }
            | SmtExpr::FPToUBv { operand, .. }
            | SmtExpr::BvToFP { operand, .. }
            | SmtExpr::FPToFP { operand, .. }
            | SmtExpr::BvBitsToFP { operand, .. } => f(operand),
            SmtExpr::Concat { hi, lo, .. } => {
                f(hi);
                f(lo);
            }
            SmtExpr::TrapIfZero { guard, value, .. } => {
                f(guard);
                f(value);
            }
            SmtExpr::Ite {
                cond,
                then_expr,
                else_expr,
            } => {
                f(cond);
                f(then_expr);
                f(else_expr);
            }
            SmtExpr::Select { array, index } => {
                f(array);
                f(index);
            }
            SmtExpr::MemLoad { addr, .. } => f(addr),
            SmtExpr::Store {
                array,
                index,
                value,
            } => {
                f(array);
                f(index);
                f(value);
            }
            SmtExpr::ConstArray { value, .. } => f(value),
            SmtExpr::UF { args, .. } => {
                for arg in args {
                    f(arg);
                }
            }
            SmtExpr::ForAll {
                lower, upper, body, ..
            }
            | SmtExpr::Exists {
                lower, upper, body, ..
            } => {
                f(lower);
                f(upper);
                f(body);
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Concrete evaluation
// ---------------------------------------------------------------------------

/// Evaluation result: bitvector, boolean, floating-point, or array.
#[derive(Debug, Clone, PartialEq)]
pub enum EvalResult {
    Bv(u64),
    /// Wide bitvector (65-128 bits). Used for 128-bit NEON vector intermediates.
    ///
    /// NEON operations produce 128-bit results via `Concat`. The lane-extraction
    /// pattern (`Extract` after `Concat`) reduces back to <= 64 bits for final
    /// comparison. `Bv128` exists to carry the intermediate without overflow.
    Bv128(u128),
    Bool(bool),
    /// Floating-point value stored as f64 (sufficient for FP16/FP32/FP64).
    Float(f64),
    /// Array value: maps bitvector index (u64) to EvalResult.
    /// The default value is used for indices not in the map.
    Array {
        entries: HashMap<u64, Box<EvalResult>>,
        default: Box<EvalResult>,
    },
    /// POISON: the result of a hardware operation that TRAPS / has NO defined
    /// value at this input (e.g. x86 `IDIV`/`DIV` on a zero divisor `#DE`-traps,
    /// or signed `INT_MIN / -1` overflow). Poison is DISTINCT from every defined
    /// value AND from itself under [`semantically_equal`]: an obligation whose
    /// machine side is Poison while the source side is any defined value (incl.
    /// the source's own div-by-zero contract sentinel) therefore REFUTES at that
    /// input. This is what makes a `divisor != 0` precondition LOAD-BEARING in the
    /// native evaluator — without the precondition the trap point is sampled and
    /// Poison ≠ sentinel ⇒ counterexample (closes the D survivor, fault 5a).
    Poison,
}

impl Eq for EvalResult {}

impl EvalResult {
    pub fn as_u64(self) -> u64 {
        match self {
            EvalResult::Bv(v) => v,
            EvalResult::Bv128(v) => v as u64,
            EvalResult::Bool(b) => b as u64,
            EvalResult::Float(f) => f.to_bits(),
            EvalResult::Array { .. } => 0, // arrays don't have a scalar representation
            // Poison has no defined scalar value; surface a distinctive sentinel.
            // It is never compared as a number (semantically_equal rejects it),
            // so this only matters if poison leaks into an arithmetic context — a
            // distinctive value makes such a leak easy to spot in a counterexample.
            EvalResult::Poison => u64::MAX,
        }
    }

    /// Convert to u128. `Bv` values are zero-extended.
    pub fn as_u128(self) -> u128 {
        match self {
            EvalResult::Bv(v) => v as u128,
            EvalResult::Bv128(v) => v,
            EvalResult::Bool(b) => b as u128,
            EvalResult::Float(f) => f.to_bits() as u128,
            EvalResult::Array { .. } => 0,
            EvalResult::Poison => u128::MAX,
        }
    }

    pub fn as_bool(self) -> bool {
        match self {
            EvalResult::Bool(b) => b,
            EvalResult::Bv(v) => v != 0,
            EvalResult::Bv128(v) => v != 0,
            EvalResult::Float(f) => f != 0.0,
            EvalResult::Array { .. } => false,
            EvalResult::Poison => false,
        }
    }

    pub fn as_f64(&self) -> f64 {
        match self {
            EvalResult::Float(f) => *f,
            EvalResult::Bv(v) => *v as f64,
            EvalResult::Bv128(v) => *v as f64,
            EvalResult::Bool(b) => {
                if *b {
                    1.0
                } else {
                    0.0
                }
            }
            EvalResult::Array { .. } => 0.0,
            EvalResult::Poison => f64::NAN,
        }
    }

    /// Semantic equality that treats NaN values as equal to other NaN values.
    ///
    /// The default `PartialEq`/`Eq` derive compares `f64` with `==`, which
    /// is IEEE-754 equality: `NaN != NaN`. For verification of FP lowerings,
    /// "both sides produce NaN" is a passing result — the trust_ir and the target
    /// instruction agree that the operation is not a number, which is the
    /// strongest semantic guarantee available without tracking exact payload
    /// bits. This method returns `true` in that case.
    ///
    /// For non-NaN floats, bit-level equality is used (so +0.0 == +0.0 but
    /// +0.0 != -0.0), matching IEEE-754 comparison except for the NaN rule.
    /// For non-Float variants, ordinary `==` is used.
    ///
    /// # Rationale
    ///
    /// IEEE-754 FDIV(0.0, 0.0) yields NaN; so does AArch64 `FDIV`. Rust's
    /// default `PartialEq` on `f64` returns false for NaN != NaN, causing
    /// the evaluator to flag a spurious counterexample even though both
    /// sides produce the canonical NaN result. See #388.
    pub fn semantically_equal(&self, other: &Self) -> bool {
        match (self, other) {
            // POISON is unequal to EVERYTHING, including another Poison. A trapping
            // hardware op (x86 IDIV/DIV on a zero divisor) has NO defined result;
            // equating it to any value — even the source's div-by-zero contract
            // sentinel, even another trap — would be unsound. So if EITHER side is
            // Poison the obligation must REFUTE at that input. This is what makes the
            // divisor!=0 precondition load-bearing in the native lane (see #79).
            (EvalResult::Poison, _) | (_, EvalResult::Poison) => false,
            (EvalResult::Float(a), EvalResult::Float(b)) => {
                // Both NaN = semantically equal.
                if a.is_nan() && b.is_nan() {
                    return true;
                }
                // Otherwise compare by bit pattern so +0.0 == +0.0 but
                // +0.0 != -0.0 and signalling vs quiet NaN (already handled
                // above) stay distinct for finite values.
                a.to_bits() == b.to_bits()
            }
            _ => self == other,
        }
    }
}

/// Mask a value to the given bitvector width.
pub fn mask(value: u64, width: u32) -> u64 {
    if width >= 64 {
        value
    } else {
        value & ((1u64 << width) - 1)
    }
}

/// Deterministic name of the fresh, UNCONSTRAINED poison constant a
/// [`SmtExpr::TrapIfZero`] node lowers to in the SMT-LIB / ay lane. It is derived
/// from a structural hash of `(guard, value, width)` so the same trap node always
/// produces the same constant name (so the declaration and the use agree), while
/// distinct trap nodes get distinct constants. The constant is left UNCONSTRAINED
/// so the solver may assign it any value — exactly the "no defined result" trap
/// semantics — and therefore cannot prove the machine side equals the source side
/// at `guard == 0` unless the obligation rules that point out (divisor != 0).
pub fn trap_poison_const_name(guard: &SmtExpr, value: &SmtExpr, width: u32) -> String {
    use std::hash::{Hash, Hasher};
    let mut h = std::collections::hash_map::DefaultHasher::new();
    format!("{guard}").hash(&mut h);
    format!("{value}").hash(&mut h);
    width.hash(&mut h);
    format!("trap_poison_{:016x}_{}", h.finish(), width)
}

/// Walk `expr` and collect, for every [`SmtExpr::TrapIfZero`] node, the
/// `(constant_name, width)` of the fresh poison constant it lowers to. The
/// SMT-LIB serializer declares each as an unconstrained `(declare-const name (_
/// BitVec width))` so the Display form's reference resolves. Deduplicated.
pub fn collect_trap_poison_decls(expr: &SmtExpr) -> Vec<(String, u32)> {
    let mut out = Vec::new();
    collect_trap_poison_decls_into(expr, &mut out);
    out.sort();
    out.dedup();
    out
}

fn collect_trap_poison_decls_into(expr: &SmtExpr, out: &mut Vec<(String, u32)>) {
    if let SmtExpr::TrapIfZero {
        guard,
        value,
        width,
    } = expr
    {
        out.push((trap_poison_const_name(guard, value, *width), *width));
    }
    expr.for_each_child(&mut |child| collect_trap_poison_decls_into(child, out));
}

/// Deterministic avalanche hash of a 64-bit address, the CONCRETE instance of the
/// "memory contents" function `f` used by [`SmtExpr::MemLoad`]. This is the
/// splitmix64 finalizer: a BIJECTION on `u64` with strong avalanche (each input
/// bit affects ~half the output bits). Because it is a bijection, distinct
/// addresses map to distinct values, so a wrong effective address yields a
/// different loaded value for sampled inputs ⇒ the obligation REFUTES. Because it
/// is a (pure) function, equal addresses always yield equal values ⇒ a correct
/// lowering (machine EA == IR EA) discharges Valid. Avalanche ensures even a tiny
/// EA perturbation (a +1 displacement) flips low output bits, so a narrow load
/// width still distinguishes the addresses.
fn mem_load_mix(addr: u64) -> u64 {
    let mut z = addr.wrapping_add(0x9e37_79b9_7f4a_7c15);
    z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    z ^ (z >> 31)
}

/// Mask a 128-bit value to the given bitvector width.
fn mask128(value: u128, width: u32) -> u128 {
    if width >= 128 {
        value
    } else {
        value & ((1u128 << width) - 1)
    }
}

/// Sign-extend a `width`-bit value stored in a u64 to i64.
fn sign_extend(value: u64, width: u32) -> i64 {
    if width == 0 {
        return 0;
    }
    if width >= 64 {
        return value as i64;
    }
    let shift = 64 - width;
    ((value << shift) as i64) >> shift
}

/// Round a floating-point value to an integral value in the direction selected by
/// `rm`, the FIRST step of every FP->int conversion (`fp.to_sbv` / `fp.to_ubv`).
///
/// This is the rounding half of the IEEE-754 `fp.to_*bv` semantics: round the
/// operand to an integral floating-point value per the rounding mode, THEN convert
/// to the integer domain (with saturation, handled by the width-typed `as` cast in
/// the caller). NaN / +-Inf pass through unchanged (the caller's `as` cast maps NaN
/// -> 0 and +-Inf -> the saturated extreme). Modeling `rm` here is what lets an
/// RNE-for-RTZ lowering bug REFUTE: a non-integral tie input (1.5) rounds to 1
/// under RTZ but 2 under RNE.
fn round_fp_by_mode(a: f64, rm: RoundingMode) -> f64 {
    if a.is_nan() || a.is_infinite() {
        return a;
    }
    match rm {
        RoundingMode::RTZ => a.trunc(),
        RoundingMode::RNE => a.round_ties_even(),
        RoundingMode::RNA => a.round(),
        RoundingMode::RTP => a.ceil(),
        RoundingMode::RTN => a.floor(),
    }
}

/// Sign-extend a `width`-bit value stored in a u128 to i128.
fn sign_extend128(value: u128, width: u32) -> i128 {
    if width == 0 {
        return 0;
    }
    if width >= 128 {
        return value as i128;
    }
    let shift = 128 - width;
    ((value << shift) as i128) >> shift
}

// ===========================================================================
// FP16 conversion path — SILICON-VALIDATED INTEGER-ONLY BIT-MODEL (campaign #4b).
// ===========================================================================
//
// THE FINDING this repairs: trust-cg's FP16 model was a BESPOKE, NON-silicon-
// validated pair fp16_bits_to_f64 / f64_to_fp16_bits (plus round_to_fp16_value
// and an ad-hoc round_shift_right_ties_to_even), built from native f64 arithmetic
// (`2f64.powi(...)`, `frac as f64 / 1024.0`, ...). The scout flagged it as the FP
// weak link: it was the only FP model on the verification path with NO hardware
// validation, and any divergence from the M4's ARMv8.2-FP16 behaviour (rounding,
// subnormal handling, NaN payload) was invisible.
//
// IT IS NOW REPLACED, end-to-end, by the INTEGER-ONLY, M4-silicon-validated FP16
// bit-model in fp_bitmodel.rs (fcvt_h_to_d / fcvt_d_to_h, ported from the Clean
// proofs/aarch64_fp16.lean defs and asserted == real Apple M4 results for the
// 200+ aarch64_fp16_chip.lean `:= rfl` facts by tests/fp_bitmodel_bridge.rs).
// fp16_bits_to_f64 / f64_to_fp16_bits / round_shift_right_ties_to_even are GONE.
//
// The EvalResult::Float(f64) carrier holds the f64-WIDENING of an fp16 value.
// Because EVERY fp16 value is EXACTLY representable in f64, the widen is exact and
// loss-free, so round_to_fp16_value / decode_fp16_const_bits go through the
// bit-model with no host-FPU rounding round-trip (only NaN payloads are quieted by
// the narrow, which is exactly the ARM behaviour the chip facts pin).

/// Round an f64-carrier value to the nearest fp16 value, returned as the f64
/// WIDENING of that fp16 (so it can ride the f64 carrier). Routes through the
/// silicon-validated bit-model: narrow d->h (RNE) then widen h->d (EXACT).
fn round_to_fp16_value(value: f64) -> f64 {
    let h = crate::fp_bitmodel::fcvt_d_to_h(value.to_bits());
    f64::from_bits(crate::fp_bitmodel::fcvt_h_to_d(h))
}

/// Decode an FP16 constant. `bits <= 0xFFFF` is a RAW fp16 bit pattern (widened
/// to f64 EXACTLY via the bit-model). A wider `bits` is an f64 bit pattern that
/// is first narrowed to fp16 (RNE) — the legacy const-encoding path.
fn decode_fp16_const_bits(bits: u64) -> f64 {
    if bits <= u16::MAX as u64 {
        // RAW fp16 bits -> exact f64 widening via the silicon-validated bit-model.
        f64::from_bits(crate::fp_bitmodel::fcvt_h_to_d(bits))
    } else {
        round_to_fp16_value(f64::from_bits(bits))
    }
}

fn round_fp_result_if_fp16(value: f64, sort: &SmtSort) -> f64 {
    if matches!(sort, SmtSort::FloatingPoint(5, 11)) {
        round_to_fp16_value(value)
    } else {
        value
    }
}

/// GUARDED-SWAP gate (host-FPU eviction, campaign #89). For a binary64 operand
/// sort, the `EvalResult::Float(f64)` carrier holds the EXACT operand bit pattern
/// (`f64::to_bits()` is loss-free and the re-wrap `f64::from_bits()` is too — no
/// FPU rounding round-trip), so the FP op CAN be computed by the INTEGER-ONLY
/// bit-model (`fp_bitmodel`, silicon-validated by tests/fp_bitmodel_bridge.rs)
/// instead of native f64 arithmetic, evicting the host FPU from the binary64 FP-
/// verification path. For binary32 (sort `(8,24)`) the carrier is the f64-WIDENED
/// value, so re-deriving the f32 bit pattern would need an `as f32` FPU round-trip
/// — that case is HONEST-DEFERRED to the native path until the carrier is widened
/// to hold raw bits (Pending: B-aarch64-fp manifest entry). Returns true iff
/// `sort` is binary64.
#[inline]
fn bitmodel_handles(sort: &SmtSort) -> bool {
    matches!(sort, SmtSort::FloatingPoint(11, 53))
}

/// FP16 GUARDED-SWAP gate (campaign #4b). For a binary16 sort, the
/// `EvalResult::Float(f64)` carrier holds the f64-WIDENING of the fp16 value.
/// Because EVERY fp16 value is EXACTLY representable in f64, that widening is
/// loss-free, so the raw fp16 bits are recoverable by `fcvt_d_to_h(carrier.bits)`
/// WITHOUT any host-FPU round-trip (the narrow is the silicon-validated integer-
/// only bit-model, not an `as f16`). The fp16 op is then run at F16 in the integer
/// bit-model and the result widened back to f64 for the carrier — host FPU EVICTED
/// for fp16 FADD/FSUB/FMUL/FNEG/FABS. (The only information the narrow drops is an
/// sNaN payload, which ARM quiets on every fp16 op anyway, matching the chip.)
/// Returns true iff `sort` is binary16.
#[inline]
fn fp16_handles(sort: &SmtSort) -> bool {
    matches!(sort, SmtSort::FloatingPoint(5, 11))
}

/// Recover the raw fp16 bits from an f64-carrier value (the exact narrow; no host
/// FPU — the silicon-validated integer-only bit-model).
#[inline]
fn fp16_bits_of(value: f64) -> u64 {
    crate::fp_bitmodel::fcvt_d_to_h(value.to_bits())
}

/// Widen raw fp16 bits back to the f64 carrier (EXACT; integer-only bit-model).
#[inline]
fn fp16_to_carrier(h: u64) -> f64 {
    f64::from_bits(crate::fp_bitmodel::fcvt_h_to_d(h))
}

/// f32 GUARDED-SWAP gate (campaign #94, the binary32 eval-carrier residual). For a
/// binary32 sort `(8,24)`, the `EvalResult::Float(f64)` carrier holds the EXACT
/// f64-WIDENING of the f32 value. That widening is loss-free (EVERY f32 value is
/// exactly representable in f64): every construction site stores exactly such a
/// widening — `FPConst` decodes `f32::from_bits(bits) as f64`; `BvToFP` /`FPToFP`
/// store `(.. as f32) as f64`. Because the widening is exact, the raw f32 bits are
/// recoverable from the carrier by the INTEGER-ONLY bit-model narrow
/// `fcvt_narrow(carrier.bits)` WITHOUT any host-FPU `as f32` round-trip (the narrow
/// is the silicon-validated integer-only model, not an `as f16`/`as f32`). The f32
/// op then runs at F32 in the integer bit-model and the result is widened back to
/// the f64 carrier via the integer-only `fcvt_widen` — host FPU EVICTED for f32
/// FADD/FSUB/FMUL/FDIV/FNEG/FABS/FSQRT. The narrow/op/widen round-trip is bit-exact
/// vs the host FPU across a 280M-input differential fuzz (examples-driven), and the
/// F32 bit-model itself is silicon-validated by the bridge (fdiv32/fsqrt32/fadd/...
/// against real-M4 facts). Returns true iff `sort` is binary32.
#[inline]
fn f32_handles(sort: &SmtSort) -> bool {
    matches!(sort, SmtSort::FloatingPoint(8, 24))
}

/// Recover the raw f32 bits from an f64-carrier value (the exact narrow; no host
/// FPU — the silicon-validated integer-only bit-model). The carrier is always the
/// exact f64-widening of an f32 value (see [`f32_handles`]), so this narrow is
/// loss-free and round-trips the original f32 bits exactly.
#[inline]
fn f32_bits_of(value: f64) -> u64 {
    crate::fp_bitmodel::fcvt_narrow(value.to_bits())
}

/// Widen raw f32 bits back to the f64 carrier (EXACT; integer-only bit-model).
#[inline]
fn f32_to_carrier(s: u64) -> f64 {
    f64::from_bits(crate::fp_bitmodel::fcvt_widen(s))
}

impl SmtExpr {
    /// Evaluate this expression under the given variable assignment (fallible).
    ///
    /// Variables map name -> u64 value (already masked to width).
    /// Returns `Err(SmtError::UndefinedVariable)` if a variable is not found.
    pub fn try_eval<E: EnvOps>(&self, env: &E) -> Result<EvalResult, SmtError> {
        match self {
            SmtExpr::Var { name, width } => {
                let v = env
                    .get_var(name)
                    .ok_or_else(|| SmtError::UndefinedVariable(name.clone()))?;
                Ok(EvalResult::Bv(mask(v, *width)))
            }
            SmtExpr::BvConst { value, width } => {
                if *width > 64 {
                    Ok(EvalResult::Bv128(*value as u128))
                } else {
                    Ok(EvalResult::Bv(mask(*value, *width)))
                }
            }
            SmtExpr::BoolConst(b) => Ok(EvalResult::Bool(*b)),

            SmtExpr::BvAdd { lhs, rhs, width } => {
                if *width > 64 {
                    let a = lhs.try_eval(env)?.as_u128();
                    let b = rhs.try_eval(env)?.as_u128();
                    Ok(EvalResult::Bv128(mask128(a.wrapping_add(b), *width)))
                } else {
                    let a = lhs.try_eval(env)?.as_u64();
                    let b = rhs.try_eval(env)?.as_u64();
                    Ok(EvalResult::Bv(mask(a.wrapping_add(b), *width)))
                }
            }
            SmtExpr::BvSub { lhs, rhs, width } => {
                if *width > 64 {
                    let a = lhs.try_eval(env)?.as_u128();
                    let b = rhs.try_eval(env)?.as_u128();
                    Ok(EvalResult::Bv128(mask128(a.wrapping_sub(b), *width)))
                } else {
                    let a = lhs.try_eval(env)?.as_u64();
                    let b = rhs.try_eval(env)?.as_u64();
                    Ok(EvalResult::Bv(mask(a.wrapping_sub(b), *width)))
                }
            }
            SmtExpr::BvMul { lhs, rhs, width } => {
                if *width > 64 {
                    let a = lhs.try_eval(env)?.as_u128();
                    let b = rhs.try_eval(env)?.as_u128();
                    Ok(EvalResult::Bv128(mask128(a.wrapping_mul(b), *width)))
                } else {
                    let a = lhs.try_eval(env)?.as_u64();
                    let b = rhs.try_eval(env)?.as_u64();
                    Ok(EvalResult::Bv(mask(a.wrapping_mul(b), *width)))
                }
            }
            SmtExpr::BvSDiv { lhs, rhs, width } => {
                // The DOUBLE-WIDTH dividend of an x86 IDIV reconstruction is a
                // 128-bit value (sext(rax, 128) for a 64-bit divide), so signed
                // division MUST support widths > 64 in i128 (a u64-truncated
                // division of the 128-bit dividend would silently give the WRONG
                // quotient and falsely pass — see x86_64_function_verifier Idiv).
                if *width > 64 {
                    let a = sign_extend128(lhs.try_eval(env)?.as_u128(), *width);
                    let b = sign_extend128(rhs.try_eval(env)?.as_u128(), *width);
                    if b == 0 {
                        Ok(EvalResult::Bv128(0))
                    } else if a == i128::MIN && b == -1 && *width >= 128 {
                        // Overflow: INT_MIN / -1 wraps to INT_MIN (gated out by
                        // the no-overflow precondition on real divide proofs).
                        Ok(EvalResult::Bv128(mask128(a as u128, *width)))
                    } else {
                        let result = a.wrapping_div(b);
                        Ok(EvalResult::Bv128(mask128(result as u128, *width)))
                    }
                } else {
                    let a = sign_extend(lhs.try_eval(env)?.as_u64(), *width);
                    let b = sign_extend(rhs.try_eval(env)?.as_u64(), *width);
                    if b == 0 {
                        // SMT-LIB: bvsdiv by zero is defined (returns all-ones
                        // for positive dividend, etc.). For verification we gate
                        // on b != 0 as a precondition, but we still need a defined
                        // value here. Return 0 as sentinel.
                        Ok(EvalResult::Bv(0))
                    } else if a == i64::MIN && b == -1 && *width == 64 {
                        // Overflow: INT_MIN / -1.
                        Ok(EvalResult::Bv(mask(a as u64, *width)))
                    } else {
                        let result = a.wrapping_div(b);
                        Ok(EvalResult::Bv(mask(result as u64, *width)))
                    }
                }
            }
            SmtExpr::BvUDiv { lhs, rhs, width } => {
                // Double-width (128-bit) unsigned dividend of an x86 DIV
                // reconstruction (zext(rax, 128) for a 64-bit divide). As with
                // BvSDiv a u64-truncated division would falsely pass.
                if *width > 64 {
                    let a = lhs.try_eval(env)?.as_u128();
                    let b = rhs.try_eval(env)?.as_u128();
                    Ok(EvalResult::Bv128(
                        a.checked_div(b)
                            .map(|quotient| mask128(quotient, *width))
                            .unwrap_or(0),
                    ))
                } else {
                    let a = lhs.try_eval(env)?.as_u64();
                    let b = rhs.try_eval(env)?.as_u64();
                    Ok(EvalResult::Bv(
                        a.checked_div(b)
                            .map(|quotient| mask(quotient, *width))
                            .unwrap_or(0),
                    ))
                }
            }
            SmtExpr::BvURem { lhs, rhs, width } => {
                let a = lhs.try_eval(env)?.as_u64();
                let b = rhs.try_eval(env)?.as_u64();
                if b == 0 {
                    // SMT-LIB defines bvurem by zero as the dividend.
                    Ok(EvalResult::Bv(mask(a, *width)))
                } else {
                    Ok(EvalResult::Bv(mask(a % b, *width)))
                }
            }
            SmtExpr::TrapIfZero { guard, value, .. } => {
                // FAITHFUL x86 IDIV/DIV #DE-trap model: at guard == 0 the hardware
                // has NO defined result, so we yield POISON (unequal to every
                // value, even the source's div-by-zero contract sentinel). Off the
                // trap point this is exactly the underlying defined `value`. This is
                // what makes the divisor!=0 precondition load-bearing in the native
                // lane: drop it and the divisor==0 sample yields Poison ⇒ REFUTE.
                let g = guard.try_eval(env)?;
                if matches!(g, EvalResult::Poison) || g.as_u128() == 0 {
                    Ok(EvalResult::Poison)
                } else {
                    value.try_eval(env)
                }
            }
            SmtExpr::BvAnd { lhs, rhs, width } => {
                if *width > 64 {
                    let a = lhs.try_eval(env)?.as_u128();
                    let b = rhs.try_eval(env)?.as_u128();
                    Ok(EvalResult::Bv128(mask128(a & b, *width)))
                } else {
                    let a = lhs.try_eval(env)?.as_u64();
                    let b = rhs.try_eval(env)?.as_u64();
                    Ok(EvalResult::Bv(mask(a & b, *width)))
                }
            }
            SmtExpr::BvOr { lhs, rhs, width } => {
                if *width > 64 {
                    let a = lhs.try_eval(env)?.as_u128();
                    let b = rhs.try_eval(env)?.as_u128();
                    Ok(EvalResult::Bv128(mask128(a | b, *width)))
                } else {
                    let a = lhs.try_eval(env)?.as_u64();
                    let b = rhs.try_eval(env)?.as_u64();
                    Ok(EvalResult::Bv(mask(a | b, *width)))
                }
            }
            SmtExpr::BvXor { lhs, rhs, width } => {
                if *width > 64 {
                    let a = lhs.try_eval(env)?.as_u128();
                    let b = rhs.try_eval(env)?.as_u128();
                    Ok(EvalResult::Bv128(mask128(a ^ b, *width)))
                } else {
                    let a = lhs.try_eval(env)?.as_u64();
                    let b = rhs.try_eval(env)?.as_u64();
                    Ok(EvalResult::Bv(mask(a ^ b, *width)))
                }
            }
            SmtExpr::BvShl { lhs, rhs, width } => {
                if *width > 64 {
                    let a = lhs.try_eval(env)?.as_u128();
                    let b = rhs.try_eval(env)?.as_u128();
                    if b >= *width as u128 {
                        Ok(EvalResult::Bv128(0))
                    } else {
                        Ok(EvalResult::Bv128(mask128(a << b, *width)))
                    }
                } else {
                    let a = lhs.try_eval(env)?.as_u64();
                    let b = rhs.try_eval(env)?.as_u64();
                    // SMT-LIB: if shift amount >= width, result is 0.
                    if b >= *width as u64 {
                        Ok(EvalResult::Bv(0))
                    } else {
                        Ok(EvalResult::Bv(mask(a << b, *width)))
                    }
                }
            }
            SmtExpr::BvLshr { lhs, rhs, width } => {
                if *width > 64 {
                    let a = lhs.try_eval(env)?.as_u128();
                    let b = rhs.try_eval(env)?.as_u128();
                    if b >= *width as u128 {
                        Ok(EvalResult::Bv128(0))
                    } else {
                        Ok(EvalResult::Bv128(mask128(a >> b, *width)))
                    }
                } else {
                    let a = lhs.try_eval(env)?.as_u64();
                    let b = rhs.try_eval(env)?.as_u64();
                    if b >= *width as u64 {
                        Ok(EvalResult::Bv(0))
                    } else {
                        Ok(EvalResult::Bv(mask(a >> b, *width)))
                    }
                }
            }
            SmtExpr::BvAshr { lhs, rhs, width } => {
                if *width > 64 {
                    let a = sign_extend128(lhs.try_eval(env)?.as_u128(), *width);
                    let b = rhs.try_eval(env)?.as_u128();
                    if b >= *width as u128 {
                        if a < 0 {
                            Ok(EvalResult::Bv128(mask128(u128::MAX, *width)))
                        } else {
                            Ok(EvalResult::Bv128(0))
                        }
                    } else {
                        Ok(EvalResult::Bv128(mask128((a >> b) as u128, *width)))
                    }
                } else {
                    let a = sign_extend(lhs.try_eval(env)?.as_u64(), *width);
                    let b = rhs.try_eval(env)?.as_u64();
                    if b >= *width as u64 {
                        // Sign-fill: all 1s if negative, all 0s if positive.
                        if a < 0 {
                            Ok(EvalResult::Bv(mask(u64::MAX, *width)))
                        } else {
                            Ok(EvalResult::Bv(0))
                        }
                    } else {
                        Ok(EvalResult::Bv(mask((a >> b) as u64, *width)))
                    }
                }
            }
            SmtExpr::BvNeg { operand, width } => {
                if *width > 64 {
                    let a = operand.try_eval(env)?.as_u128();
                    Ok(EvalResult::Bv128(mask128((!a).wrapping_add(1), *width)))
                } else {
                    let a = operand.try_eval(env)?.as_u64();
                    // Two's complement negation = wrapping negate.
                    Ok(EvalResult::Bv(mask((!a).wrapping_add(1), *width)))
                }
            }

            SmtExpr::Eq { lhs, rhs } => {
                let a = lhs.try_eval(env)?;
                let b = rhs.try_eval(env)?;
                Ok(EvalResult::Bool(a == b))
            }
            SmtExpr::Not { operand } => Ok(EvalResult::Bool(!operand.try_eval(env)?.as_bool())),
            SmtExpr::BvSlt { lhs, rhs, width } => {
                let a = sign_extend(lhs.try_eval(env)?.as_u64(), *width);
                let b = sign_extend(rhs.try_eval(env)?.as_u64(), *width);
                Ok(EvalResult::Bool(a < b))
            }
            SmtExpr::BvSge { lhs, rhs, width } => {
                let a = sign_extend(lhs.try_eval(env)?.as_u64(), *width);
                let b = sign_extend(rhs.try_eval(env)?.as_u64(), *width);
                Ok(EvalResult::Bool(a >= b))
            }
            SmtExpr::BvUge { lhs, rhs, .. } => {
                let a = lhs.try_eval(env)?.as_u64();
                let b = rhs.try_eval(env)?.as_u64();
                Ok(EvalResult::Bool(a >= b))
            }
            SmtExpr::BvSgt { lhs, rhs, width } => {
                let a = sign_extend(lhs.try_eval(env)?.as_u64(), *width);
                let b = sign_extend(rhs.try_eval(env)?.as_u64(), *width);
                Ok(EvalResult::Bool(a > b))
            }
            SmtExpr::BvSle { lhs, rhs, width } => {
                let a = sign_extend(lhs.try_eval(env)?.as_u64(), *width);
                let b = sign_extend(rhs.try_eval(env)?.as_u64(), *width);
                Ok(EvalResult::Bool(a <= b))
            }
            SmtExpr::BvUlt { lhs, rhs, .. } => {
                let a = lhs.try_eval(env)?.as_u64();
                let b = rhs.try_eval(env)?.as_u64();
                Ok(EvalResult::Bool(a < b))
            }
            SmtExpr::BvUgt { lhs, rhs, .. } => {
                let a = lhs.try_eval(env)?.as_u64();
                let b = rhs.try_eval(env)?.as_u64();
                Ok(EvalResult::Bool(a > b))
            }
            SmtExpr::BvUle { lhs, rhs, .. } => {
                let a = lhs.try_eval(env)?.as_u64();
                let b = rhs.try_eval(env)?.as_u64();
                Ok(EvalResult::Bool(a <= b))
            }
            SmtExpr::And { lhs, rhs } => Ok(EvalResult::Bool(
                lhs.try_eval(env)?.as_bool() && rhs.try_eval(env)?.as_bool(),
            )),
            SmtExpr::Or { lhs, rhs } => Ok(EvalResult::Bool(
                lhs.try_eval(env)?.as_bool() || rhs.try_eval(env)?.as_bool(),
            )),
            SmtExpr::Ite {
                cond,
                then_expr,
                else_expr,
            } => {
                if cond.try_eval(env)?.as_bool() {
                    then_expr.try_eval(env)
                } else {
                    else_expr.try_eval(env)
                }
            }
            SmtExpr::Extract {
                high,
                low,
                operand,
                width,
            } => {
                // Use u128 for extraction to handle wide intermediates (e.g., 128-bit NEON vectors).
                let v = operand.try_eval(env)?.as_u128();
                let extracted = (v >> low) & mask128(u128::MAX, *width);
                let _ = high; // used in width calculation
                // Result always fits in u64 since extract width <= 64 for valid NEON lanes.
                Ok(EvalResult::Bv(extracted as u64))
            }
            SmtExpr::Concat { hi, lo, width } => {
                let hi_val = hi.try_eval(env)?.as_u128();
                let lo_val = lo.try_eval(env)?.as_u128();
                let lo_width = lo.bv_width();
                // Place hi bits above lo bits using u128 to avoid overflow.
                let result = mask128((hi_val << lo_width) | lo_val, *width);
                if *width <= 64 {
                    Ok(EvalResult::Bv(result as u64))
                } else {
                    Ok(EvalResult::Bv128(result))
                }
            }
            SmtExpr::ZeroExtend { operand, width, .. } => {
                let v = operand.try_eval(env)?.as_u128();
                if *width > 64 {
                    Ok(EvalResult::Bv128(mask128(v, *width)))
                } else {
                    Ok(EvalResult::Bv(mask(v as u64, *width)))
                }
            }
            SmtExpr::SignExtend {
                operand,
                extra_bits,
                width,
            } => {
                let src_width = *width - *extra_bits;
                if *width > 64 {
                    let v = operand.try_eval(env)?.as_u128();
                    let extended = sign_extend128(v, src_width) as u128;
                    Ok(EvalResult::Bv128(mask128(extended, *width)))
                } else {
                    let v = operand.try_eval(env)?.as_u64();
                    let extended = sign_extend(v, src_width) as u64;
                    Ok(EvalResult::Bv(mask(extended, *width)))
                }
            }

            // -- Array evaluation --
            SmtExpr::ConstArray { value, .. } => {
                let v = value.try_eval(env)?;
                Ok(EvalResult::Array {
                    entries: HashMap::new(),
                    default: Box::new(v),
                })
            }
            SmtExpr::Select { array, index } => {
                let arr = array.try_eval(env)?;
                let idx = index.try_eval(env)?.as_u64();
                match arr {
                    EvalResult::Array { entries, default } => {
                        // Clone the EvalResult directly; `*v.clone()` would alloc a
                        // throwaway Box per select (hot: 100k samples x memory loads).
                        Ok(entries.get(&idx).map(|v| (**v).clone()).unwrap_or(*default))
                    }
                    _ => Err(SmtError::EvalError("select on non-array value".to_string())),
                }
            }
            SmtExpr::Store {
                array,
                index,
                value,
            } => {
                let arr = array.try_eval(env)?;
                let idx = index.try_eval(env)?.as_u64();
                let val = value.try_eval(env)?;
                match arr {
                    EvalResult::Array {
                        mut entries,
                        default,
                    } => {
                        entries.insert(idx, Box::new(val));
                        Ok(EvalResult::Array { entries, default })
                    }
                    _ => Err(SmtError::EvalError("store on non-array value".to_string())),
                }
            }

            // -- Memory load: a DETERMINISTIC function of the effective address --
            // value = extend(trunc(mix(addr), load_bits), result_width). `mix` is a
            // bijective avalanche hash of the FULL address, so the loaded value is a
            // deterministic function of the entire effective address: equal EAs give
            // equal values (Valid for a correct lowering), and a wrong EA / width /
            // signedness diverges for sampled inputs (REFUTE). See the `MemLoad`
            // variant docs.
            SmtExpr::MemLoad {
                addr,
                load_bits,
                signed,
                result_width,
            } => {
                let a = addr.try_eval(env)?.as_u64();
                let raw = mask(mem_load_mix(a), *load_bits);
                let value = if *signed {
                    // Sign-extend the load_bits-wide raw value to result_width.
                    mask(sign_extend(raw, *load_bits) as u64, *result_width)
                } else {
                    // Zero-extend (raw already masked to load_bits).
                    mask(raw, *result_width)
                };
                Ok(EvalResult::Bv(value))
            }

            // -- Floating-point evaluation (using Rust native f32/f64) --
            SmtExpr::FPConst { bits, eb, sb } => {
                let f = if *eb == 5 && *sb == 11 {
                    decode_fp16_const_bits(*bits)
                } else if *eb == 8 && *sb == 24 {
                    // FP32: interpret lower 32 bits as f32
                    f32::from_bits(*bits as u32) as f64
                } else {
                    // FP64 or other: interpret as f64
                    f64::from_bits(*bits)
                };
                Ok(EvalResult::Float(f))
            }
            SmtExpr::FPAdd { lhs, rhs, .. } => {
                let sort = lhs.sort();
                let a = lhs.try_eval(env)?.as_f64();
                let b = rhs.try_eval(env)?.as_f64();
                // GUARDED SWAP: integer-only bit-model on the EXACT f64 bits (no
                // host FPU) for binary64 (#89) and binary16 (#4b, via the lossless
                // f16<->f64 narrow/widen); native path for f32 (carrier lossy for
                // f32 bits — honest-deferred pending the raw-bits carrier).
                if bitmodel_handles(&sort) {
                    let bits =
                        crate::fp_bitmodel::fadd(crate::fp_bitmodel::F64, a.to_bits(), b.to_bits());
                    return Ok(EvalResult::Float(f64::from_bits(bits)));
                }
                if fp16_handles(&sort) {
                    let h = crate::fp_bitmodel::fadd(
                        crate::fp_bitmodel::F16,
                        fp16_bits_of(a),
                        fp16_bits_of(b),
                    );
                    return Ok(EvalResult::Float(fp16_to_carrier(h)));
                }
                if f32_handles(&sort) {
                    let s = crate::fp_bitmodel::fadd(
                        crate::fp_bitmodel::F32,
                        f32_bits_of(a),
                        f32_bits_of(b),
                    );
                    return Ok(EvalResult::Float(f32_to_carrier(s)));
                }
                Ok(EvalResult::Float(round_fp_result_if_fp16(a + b, &sort)))
            }
            SmtExpr::FPSub { lhs, rhs, .. } => {
                let sort = lhs.sort();
                let a = lhs.try_eval(env)?.as_f64();
                let b = rhs.try_eval(env)?.as_f64();
                if bitmodel_handles(&sort) {
                    let bits =
                        crate::fp_bitmodel::fsub(crate::fp_bitmodel::F64, a.to_bits(), b.to_bits());
                    return Ok(EvalResult::Float(f64::from_bits(bits)));
                }
                if fp16_handles(&sort) {
                    let h = crate::fp_bitmodel::fsub(
                        crate::fp_bitmodel::F16,
                        fp16_bits_of(a),
                        fp16_bits_of(b),
                    );
                    return Ok(EvalResult::Float(fp16_to_carrier(h)));
                }
                if f32_handles(&sort) {
                    let s = crate::fp_bitmodel::fsub(
                        crate::fp_bitmodel::F32,
                        f32_bits_of(a),
                        f32_bits_of(b),
                    );
                    return Ok(EvalResult::Float(f32_to_carrier(s)));
                }
                Ok(EvalResult::Float(round_fp_result_if_fp16(a - b, &sort)))
            }
            SmtExpr::FPMul { lhs, rhs, .. } => {
                let sort = lhs.sort();
                let a = lhs.try_eval(env)?.as_f64();
                let b = rhs.try_eval(env)?.as_f64();
                if bitmodel_handles(&sort) {
                    let bits =
                        crate::fp_bitmodel::fmul(crate::fp_bitmodel::F64, a.to_bits(), b.to_bits());
                    return Ok(EvalResult::Float(f64::from_bits(bits)));
                }
                if fp16_handles(&sort) {
                    let h = crate::fp_bitmodel::fmul(
                        crate::fp_bitmodel::F16,
                        fp16_bits_of(a),
                        fp16_bits_of(b),
                    );
                    return Ok(EvalResult::Float(fp16_to_carrier(h)));
                }
                if f32_handles(&sort) {
                    let s = crate::fp_bitmodel::fmul(
                        crate::fp_bitmodel::F32,
                        f32_bits_of(a),
                        f32_bits_of(b),
                    );
                    return Ok(EvalResult::Float(f32_to_carrier(s)));
                }
                Ok(EvalResult::Float(round_fp_result_if_fp16(a * b, &sort)))
            }
            SmtExpr::FPDiv { lhs, rhs, .. } => {
                let sort = lhs.sort();
                let a = lhs.try_eval(env)?.as_f64();
                let b = rhs.try_eval(env)?.as_f64();
                // GUARDED SWAP (#94): integer-only long-division bit-model (no host
                // FPU) on the EXACT f64 bits for binary64, and on the lossless
                // f16<->f64 narrow/widen for binary16 — host FPU EVICTED for div.
                // Native path remains only for binary32 (carrier lossy for f32 bits
                // — honest-deferred pending the raw-bits carrier).
                if bitmodel_handles(&sort) {
                    let bits =
                        crate::fp_bitmodel::fdiv(crate::fp_bitmodel::F64, a.to_bits(), b.to_bits());
                    return Ok(EvalResult::Float(f64::from_bits(bits)));
                }
                if fp16_handles(&sort) {
                    let h = crate::fp_bitmodel::fdiv(
                        crate::fp_bitmodel::F16,
                        fp16_bits_of(a),
                        fp16_bits_of(b),
                    );
                    return Ok(EvalResult::Float(fp16_to_carrier(h)));
                }
                if f32_handles(&sort) {
                    let s = crate::fp_bitmodel::fdiv(
                        crate::fp_bitmodel::F32,
                        f32_bits_of(a),
                        f32_bits_of(b),
                    );
                    return Ok(EvalResult::Float(f32_to_carrier(s)));
                }
                Ok(EvalResult::Float(round_fp_result_if_fp16(a / b, &sort)))
            }
            SmtExpr::FPNeg { operand } => {
                let sort = operand.sort();
                let a = operand.try_eval(env)?.as_f64();
                if bitmodel_handles(&sort) {
                    let bits = crate::fp_bitmodel::fneg(crate::fp_bitmodel::F64, a.to_bits());
                    return Ok(EvalResult::Float(f64::from_bits(bits)));
                }
                if fp16_handles(&sort) {
                    let h = crate::fp_bitmodel::fneg(crate::fp_bitmodel::F16, fp16_bits_of(a));
                    return Ok(EvalResult::Float(fp16_to_carrier(h)));
                }
                if f32_handles(&sort) {
                    let s = crate::fp_bitmodel::fneg(crate::fp_bitmodel::F32, f32_bits_of(a));
                    return Ok(EvalResult::Float(f32_to_carrier(s)));
                }
                Ok(EvalResult::Float(round_fp_result_if_fp16(-a, &sort)))
            }
            SmtExpr::FPEq { lhs, rhs } => {
                let a = lhs.try_eval(env)?.as_f64();
                let b = rhs.try_eval(env)?.as_f64();
                Ok(EvalResult::Bool(a == b))
            }
            SmtExpr::FPLt { lhs, rhs } => {
                let a = lhs.try_eval(env)?.as_f64();
                let b = rhs.try_eval(env)?.as_f64();
                Ok(EvalResult::Bool(a < b))
            }
            SmtExpr::FPGt { lhs, rhs } => {
                let a = lhs.try_eval(env)?.as_f64();
                let b = rhs.try_eval(env)?.as_f64();
                Ok(EvalResult::Bool(a > b))
            }
            SmtExpr::FPGe { lhs, rhs } => {
                let a = lhs.try_eval(env)?.as_f64();
                let b = rhs.try_eval(env)?.as_f64();
                Ok(EvalResult::Bool(a >= b))
            }
            SmtExpr::FPLe { lhs, rhs } => {
                let a = lhs.try_eval(env)?.as_f64();
                let b = rhs.try_eval(env)?.as_f64();
                Ok(EvalResult::Bool(a <= b))
            }
            SmtExpr::FPSqrt { operand, .. } => {
                let sort = operand.sort();
                let a = operand.try_eval(env)?.as_f64();
                // GUARDED SWAP (#94): integer-only digit-by-digit sqrt bit-model (no
                // host FPU) on the EXACT f64 bits for binary64, and on the lossless
                // f16<->f64 narrow/widen for binary16 — host FPU EVICTED for sqrt.
                // Native path remains only for binary32 (lossy carrier — deferred).
                if bitmodel_handles(&sort) {
                    let bits = crate::fp_bitmodel::fsqrt(crate::fp_bitmodel::F64, a.to_bits());
                    return Ok(EvalResult::Float(f64::from_bits(bits)));
                }
                if fp16_handles(&sort) {
                    let h = crate::fp_bitmodel::fsqrt(crate::fp_bitmodel::F16, fp16_bits_of(a));
                    return Ok(EvalResult::Float(fp16_to_carrier(h)));
                }
                if f32_handles(&sort) {
                    let s = crate::fp_bitmodel::fsqrt(crate::fp_bitmodel::F32, f32_bits_of(a));
                    return Ok(EvalResult::Float(f32_to_carrier(s)));
                }
                Ok(EvalResult::Float(round_fp_result_if_fp16(a.sqrt(), &sort)))
            }
            SmtExpr::FPRoundToIntegral { rm, operand } => {
                // Round the operand value to the nearest integral floating-point
                // value in the direction given by `rm`. IEEE roundToIntegral
                // preserves NaN payloads (we model NaN -> NaN), signed zeros and
                // infinities (floor/ceil/trunc/round on +-inf and +-0.0 are the
                // identity), exactly matching Rust's f64 floor/ceil/trunc/
                // round_ties_even and the x86 ROUNDSD/ROUNDSS modes. The integral
                // result is always exactly representable in the operand's format,
                // so no extra precision rounding is needed (fp16 handled below).
                let a = operand.try_eval(env)?.as_f64();
                let rounded = match rm {
                    RoundingMode::RTN => a.floor(),
                    RoundingMode::RTP => a.ceil(),
                    RoundingMode::RTZ => a.trunc(),
                    RoundingMode::RNE => a.round_ties_even(),
                    RoundingMode::RNA => a.round(),
                };
                Ok(EvalResult::Float(round_fp_result_if_fp16(
                    rounded,
                    &operand.sort(),
                )))
            }
            SmtExpr::FPAbs { operand } => {
                let sort = operand.sort();
                let a = operand.try_eval(env)?.as_f64();
                if bitmodel_handles(&sort) {
                    let bits = crate::fp_bitmodel::fabs(crate::fp_bitmodel::F64, a.to_bits());
                    return Ok(EvalResult::Float(f64::from_bits(bits)));
                }
                if fp16_handles(&sort) {
                    let h = crate::fp_bitmodel::fabs(crate::fp_bitmodel::F16, fp16_bits_of(a));
                    return Ok(EvalResult::Float(fp16_to_carrier(h)));
                }
                if f32_handles(&sort) {
                    let s = crate::fp_bitmodel::fabs(crate::fp_bitmodel::F32, f32_bits_of(a));
                    return Ok(EvalResult::Float(f32_to_carrier(s)));
                }
                Ok(EvalResult::Float(round_fp_result_if_fp16(a.abs(), &sort)))
            }
            SmtExpr::FPFma { a, b, c, .. } => {
                let sort = a.sort();
                let av = a.try_eval(env)?.as_f64();
                let bv = b.try_eval(env)?.as_f64();
                let cv = c.try_eval(env)?.as_f64();
                // GUARDED SWAP (scalar FMADD): the SINGLE-ROUNDING fused multiply-add
                // via the integer-only bit-model — `round_RNE(a*b + c)` with ONE
                // rounding (host FPU EVICTED from the FMA path), NOT the host
                // `mul_add`. Routed for binary64 (exact carrier bits), binary16 and
                // binary32 (via the lossless narrow/widen), exactly mirroring the
                // FADD/FSUB/FMUL/FDIV swaps above.
                if bitmodel_handles(&sort) {
                    let bits = crate::fp_bitmodel::fma(
                        crate::fp_bitmodel::F64,
                        av.to_bits(),
                        bv.to_bits(),
                        cv.to_bits(),
                    );
                    return Ok(EvalResult::Float(f64::from_bits(bits)));
                }
                if fp16_handles(&sort) {
                    let h = crate::fp_bitmodel::fma(
                        crate::fp_bitmodel::F16,
                        fp16_bits_of(av),
                        fp16_bits_of(bv),
                        fp16_bits_of(cv),
                    );
                    return Ok(EvalResult::Float(fp16_to_carrier(h)));
                }
                if f32_handles(&sort) {
                    let s = crate::fp_bitmodel::fma(
                        crate::fp_bitmodel::F32,
                        f32_bits_of(av),
                        f32_bits_of(bv),
                        f32_bits_of(cv),
                    );
                    return Ok(EvalResult::Float(f32_to_carrier(s)));
                }
                Ok(EvalResult::Float(round_fp_result_if_fp16(
                    av.mul_add(bv, cv),
                    &sort,
                )))
            }
            SmtExpr::FPIsNaN { operand } => {
                let a = operand.try_eval(env)?.as_f64();
                Ok(EvalResult::Bool(a.is_nan()))
            }
            SmtExpr::FPIsInf { operand } => {
                let a = operand.try_eval(env)?.as_f64();
                Ok(EvalResult::Bool(a.is_infinite()))
            }
            SmtExpr::FPIsZero { operand } => {
                let a = operand.try_eval(env)?.as_f64();
                Ok(EvalResult::Bool(a == 0.0))
            }
            SmtExpr::FPIsNormal { operand } => {
                let a = operand.try_eval(env)?.as_f64();
                Ok(EvalResult::Bool(a.is_normal()))
            }
            SmtExpr::FPToSBv {
                rm,
                operand,
                width,
                mode,
            } => {
                let op_sort = operand.sort();
                let a = operand.try_eval(env)?.as_f64();
                // x86 CVT[T]*2SI: INTEGER-INDEFINITE on NaN / +-Inf / out-of-
                // range (Intel SDM), NOT saturation. The EvalResult::Float(f64)
                // carrier holds the EXACT source value for a binary64 source AND
                // for a binary32 source (every finite f32 is exactly representable
                // in f64; NaN/+-Inf widen to NaN/+-Inf), so the integer-only F64
                // bit-model recovers the correct rounded value and the correct
                // out-of-range classification for BOTH widths — no host FPU.
                // (CVTT* = truncate toward zero / RTZ; CVT* = round-to-nearest-
                // even / RNE, the MXCSR default.)
                if matches!(mode, OutOfRangeMode::IntegerIndefinite)
                    && (*width == 32 || *width == 64)
                    && matches!(rm, RoundingMode::RTZ | RoundingMode::RNE)
                {
                    let v = if matches!(rm, RoundingMode::RNE) {
                        crate::fp_bitmodel::cvt_to_si(crate::fp_bitmodel::F64, *width, a.to_bits())
                    } else {
                        crate::fp_bitmodel::cvtt_to_si(crate::fp_bitmodel::F64, *width, a.to_bits())
                    };
                    return Ok(EvalResult::Bv(mask(v, *width)));
                }
                // GUARDED SWAP (#89): for a binary64 SOURCE the carrier holds the
                // exact bits; route FCVTZS (RTZ) / FCVTNS (RNE) at int width 32/64
                // through the integer-only bit-model. RTN/RTP/RNA modes keep the
                // native path (the AArch64 FCVTZS/NS the bit-model models are RTZ/RNE;
                // other rounding modes are honest-deferred). f32 source: native
                // (lossy carrier), honest-deferred.
                if bitmodel_handles(&op_sort)
                    && (*width == 32 || *width == 64)
                    && matches!(rm, RoundingMode::RTZ | RoundingMode::RNE)
                {
                    let nearest = matches!(rm, RoundingMode::RNE);
                    let v = if nearest {
                        crate::fp_bitmodel::fcvtns(crate::fp_bitmodel::F64, *width, a.to_bits())
                    } else {
                        crate::fp_bitmodel::fcvtzs(crate::fp_bitmodel::F64, *width, a.to_bits())
                    };
                    return Ok(EvalResult::Bv(mask(v, *width)));
                }
                // FAITHFUL FP->signed-int conversion (task: discharge the deferred
                // conversions). Two parts that the old `a as i64` model got wrong:
                //
                //   1. ROUNDING MODE. The float is first rounded to an integral
                //      value in the direction `rm` selects (RTZ = trunc toward zero,
                //      RNE = round-ties-even, RTN = floor, RTP = ceil, RNA = round-
                //      ties-away). The old model hard-coded RTZ, so an RNE-for-RTZ
                //      lowering bug (x86 CVTSD2SI mis-lowered as a truncating CVTT)
                //      could NOT refute. Now RNE and RTZ DIVERGE on a non-integral
                //      tie input (e.g. 1.5 -> RTZ 1, RNE 2) ⇒ REFUTE.
                //   2. SATURATION + NaN. After rounding, the integral value is
                //      CLAMPED to the signed `width`-bit range and NaN maps to 0 —
                //      the DEFINED out-of-range behaviour of wasm `trunc_sat`,
                //      AArch64 FCVTZS and the Rust `as` cast. (Rust's float-to-int
                //      `as` already saturates+NaN->0 at the target width, so the
                //      width-typed cast below realises both clamps faithfully.)
                let rounded = round_fp_by_mode(a, *rm);
                let v: u64 = match *width {
                    8 => (rounded as i8) as u64 & 0xff,
                    16 => (rounded as i16) as u64 & 0xffff,
                    32 => (rounded as i32) as u32 as u64,
                    _ => (rounded as i64) as u64,
                };
                Ok(EvalResult::Bv(mask(v, *width)))
            }
            SmtExpr::FPToUBv { rm, operand, width } => {
                let op_sort = operand.sort();
                let a = operand.try_eval(env)?.as_f64();
                // GUARDED SWAP (#89): binary64 source, int width 32/64, RTZ (FCVTZU)
                // or RNE (FCVTNU) -> integer-only bit-model. Others honest-deferred.
                if bitmodel_handles(&op_sort)
                    && (*width == 32 || *width == 64)
                    && matches!(rm, RoundingMode::RTZ | RoundingMode::RNE)
                {
                    let nearest = matches!(rm, RoundingMode::RNE);
                    let v = if nearest {
                        crate::fp_bitmodel::fcvtnu(crate::fp_bitmodel::F64, *width, a.to_bits())
                    } else {
                        crate::fp_bitmodel::fcvtzu(crate::fp_bitmodel::F64, *width, a.to_bits())
                    };
                    return Ok(EvalResult::Bv(mask(v, *width)));
                }
                // FAITHFUL FP->unsigned-int conversion: round per `rm`, then SATURATE
                // to the unsigned `width`-bit range with NaN/negative -> 0 (the wasm
                // `trunc_sat..._u`, AArch64 FCVTZU and Rust `as` semantics). Rust's
                // float-to-unsigned `as` cast already clamps to [0, MAX] at the
                // target width and maps NaN/negatives to 0.
                let rounded = round_fp_by_mode(a, *rm);
                let v: u64 = match *width {
                    8 => (rounded as u8) as u64,
                    16 => (rounded as u16) as u64,
                    32 => (rounded as u32) as u64,
                    _ => rounded as u64,
                };
                Ok(EvalResult::Bv(mask(v, *width)))
            }
            SmtExpr::BvToFP {
                operand, eb, sb, ..
            } => {
                // INT->FP convert. `BvToFP` interprets its operand as a SIGNED
                // bitvector of `operand.bv_width()` bits — this IS the signed
                // conversion (x86 CVTSI2SD/SS, AArch64 SCVTF). UNSIGNED conversions
                // (wasm `f*.convert_i*_u`, AArch64 UCVTF) are encoded by FIRST
                // zero-extending the operand by one bit-width and feeding THAT wider,
                // sign-bit-clear bitvector here — so the same signed interpretation
                // yields the correct non-negative magnitude. A signed-for-unsigned
                // lowering bug therefore feeds a DIFFERENT operand (the un-extended,
                // sign-bit-set value) ⇒ a different f64 magnitude ⇒ REFUTE.
                //
                // Operate in i128 so a zero-extended-to-128 unsigned i64 source
                // keeps its full magnitude (truncating to u64 first would corrupt
                // the high half). `as f64`/`as f32` round to nearest, matching the
                // RNE default of these converts (and the precision loss of the
                // i64->f32/f64 cases that cannot be represented exactly).
                let src_width = operand.bv_width();
                let signed: i128 = match operand.try_eval(env)? {
                    EvalResult::Bv128(w) => sign_extend128(w, src_width),
                    other => sign_extend(other.as_u64(), src_width) as i128,
                };
                let f = if *eb == 5 && *sb == 11 {
                    round_to_fp16_value(signed as f64)
                } else if *eb == 8 && *sb == 24 {
                    (signed as f32) as f64
                } else {
                    signed as f64
                };
                Ok(EvalResult::Float(f))
            }
            SmtExpr::FPToFP {
                operand, eb, sb, ..
            } => {
                let f = operand.try_eval(env)?.as_f64();
                // Convert between FP formats via Rust f32/f64.
                let result = if *eb == 5 && *sb == 11 {
                    round_to_fp16_value(f)
                } else if *eb == 8 && *sb == 24 {
                    (f as f32) as f64
                } else {
                    f
                };
                Ok(EvalResult::Float(result))
            }

            SmtExpr::BvBitsToFP { operand, eb, sb } => {
                // Raw IEEE bit REINTERPRET (no rounding, no numeric convert).
                // The f64 evaluation carrier holds binary32/binary16 values
                // exactly (every f32/f16 widens losslessly); NaN payloads are
                // canonicalized by the carrier, which the FP comparison rules
                // (NaN == NaN) already absorb.
                let bits = match operand.try_eval(env)? {
                    EvalResult::Bv128(w) => w as u64,
                    other => other.as_u64(),
                };
                let f = if *eb == 11 && *sb == 53 {
                    f64::from_bits(bits)
                } else if *eb == 8 && *sb == 24 {
                    f32::from_bits(bits as u32) as f64
                } else if *eb == 5 && *sb == 11 {
                    f64::from_bits(crate::fp_bitmodel::fcvt_h_to_d(bits as u16 as u64))
                } else {
                    return Err(SmtError::UnsupportedType(format!(
                        "BvBitsToFP: unsupported format ({eb}, {sb})"
                    )));
                };
                Ok(EvalResult::Float(f))
            }

            // -- Uninterpreted functions --
            // UF evaluation is not meaningful in concrete evaluation (they are
            // uninterpreted). Return an error for now; real verification uses
            // the SMT solver for UF reasoning.
            SmtExpr::UF { name, .. } => Err(SmtError::EvalError(format!(
                "cannot concretely evaluate uninterpreted function '{}'",
                name
            ))),
            SmtExpr::UFDecl { name, .. } => Err(SmtError::EvalError(format!(
                "cannot evaluate UF declaration '{}'",
                name
            ))),

            // -- Bounded quantifier evaluation (loop unrolling) --
            SmtExpr::ForAll {
                var,
                var_width,
                lower,
                upper,
                body,
            } => {
                let lo = lower.try_eval(env)?.as_u64();
                let hi = upper.try_eval(env)?.as_u64();
                if hi <= lo {
                    // Empty range: vacuously true.
                    return Ok(EvalResult::Bool(true));
                }
                let count = hi - lo;
                if count > 256 {
                    return Err(SmtError::EvalError(format!(
                        "forall range too large for unrolling: {} (max 256)",
                        count
                    )));
                }
                let mut local_env = env.clone();
                for i in lo..hi {
                    local_env.set_var(var.clone(), mask(i, *var_width));
                    let result = body.try_eval(&local_env)?;
                    if !result.as_bool() {
                        return Ok(EvalResult::Bool(false));
                    }
                }
                Ok(EvalResult::Bool(true))
            }

            SmtExpr::Exists {
                var,
                var_width,
                lower,
                upper,
                body,
            } => {
                let lo = lower.try_eval(env)?.as_u64();
                let hi = upper.try_eval(env)?.as_u64();
                if hi <= lo {
                    // Empty range: vacuously false.
                    return Ok(EvalResult::Bool(false));
                }
                let count = hi - lo;
                if count > 256 {
                    return Err(SmtError::EvalError(format!(
                        "exists range too large for unrolling: {} (max 256)",
                        count
                    )));
                }
                let mut local_env = env.clone();
                for i in lo..hi {
                    local_env.set_var(var.clone(), mask(i, *var_width));
                    let result = body.try_eval(&local_env)?;
                    if result.as_bool() {
                        return Ok(EvalResult::Bool(true));
                    }
                }
                Ok(EvalResult::Bool(false))
            }
        }
    }

    /// Evaluate this expression under the given variable assignment.
    ///
    /// Variables map name -> u64 value (already masked to width).
    ///
    /// # Panics
    ///
    /// Panics if a variable is not found in the environment. Use [`try_eval`]
    /// for fallible evaluation.
    pub fn eval<E: EnvOps>(&self, env: &E) -> EvalResult {
        self.try_eval(env)
            .expect("SmtExpr::eval failed; use try_eval() for fallible evaluation")
    }

    /// Serialize this expression to an SMT-LIB2 expression string.
    ///
    /// This is a convenience method that delegates to the [`Display`] implementation,
    /// which produces valid SMT-LIB2 syntax for each expression variant.
    ///
    /// # Example
    ///
    /// ```
    /// use trust_cg_verify::SmtExpr;
    /// let a = SmtExpr::var("a", 32);
    /// let b = SmtExpr::var("b", 32);
    /// let expr = a.bvadd(b);
    /// assert_eq!(expr.to_smt2_expr(), "(bvadd a b)");
    /// ```
    pub fn to_smt2_expr(&self) -> String {
        format!("{}", self)
    }
}

// ---------------------------------------------------------------------------
// Display (SMT-LIB2 format for debugging)
// ---------------------------------------------------------------------------

impl fmt::Display for SmtExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SmtExpr::Var { name, .. } => write!(f, "{}", name),
            SmtExpr::BvConst { value, width } => {
                write!(f, "(_ bv{} {})", value, width)
            }
            SmtExpr::BoolConst(b) => write!(f, "{}", b),
            SmtExpr::BvAdd { lhs, rhs, .. } => write!(f, "(bvadd {} {})", lhs, rhs),
            SmtExpr::BvSub { lhs, rhs, .. } => write!(f, "(bvsub {} {})", lhs, rhs),
            SmtExpr::BvMul { lhs, rhs, .. } => write!(f, "(bvmul {} {})", lhs, rhs),
            SmtExpr::BvSDiv { lhs, rhs, .. } => write!(f, "(bvsdiv {} {})", lhs, rhs),
            SmtExpr::BvUDiv { lhs, rhs, .. } => write!(f, "(bvudiv {} {})", lhs, rhs),
            SmtExpr::BvURem { lhs, rhs, .. } => write!(f, "(bvurem {} {})", lhs, rhs),
            // The trap point is modeled in SMT-LIB as a fresh, UNCONSTRAINED poison
            // constant (declared by the serializer / introduced as a fresh ay term
            // by `translate_expr_to_ay`), so the solver treats the value at
            // `guard == 0` as arbitrary and cannot prove equality without the
            // divisor!=0 precondition. The Display form names that constant so the
            // declaration and the use agree. See `SmtExpr::TrapIfZero`.
            SmtExpr::TrapIfZero {
                guard,
                value,
                width,
            } => write!(
                f,
                "(ite (= {} (_ bv0 {})) {} {})",
                guard,
                guard.try_bv_width().unwrap_or(*width),
                trap_poison_const_name(guard, value, *width),
                value
            ),
            SmtExpr::BvAnd { lhs, rhs, .. } => write!(f, "(bvand {} {})", lhs, rhs),
            SmtExpr::BvOr { lhs, rhs, .. } => write!(f, "(bvor {} {})", lhs, rhs),
            SmtExpr::BvXor { lhs, rhs, .. } => write!(f, "(bvxor {} {})", lhs, rhs),
            SmtExpr::BvShl { lhs, rhs, .. } => write!(f, "(bvshl {} {})", lhs, rhs),
            SmtExpr::BvLshr { lhs, rhs, .. } => write!(f, "(bvlshr {} {})", lhs, rhs),
            SmtExpr::BvAshr { lhs, rhs, .. } => write!(f, "(bvashr {} {})", lhs, rhs),
            SmtExpr::BvNeg { operand, .. } => write!(f, "(bvneg {})", operand),
            SmtExpr::Eq { lhs, rhs } => write!(f, "(= {} {})", lhs, rhs),
            SmtExpr::Not { operand } => write!(f, "(not {})", operand),
            SmtExpr::BvSlt { lhs, rhs, .. } => write!(f, "(bvslt {} {})", lhs, rhs),
            SmtExpr::BvSge { lhs, rhs, .. } => write!(f, "(bvsge {} {})", lhs, rhs),
            SmtExpr::BvSgt { lhs, rhs, .. } => write!(f, "(bvsgt {} {})", lhs, rhs),
            SmtExpr::BvSle { lhs, rhs, .. } => write!(f, "(bvsle {} {})", lhs, rhs),
            SmtExpr::BvUlt { lhs, rhs, .. } => write!(f, "(bvult {} {})", lhs, rhs),
            SmtExpr::BvUge { lhs, rhs, .. } => write!(f, "(bvuge {} {})", lhs, rhs),
            SmtExpr::BvUgt { lhs, rhs, .. } => write!(f, "(bvugt {} {})", lhs, rhs),
            SmtExpr::BvUle { lhs, rhs, .. } => write!(f, "(bvule {} {})", lhs, rhs),
            SmtExpr::And { lhs, rhs } => write!(f, "(and {} {})", lhs, rhs),
            SmtExpr::Or { lhs, rhs } => write!(f, "(or {} {})", lhs, rhs),
            SmtExpr::Ite {
                cond,
                then_expr,
                else_expr,
            } => {
                write!(f, "(ite {} {} {})", cond, then_expr, else_expr)
            }
            SmtExpr::Extract {
                high, low, operand, ..
            } => {
                write!(f, "((_ extract {} {}) {})", high, low, operand)
            }
            SmtExpr::Concat { hi, lo, .. } => {
                write!(f, "(concat {} {})", hi, lo)
            }
            SmtExpr::ZeroExtend {
                operand,
                extra_bits,
                ..
            } => {
                write!(f, "((_ zero_extend {}) {})", extra_bits, operand)
            }
            SmtExpr::SignExtend {
                operand,
                extra_bits,
                ..
            } => {
                write!(f, "((_ sign_extend {}) {})", extra_bits, operand)
            }
            // Array operations
            SmtExpr::Select { array, index } => {
                write!(f, "(select {} {})", array, index)
            }
            SmtExpr::Store {
                array,
                index,
                value,
            } => {
                write!(f, "(store {} {} {})", array, index, value)
            }
            SmtExpr::ConstArray { index_sort, value } => {
                // SMT-LIB2: ((as const (Array idx_sort elem_sort)) value)
                let elem_sort = value.sort();
                let array_sort = SmtSort::Array(Box::new(index_sort.clone()), Box::new(elem_sort));
                write!(f, "((as const {}) {})", array_sort, value)
            }
            // Memory load as an uninterpreted function of the address. A distinct
            // UF symbol per (load width, signedness) gives the same congruence the
            // evaluator's deterministic `mix` does: `mem_load_W_s(ea1) ==
            // mem_load_W_s(ea2)` is implied by `ea1 == ea2`, and is the ONLY thing
            // the solver may assume, so a wrong EA/width/sign is never spuriously
            // equal. The UF returns a `load_bits`-wide value; the surrounding
            // sign/zero-extend to `result_width` is emitted explicitly.
            SmtExpr::MemLoad {
                addr,
                load_bits,
                signed,
                result_width,
            } => {
                let s = if *signed { "s" } else { "u" };
                let uf = format!("(mem_load_{load_bits}_{s} {addr})");
                let extra = result_width - load_bits;
                if extra == 0 {
                    write!(f, "{uf}")
                } else if *signed {
                    write!(f, "((_ sign_extend {extra}) {uf})")
                } else {
                    write!(f, "((_ zero_extend {extra}) {uf})")
                }
            }
            // Floating-point operations
            SmtExpr::FPConst { bits, eb, sb } => {
                // Emit as fp literal with bitvector decomposition
                let total = eb + sb;
                let sign = if bits >> (total - 1) & 1 == 1 {
                    "1"
                } else {
                    "0"
                };
                let exp = format!(
                    "{:0>width$b}",
                    (bits >> (sb - 1)) & ((1u64 << eb) - 1),
                    width = *eb as usize
                );
                let sig = format!(
                    "{:0>width$b}",
                    bits & ((1u64 << (sb - 1)) - 1),
                    width = (*sb - 1) as usize
                );
                write!(f, "(fp #b{} #b{} #b{})", sign, exp, sig)
            }
            SmtExpr::FPAdd { rm, lhs, rhs } => {
                write!(f, "(fp.add {} {} {})", rm, lhs, rhs)
            }
            SmtExpr::FPSub { rm, lhs, rhs } => {
                write!(f, "(fp.sub {} {} {})", rm, lhs, rhs)
            }
            SmtExpr::FPMul { rm, lhs, rhs } => {
                write!(f, "(fp.mul {} {} {})", rm, lhs, rhs)
            }
            SmtExpr::FPDiv { rm, lhs, rhs } => {
                write!(f, "(fp.div {} {} {})", rm, lhs, rhs)
            }
            SmtExpr::FPNeg { operand } => {
                write!(f, "(fp.neg {})", operand)
            }
            SmtExpr::FPEq { lhs, rhs } => {
                write!(f, "(fp.eq {} {})", lhs, rhs)
            }
            SmtExpr::FPLt { lhs, rhs } => {
                write!(f, "(fp.lt {} {})", lhs, rhs)
            }
            SmtExpr::FPGt { lhs, rhs } => {
                write!(f, "(fp.gt {} {})", lhs, rhs)
            }
            SmtExpr::FPGe { lhs, rhs } => {
                write!(f, "(fp.geq {} {})", lhs, rhs)
            }
            SmtExpr::FPLe { lhs, rhs } => {
                write!(f, "(fp.leq {} {})", lhs, rhs)
            }
            SmtExpr::FPSqrt { rm, operand } => {
                write!(f, "(fp.sqrt {} {})", rm, operand)
            }
            SmtExpr::FPRoundToIntegral { rm, operand } => {
                write!(f, "(fp.roundToIntegral {} {})", rm, operand)
            }
            SmtExpr::FPAbs { operand } => {
                write!(f, "(fp.abs {})", operand)
            }
            SmtExpr::FPFma { rm, a, b, c } => {
                write!(f, "(fp.fma {} {} {} {})", rm, a, b, c)
            }
            SmtExpr::FPIsNaN { operand } => {
                write!(f, "(fp.isNaN {})", operand)
            }
            SmtExpr::FPIsInf { operand } => {
                write!(f, "(fp.isInfinite {})", operand)
            }
            SmtExpr::FPIsZero { operand } => {
                write!(f, "(fp.isZero {})", operand)
            }
            SmtExpr::FPIsNormal { operand } => {
                write!(f, "(fp.isNormal {})", operand)
            }
            SmtExpr::FPToSBv {
                rm, operand, width, ..
            } => {
                // The out-of-range `mode` is a concrete-eval concept; SMT-LIB
                // `fp.to_sbv` leaves out-of-range unspecified, so it is not
                // emitted into the query (the solver path is mode-agnostic).
                write!(f, "((_ fp.to_sbv {}) {} {})", width, rm, operand)
            }
            SmtExpr::FPToUBv { rm, operand, width } => {
                write!(f, "((_ fp.to_ubv {}) {} {})", width, rm, operand)
            }
            SmtExpr::BvToFP {
                rm,
                operand,
                eb,
                sb,
            } => {
                write!(f, "((_ to_fp {} {}) {} {})", eb, sb, rm, operand)
            }
            SmtExpr::FPToFP {
                rm,
                operand,
                eb,
                sb,
            } => {
                write!(f, "((_ to_fp {} {}) {} {})", eb, sb, rm, operand)
            }
            SmtExpr::BvBitsToFP { operand, eb, sb } => {
                // Single-argument to_fp: the IEEE bit-reinterpret form.
                write!(f, "((_ to_fp {} {}) {})", eb, sb, operand)
            }
            // Uninterpreted functions
            SmtExpr::UF { name, args, .. } => {
                if args.is_empty() {
                    write!(f, "{}", name)
                } else {
                    write!(f, "({}", name)?;
                    for arg in args {
                        write!(f, " {}", arg)?;
                    }
                    write!(f, ")")
                }
            }
            SmtExpr::UFDecl {
                name,
                arg_sorts,
                ret_sort,
            } => {
                write!(f, "(declare-fun {} (", name)?;
                for (i, sort) in arg_sorts.iter().enumerate() {
                    if i > 0 {
                        write!(f, " ")?;
                    }
                    write!(f, "{}", sort)?;
                }
                write!(f, ") {})", ret_sort)
            }
            // Bounded quantifiers: emit SMT-LIB2 with range predicate as guard.
            // ForAll: (forall ((var (_ BitVec w))) (=> (and (bvuge var lo) (bvult var hi)) body))
            SmtExpr::ForAll {
                var,
                var_width,
                lower,
                upper,
                body,
            } => {
                write!(
                    f,
                    "(forall (({} (_ BitVec {}))) (=> (and (bvuge {} {}) (bvult {} {})) {}))",
                    var, var_width, var, lower, var, upper, body
                )
            }
            // Exists: (exists ((var (_ BitVec w))) (and (bvuge var lo) (bvult var hi) body))
            SmtExpr::Exists {
                var,
                var_width,
                lower,
                upper,
                body,
            } => {
                write!(
                    f,
                    "(exists (({} (_ BitVec {}))) (and (bvuge {} {}) (bvult {} {}) {}))",
                    var, var_width, var, lower, var, upper, body
                )
            }
        }
    }
}

impl fmt::Display for RoundingMode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RoundingMode::RNE => write!(f, "RNE"),
            RoundingMode::RNA => write!(f, "RNA"),
            RoundingMode::RTP => write!(f, "RTP"),
            RoundingMode::RTN => write!(f, "RTN"),
            RoundingMode::RTZ => write!(f, "RTZ"),
        }
    }
}

impl fmt::Display for SmtSort {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SmtSort::BitVec(w) => write!(f, "(_ BitVec {})", w),
            SmtSort::Bool => write!(f, "Bool"),
            SmtSort::Array(idx, elem) => write!(f, "(Array {} {})", idx, elem),
            SmtSort::FloatingPoint(eb, sb) => write!(f, "(_ FloatingPoint {} {})", eb, sb),
        }
    }
}

// ---------------------------------------------------------------------------
// NEON / SIMD lane helpers
// ---------------------------------------------------------------------------

/// NEON vector arrangement: describes element size and lane count.
///
/// ARM DDI 0487: "The arrangement specifier determines the size of elements
/// and the number of lanes in the vector register."
///
/// Naming convention follows ARM assembly syntax:
/// - `8B` = 8 lanes of 8-bit bytes (64-bit, lower half of V register)
/// - `16B` = 16 lanes of 8-bit bytes (128-bit, full V register)
/// - `4H` = 4 lanes of 16-bit halfwords (64-bit)
/// - `8H` = 8 lanes of 16-bit halfwords (128-bit)
/// - `2S` = 2 lanes of 32-bit words (64-bit)
/// - `4S` = 4 lanes of 32-bit words (128-bit)
/// - `2D` = 2 lanes of 64-bit doublewords (128-bit)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum VectorArrangement {
    B8,  // 8 x 8-bit (64-bit total)
    B16, // 16 x 8-bit (128-bit total)
    H4,  // 4 x 16-bit (64-bit total)
    H8,  // 8 x 16-bit (128-bit total)
    S2,  // 2 x 32-bit (64-bit total)
    S4,  // 4 x 32-bit (128-bit total)
    D2,  // 2 x 64-bit (128-bit total)
}

impl VectorArrangement {
    /// Number of lanes in this arrangement.
    pub fn lane_count(self) -> u32 {
        match self {
            VectorArrangement::B8 => 8,
            VectorArrangement::B16 => 16,
            VectorArrangement::H4 => 4,
            VectorArrangement::H8 => 8,
            VectorArrangement::S2 => 2,
            VectorArrangement::S4 => 4,
            VectorArrangement::D2 => 2,
        }
    }

    /// Bit-width of each lane element.
    pub fn lane_bits(self) -> u32 {
        match self {
            VectorArrangement::B8 | VectorArrangement::B16 => 8,
            VectorArrangement::H4 | VectorArrangement::H8 => 16,
            VectorArrangement::S2 | VectorArrangement::S4 => 32,
            VectorArrangement::D2 => 64,
        }
    }

    /// Total bit-width of the vector (64 or 128).
    pub fn total_bits(self) -> u32 {
        self.lane_count() * self.lane_bits()
    }
}

/// Split a 128-bit (or 64-bit) vector `expr` into its lanes at the given lane
/// `width`, least-significant lane first (`lanes[0]` is `expr[width-1:0]`).
///
/// This is the named Bv128 lane-SPLIT primitive used by the lane-wise packed/SIMD
/// reconstruction (x86 `encode_paddd` & friends, wasm `i32x4.*`): the inverse of
/// [`lane_concat`]. `expr.bv_width()` must be a positive multiple of `width`.
///
/// # Panics
///
/// Panics if `width == 0` or `expr.bv_width()` is not a positive multiple of `width`.
pub fn lane_split(expr: &SmtExpr, width: u32) -> Vec<SmtExpr> {
    assert!(width > 0, "lane_split: lane width must be positive");
    let total = expr.bv_width();
    assert!(
        total.is_multiple_of(width) && total >= width,
        "lane_split: total width {total} is not a positive multiple of lane width {width}"
    );
    let n = total / width;
    (0..n)
        .map(|i| {
            let lo = i * width;
            let hi = lo + width - 1;
            expr.clone().extract(hi, lo)
        })
        .collect()
}

/// Concatenate per-lane expressions back into a single vector, least-significant
/// lane first (`lanes[0]` occupies the low bits). The named Bv128 lane-CONCAT
/// primitive — the inverse of [`lane_split`]. Each lane may be any width; the
/// result width is their sum.
///
/// # Panics
///
/// Panics if `lanes` is empty.
pub fn lane_concat(lanes: &[SmtExpr]) -> SmtExpr {
    assert!(!lanes.is_empty(), "lane_concat: need at least one lane");
    let mut result = lanes[0].clone();
    for lane in &lanes[1..] {
        result = lane.clone().concat(result);
    }
    result
}

/// Extract lane `idx` from a vector expression.
///
/// Returns `expr[hi:lo]` where `lo = idx * lane_bits` and `hi = lo + lane_bits - 1`.
///
/// # Panics
///
/// Panics if `idx >= arrangement.lane_count()`.
pub fn lane_extract(expr: &SmtExpr, arrangement: VectorArrangement, idx: u32) -> SmtExpr {
    assert!(idx < arrangement.lane_count(), "lane index out of bounds");
    let lane_bits = arrangement.lane_bits();
    let lo = idx * lane_bits;
    let hi = lo + lane_bits - 1;
    expr.clone().extract(hi, lo)
}

/// Build a vector from individual lane expressions by concatenating them.
///
/// `lanes[0]` is the least-significant lane (lane 0), `lanes[last]` is the
/// most-significant lane. Each lane expression must have width `arrangement.lane_bits()`.
///
/// # Panics
///
/// Panics if `lanes.len() != arrangement.lane_count()`.
pub fn concat_lanes(lanes: &[SmtExpr], arrangement: VectorArrangement) -> SmtExpr {
    assert_eq!(
        lanes.len() as u32,
        arrangement.lane_count(),
        "wrong number of lanes for arrangement"
    );
    // Build from lane 0 (LSB) upward: concat(lane[n-1], concat(lane[n-2], ... concat(lane[1], lane[0])))
    let mut result = lanes[0].clone();
    for lane in &lanes[1..] {
        // Each `concat` places the new lane in the higher bits.
        result = lane.clone().concat(result);
    }
    result
}

/// Insert a lane value into a vector, returning the modified vector.
///
/// Decomposes the vector into lanes, replaces lane `idx` with `new_lane`,
/// and reassembles. This is the symbolic equivalent of `INS Vd.T[idx], Vn.T[0]`.
///
/// # Panics
///
/// Panics if `idx >= arrangement.lane_count()`.
pub fn lane_insert(
    vec: &SmtExpr,
    arrangement: VectorArrangement,
    idx: u32,
    new_lane: SmtExpr,
) -> SmtExpr {
    assert!(idx < arrangement.lane_count(), "lane index out of bounds");
    let n = arrangement.lane_count();
    let lanes: Vec<SmtExpr> = (0..n)
        .map(|i| {
            if i == idx {
                new_lane.clone()
            } else {
                lane_extract(vec, arrangement, i)
            }
        })
        .collect();
    concat_lanes(&lanes, arrangement)
}

/// Apply a binary operation lane-wise to two vector expressions.
///
/// For each lane `i`, extracts the lane from both operands, applies `op`, and
/// reassembles the result. This is the core pattern for NEON integer SIMD ops.
pub fn map_lanes_binary<F>(
    lhs: &SmtExpr,
    rhs: &SmtExpr,
    arrangement: VectorArrangement,
    op: F,
) -> SmtExpr
where
    F: Fn(SmtExpr, SmtExpr) -> SmtExpr,
{
    let n = arrangement.lane_count();
    let lanes: Vec<SmtExpr> = (0..n)
        .map(|i| {
            let a = lane_extract(lhs, arrangement, i);
            let b = lane_extract(rhs, arrangement, i);
            op(a, b)
        })
        .collect();
    concat_lanes(&lanes, arrangement)
}

/// Apply a unary operation lane-wise to a vector expression.
pub fn map_lanes_unary<F>(operand: &SmtExpr, arrangement: VectorArrangement, op: F) -> SmtExpr
where
    F: Fn(SmtExpr) -> SmtExpr,
{
    let n = arrangement.lane_count();
    let lanes: Vec<SmtExpr> = (0..n)
        .map(|i| {
            let a = lane_extract(operand, arrangement, i);
            op(a)
        })
        .collect();
    concat_lanes(&lanes, arrangement)
}

/// Apply a binary operation where the second operand is a constant (e.g., shift immediate).
pub fn map_lanes_binary_imm<F>(
    lhs: &SmtExpr,
    imm: u64,
    arrangement: VectorArrangement,
    op: F,
) -> SmtExpr
where
    F: Fn(SmtExpr, SmtExpr) -> SmtExpr,
{
    let lane_bits = arrangement.lane_bits();
    let n = arrangement.lane_count();
    let lanes: Vec<SmtExpr> = (0..n)
        .map(|i| {
            let a = lane_extract(lhs, arrangement, i);
            let b = SmtExpr::bv_const(imm, lane_bits);
            op(a, b)
        })
        .collect();
    concat_lanes(&lanes, arrangement)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    /// The memory property this representation exists for: `SmtExpr` children
    /// are `Arc`, so cloning an expression SHARES its subterms instead of
    /// deep-copying them.
    ///
    /// Why it matters, measured (2026-08-06): the proof encoders build memory
    /// terms by cloning — `encode_load_le` clones the memory expression once
    /// per byte, over a memory already built from N nested stores. With `Box`
    /// children every clone was a deep copy, so the 8-byte CMPXCHG obligation
    /// expanded 1721 -> 256366 -> 2052926 bytes of tree, and the x86 proof
    /// database cost 59.3 MB. With sharing the SAME logical tree (rendering is
    /// byte-identical, so every SMT2 query is unchanged) costs 4.7 MB, and the
    /// bridge's compile memory went 2.02x -> 1.27x of LLVM.
    ///
    /// If someone changes these children back to `Box`, or introduces a deep
    /// clone, this test fails rather than the regression showing up only as
    /// mysterious compile-memory growth.
    #[test]
    fn clone_shares_subterms_rather_than_deep_copying() {
        let leaf = SmtExpr::var("x", 64);
        let inner = Arc::new(SmtExpr::BvAdd {
            lhs: Arc::new(leaf.clone()),
            rhs: Arc::new(leaf),
            width: 64,
        });
        // Reusing ONE `Arc` for both operands is exactly what the proof
        // encoders do when they clone a memory term per byte.
        let original = SmtExpr::BvMul {
            lhs: Arc::clone(&inner),
            rhs: inner,
            width: 64,
        };
        let copy = original.clone();

        let (SmtExpr::BvMul { lhs: a, rhs: b, .. }, SmtExpr::BvMul { lhs: c, .. }) =
            (&original, &copy)
        else {
            panic!("constructed a BvMul; pattern must match");
        };
        assert!(
            Arc::ptr_eq(a, c),
            "cloning an SmtExpr must SHARE children, not deep-copy them"
        );
        // And reusing one `Arc` for both operands stores ONE allocation, not
        // two copies — this is what collapses the quadratic memory-term blowup.
        assert!(
            Arc::ptr_eq(a, b),
            "reusing one Arc for both operands must store a single allocation"
        );
        // Sharing must not change the VALUE: equality is structural.
        assert_eq!(original, copy);
    }

    use super::*;

    fn env(pairs: &[(&str, u64)]) -> HashMap<String, u64> {
        pairs.iter().map(|(k, v)| (k.to_string(), *v)).collect()
    }

    #[test]
    fn test_bvadd_wrapping() {
        let a = SmtExpr::var("a", 32);
        let b = SmtExpr::var("b", 32);
        let expr = a.bvadd(b);
        // 0xFFFFFFFF + 1 = 0 (wrapping)
        let result = expr.eval(&env(&[("a", 0xFFFF_FFFF), ("b", 1)]));
        assert_eq!(result, EvalResult::Bv(0));
    }

    #[test]
    fn test_trap_if_zero_poisons_at_guard_zero_only() {
        // The x86 IDIV/DIV #DE-trap model (#79). value = a/b masked to 8 bits,
        // guarded on b. At b != 0 the node is the defined value; at b == 0 it is
        // POISON (no defined hardware result).
        let a = SmtExpr::var("a", 8);
        let b = SmtExpr::var("b", 8);
        let value = a.clone().bvudiv(b.clone());
        let trapped = value.trap_if_zero(b.clone());

        // b != 0: defined.
        assert_eq!(
            trapped.eval(&env(&[("a", 20), ("b", 4)])),
            EvalResult::Bv(5),
            "off the trap point, TrapIfZero is exactly the underlying value"
        );
        // b == 0: poison.
        assert_eq!(
            trapped.eval(&env(&[("a", 20), ("b", 0)])),
            EvalResult::Poison,
            "at guard == 0, TrapIfZero must evaluate to Poison (the #DE trap has no defined result)"
        );
    }

    #[test]
    fn test_poison_is_unequal_to_everything_including_itself() {
        // Poison must refute against ANY value, even the div-by-zero sentinel (0)
        // and even another Poison — this is what makes the divisor!=0 precond
        // load-bearing in the native lane.
        assert!(!EvalResult::Poison.semantically_equal(&EvalResult::Bv(0)));
        assert!(!EvalResult::Bv(0).semantically_equal(&EvalResult::Poison));
        assert!(!EvalResult::Poison.semantically_equal(&EvalResult::Poison));
        assert!(!EvalResult::Poison.semantically_equal(&EvalResult::Bv128(0)));
    }

    // -----------------------------------------------------------------------
    // FlatProg differential property test (the mandatory soundness gate).
    //
    // FlatProg REPLACES the interpreter on the compiled path, so a single
    // transcription slip = WRONG verdicts = a silent proof-system miscompile.
    // This test proves, arm-for-arm, that `FlatProg::compile(e).eval(env)`
    // equals `e.try_eval(env)` (DERIVED EvalResult equality — Poison==Poison is
    // true, cross-variant Bv-vs-Bv128 is unequal; NOT semantically_equal, which
    // would false-fail the div-by-zero trap point where both sides are Poison)
    // over: (1) the EXACT reconstruct_x86_division obligation trees for every
    // width x signedness incl. divisor=0 (trap) and INT_MIN/-1 (overflow);
    // (2) handcrafted 128-bit expressions covering every >64 arm the division
    // trees do not; (3) store/select + memory-load expressions; and (4) random
    // subset expressions.
    // -----------------------------------------------------------------------

    /// Build an [`EvalEnv`] with the given (name, value) pairs inserted IN ORDER
    /// (so slot i == the i-th name — the order `FlatProg::compile`'s `inputs`
    /// resolves against). Values are stored raw; both evaluators mask per width.
    fn eval_env(pairs: &[(&str, u64)]) -> EvalEnv {
        let mut e = EvalEnv::default();
        for (n, v) in pairs {
            e.insert((*n).to_string(), *v);
        }
        e
    }

    /// Assert the tape matches the interpreter at one point, with DERIVED
    /// EvalResult equality (Poison==Poison). Returns 1 (checked) or 0 (skipped —
    /// out of subset, which is always sound: the caller falls back to try_eval).
    fn assert_flat_eq(
        e: &SmtExpr,
        inputs: &[(String, u32)],
        env: &EvalEnv,
        scratch: &mut Vec<SVal>,
    ) -> u64 {
        match FlatProg::compile(e, inputs) {
            Some(prog) => {
                let got = prog.eval(env, scratch);
                let want = e
                    .try_eval(env)
                    .expect("interpreter must evaluate a subset expression");
                assert_eq!(got, want, "FlatProg diverged from try_eval for expr `{e}`");
                1
            }
            None => 0,
        }
    }

    /// Rebuild the exact `reconstruct_x86_division` trees (trust_ir, aarch64,
    /// preconditions) for a given width and signedness. Mirrors
    /// x86_64_function_verifier::reconstruct_x86_division / trust_ir_semantics.
    fn div_trees(width: u32, signed: bool) -> (SmtExpr, SmtExpr, Vec<SmtExpr>) {
        let dwidth = width * 2;
        let extra = dwidth - width;
        let rax = SmtExpr::var("recon_rax", width);
        let divisor = SmtExpr::var("recon_divisor", width);
        let (dividend_2w, divisor_2w) = if signed {
            (rax.clone().sign_ext(extra), divisor.clone().sign_ext(extra))
        } else {
            (rax.clone().zero_ext(extra), divisor.clone().zero_ext(extra))
        };
        let (q_2w, r_2w) = if signed {
            let q = dividend_2w.clone().bvsdiv(divisor_2w.clone());
            let r = dividend_2w
                .clone()
                .bvsub(q.clone().bvmul(divisor_2w.clone()));
            (q, r)
        } else {
            let q = dividend_2w.clone().bvudiv(divisor_2w.clone());
            let r = dividend_2w
                .clone()
                .bvsub(q.clone().bvmul(divisor_2w.clone()));
            (q, r)
        };
        let machine_q = q_2w.extract(width - 1, 0);
        let machine_r = r_2w.extract(width - 1, 0);
        let aarch64 = machine_q.concat(machine_r).trap_if_zero(divisor.clone());
        let (ir_q, ir_r) = if signed {
            let q = rax.clone().bvsdiv(divisor.clone());
            let r = rax
                .clone()
                .bvsub(rax.clone().bvsdiv(divisor.clone()).bvmul(divisor.clone()));
            (q, r)
        } else {
            let q = rax.clone().bvudiv(divisor.clone());
            let r = rax
                .clone()
                .bvsub(rax.clone().bvudiv(divisor.clone()).bvmul(divisor.clone()));
            (q, r)
        };
        let trust_ir = ir_q.concat(ir_r);
        let zero = SmtExpr::bv_const(0, width);
        let mut preconds = vec![divisor.clone().eq_expr(zero).not_expr()];
        if signed {
            let int_min = SmtExpr::bv_const(1u64 << (width - 1), width);
            let neg_one = SmtExpr::bv_const(mask(u64::MAX, width), width);
            let overflow = rax
                .clone()
                .eq_expr(int_min)
                .and_expr(divisor.clone().eq_expr(neg_one));
            preconds.push(overflow.not_expr());
        }
        (trust_ir, aarch64, preconds)
    }

    #[inline]
    fn lcg(s: &mut u64) -> u64 {
        *s = s
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        *s
    }

    /// Random bitvector-sorted subset expression, width <= 64 (the >64 arms are
    /// covered by the division trees + handcrafted list). Every op is total, so
    /// eager tape evaluation cannot panic or diverge from the interpreter.
    fn gen_bv(s: &mut u64, depth: u32) -> SmtExpr {
        if depth == 0 || lcg(s) % 100 < 30 {
            match lcg(s) % 6 {
                0 => SmtExpr::var("a", 8),
                1 => SmtExpr::var("b", 16),
                2 => SmtExpr::var("c", 32),
                3 => SmtExpr::var("d", 64),
                4 => {
                    let w = [8u32, 16, 32, 64][(lcg(s) % 4) as usize];
                    SmtExpr::bv_const(lcg(s), w)
                }
                _ => SmtExpr::var("d", 64),
            }
        } else {
            let a = gen_bv(s, depth - 1);
            let b = gen_bv(s, depth - 1);
            match lcg(s) % 14 {
                0 => a.bvadd(b),
                1 => a.bvsub(b),
                2 => a.bvmul(b),
                3 => a.bvand(b),
                4 => a.bvor(b),
                5 => a.bvxor(b),
                6 => a.bvshl(b),
                7 => a.bvlshr(b),
                8 => a.bvashr(b),
                9 => a.bvsdiv(b),
                10 => a.bvudiv(b),
                11 => a.bvurem(b),
                12 => a.bvneg(),
                _ => {
                    let cond = gen_bool(s, depth - 1);
                    SmtExpr::ite(cond, a, b)
                }
            }
        }
    }

    /// Random bool-sorted subset expression (comparisons + boolean connectives).
    fn gen_bool(s: &mut u64, depth: u32) -> SmtExpr {
        if depth == 0 || lcg(s) % 100 < 45 {
            let a = gen_bv(s, 1);
            let b = gen_bv(s, 1);
            match lcg(s) % 9 {
                0 => a.eq_expr(b),
                1 => a.bvslt(b),
                2 => a.bvsge(b),
                3 => a.bvsgt(b),
                4 => a.bvsle(b),
                5 => a.bvult(b),
                6 => a.bvugt(b),
                7 => a.bvule(b),
                _ => a.bvuge(b),
            }
        } else {
            match lcg(s) % 3 {
                0 => gen_bool(s, depth - 1).not_expr(),
                1 => gen_bool(s, depth - 1).and_expr(gen_bool(s, depth - 1)),
                _ => gen_bool(s, depth - 1).or_expr(gen_bool(s, depth - 1)),
            }
        }
    }

    #[test]
    fn flatprog_matches_interpreter_differential_fuzz() {
        let mut scratch: Vec<SVal> = Vec::new();
        let mut checks: u64 = 0;
        let mut exprs: u64 = 0;

        // --- Part 1: the exact reconstruct_x86_division obligation trees. ---
        for &width in &[8u32, 16, 32, 64] {
            for &signed in &[true, false] {
                let (trust_ir, aarch64, preconds) = div_trees(width, signed);
                exprs += 2 + preconds.len() as u64;
                let inputs = vec![
                    ("recon_rax".to_string(), width),
                    ("recon_divisor".to_string(), width),
                ];
                // Interesting per-width values: 0, 1, 2, -1/max, int_min, int_max,
                // max-1. Covers divisor=0 (trap), (INT_MIN,-1) (overflow), etc.
                let wmax = mask(u64::MAX, width);
                let int_min = 1u64 << (width - 1);
                let int_max = int_min.wrapping_sub(1);
                let vals = [0u64, 1, 2, wmax, int_min, int_max, wmax.wrapping_sub(1)];
                for &rax in &vals {
                    for &div in &vals {
                        let env = eval_env(&[("recon_rax", rax), ("recon_divisor", div)]);
                        checks += assert_flat_eq(&trust_ir, &inputs, &env, &mut scratch);
                        checks += assert_flat_eq(&aarch64, &inputs, &env, &mut scratch);
                        for p in &preconds {
                            checks += assert_flat_eq(p, &inputs, &env, &mut scratch);
                        }
                    }
                }
                // A batch of random (rax, divisor) points too.
                let mut s = 0x1234_5678_9abc_def0 ^ ((width as u64) << 8) ^ (signed as u64);
                for _ in 0..256 {
                    let rax = mask(lcg(&mut s), width);
                    let div = mask(lcg(&mut s), width);
                    let env = eval_env(&[("recon_rax", rax), ("recon_divisor", div)]);
                    checks += assert_flat_eq(&trust_ir, &inputs, &env, &mut scratch);
                    checks += assert_flat_eq(&aarch64, &inputs, &env, &mut scratch);
                    for p in &preconds {
                        checks += assert_flat_eq(p, &inputs, &env, &mut scratch);
                    }
                }
            }
        }

        // --- Part 2: handcrafted 128-bit + cross-variant exprs. ---
        // These exercise the >64 arithmetic/shift/bitwise/neg arms NOT reached by
        // the division trees, the 128-bit SDiv INT_MIN/-1 overflow gate, and the
        // cross-variant (Bv128 vs Bv) intermediate Eq quirk.
        let a64 = || SmtExpr::var("a", 64);
        let b64 = || SmtExpr::var("b", 64);
        let one128 = || SmtExpr::bv_const(1, 128);
        let min128 = || one128().bvshl(SmtExpr::bv_const(127, 128)); // 2^127 == i128::MIN bits
        let neg1_128 = || one128().bvneg(); // all-ones 128 == -1
        let wide: Vec<SmtExpr> = vec![
            a64().sign_ext(64).bvadd(b64().sign_ext(64)),
            a64().zero_ext(64).bvand(b64().zero_ext(64)),
            a64().zero_ext(64).bvor(b64().zero_ext(64)),
            a64().zero_ext(64).bvxor(b64().zero_ext(64)),
            a64().zero_ext(64).bvshl(b64().zero_ext(64)),
            a64().zero_ext(64).bvlshr(b64().zero_ext(64)),
            a64().sign_ext(64).bvashr(b64().zero_ext(64)),
            a64().sign_ext(64).bvneg(),
            a64().zero_ext(64),          // ZExt -> Bv128
            a64().sign_ext(64),          // SExt -> Bv128
            min128().bvsdiv(neg1_128()), // 128-bit SDiv overflow gate
            min128().bvudiv(neg1_128()),
            a64().sign_ext(64).eq_expr(b64()), // cross-variant Eq: Bv128 vs Bv
            SmtExpr::bv_const(5, 128).eq_expr(SmtExpr::bv_const(5, 64)),
            a64().bvurem(b64()), // URem @ 64
            a64().sign_ext(64).bvslt(b64().sign_ext(64)),
            a64().zero_ext(64).bvadd(b64().zero_ext(64)).extract(63, 0), // Extract of a Bv128
        ];
        let inputs64 = vec![("a".to_string(), 64u32), ("b".to_string(), 64u32)];
        let avals = [
            0u64,
            1,
            u64::MAX,
            1u64 << 63,
            (1u64 << 63) - 1,
            0xdead_beef_cafe_babe,
            2,
        ];
        exprs += wide.len() as u64;
        for e in &wide {
            for &a in &avals {
                for &b in &avals {
                    let env = eval_env(&[("a", a), ("b", b)]);
                    checks += assert_flat_eq(e, &inputs64, &env, &mut scratch);
                }
            }
        }

        // --- Part 3: scalarized array reads + deterministic memory loads. ---
        // This is the exact shape used by x86 atomic/CMPXCHG proofs: byte stores
        // under an array-valued branch followed by one or more scalar loads.
        // FlatProg must apply read-over-write rather than falling back to the
        // allocation-heavy concrete-array interpreter for every 100k sample.
        let idx = SmtExpr::var("idx", 64);
        let write_idx = SmtExpr::var("write_idx", 64);
        let value = SmtExpr::var("value", 8);
        let choose = SmtExpr::var("choose", 1).eq_expr(SmtExpr::bv_const(1, 1));
        let zero_mem = SmtExpr::const_array(SmtSort::BitVec(64), SmtExpr::bv_const(0, 8));
        let one_store = SmtExpr::store(zero_mem.clone(), write_idx.clone(), value.clone());
        let two_stores = SmtExpr::store(
            one_store.clone(),
            write_idx.clone().bvadd(SmtExpr::bv_const(1, 64)),
            value.clone().bvxor(SmtExpr::bv_const(0xff, 8)),
        );
        let branch_mem = SmtExpr::ite(choose, two_stores, one_store);
        let selected = SmtExpr::select(branch_mem, idx.clone());
        let deterministic_load = SmtExpr::mem_load(idx.clone(), 16, true, 64);
        let memory_exprs = [selected, deterministic_load];
        let memory_inputs = vec![
            ("idx".to_string(), 64),
            ("write_idx".to_string(), 64),
            ("value".to_string(), 8),
            ("choose".to_string(), 1),
        ];
        let memory_points = [
            (0, 0, 0, 0),
            (0, 0, 0xa5, 1),
            (1, 0, 0xa5, 1),
            (2, 0, 0xa5, 1),
            (u64::MAX, u64::MAX, 0x5a, 0),
            (0, u64::MAX, 0x5a, 1),
            (0x1234, 0x1234, 0xff, 1),
        ];
        exprs += memory_exprs.len() as u64;
        for e in &memory_exprs {
            for &(read, write, byte, branch) in &memory_points {
                let env = eval_env(&[
                    ("idx", read),
                    ("write_idx", write),
                    ("value", byte),
                    ("choose", branch),
                ]);
                checks += assert_flat_eq(e, &memory_inputs, &env, &mut scratch);
            }
        }

        // --- Part 4: random subset expressions (<= 64). ---
        let inputs4 = vec![
            ("a".to_string(), 8u32),
            ("b".to_string(), 16u32),
            ("c".to_string(), 32u32),
            ("d".to_string(), 64u32),
        ];
        let mut gs: u64 = 0xf00d_1234_5678_9abc;
        for _ in 0..600 {
            let e = if lcg(&mut gs).is_multiple_of(4) {
                gen_bool(&mut gs, 4)
            } else {
                gen_bv(&mut gs, 4)
            };
            exprs += 1;
            let mut es = lcg(&mut gs);
            for _ in 0..24 {
                let env = eval_env(&[
                    ("a", lcg(&mut es)),
                    ("b", lcg(&mut es)),
                    ("c", lcg(&mut es)),
                    ("d", lcg(&mut es)),
                ]);
                checks += assert_flat_eq(&e, &inputs4, &env, &mut scratch);
            }
            // Also a few all-edge points (all-zeros, all-ones, sign bits).
            for &edge in &[0u64, 1, u64::MAX, 1u64 << 63] {
                let env = eval_env(&[("a", edge), ("b", edge), ("c", edge), ("d", edge)]);
                checks += assert_flat_eq(&e, &inputs4, &env, &mut scratch);
            }
        }

        assert!(checks > 20_000, "expected a large fuzz sweep, got {checks}");
        eprintln!(
            "FlatProg differential fuzz: {exprs} exprs x samples = {checks} point-checks, 0 divergences"
        );
    }

    #[test]
    fn test_trap_if_zero_serializes_with_declared_poison_const() {
        // The SMT-LIB form references a fresh poison constant; the serializer must
        // be able to enumerate it for declaration (so the lowered formula is
        // well-formed and the solver treats the trap value as arbitrary).
        let a = SmtExpr::var("a", 8);
        let b = SmtExpr::var("b", 8);
        let trapped = a.clone().bvudiv(b.clone()).trap_if_zero(b.clone());
        let decls = collect_trap_poison_decls(&trapped);
        assert_eq!(
            decls.len(),
            1,
            "exactly one poison constant for one trap node"
        );
        assert_eq!(decls[0].1, 8, "the poison constant has the value's width");
        let s = format!("{trapped}");
        assert!(
            s.contains(&decls[0].0),
            "the SMT-LIB form must reference the declared poison const"
        );
        assert!(
            s.contains("ite"),
            "the SMT-LIB form is an ite guarded on the divisor"
        );
    }

    #[test]
    fn test_bvsub() {
        let a = SmtExpr::var("a", 32);
        let b = SmtExpr::var("b", 32);
        let expr = a.bvsub(b);
        let result = expr.eval(&env(&[("a", 10), ("b", 3)]));
        assert_eq!(result, EvalResult::Bv(7));
    }

    #[test]
    fn test_bvmul() {
        let a = SmtExpr::var("a", 32);
        let b = SmtExpr::var("b", 32);
        let expr = a.bvmul(b);
        let result = expr.eval(&env(&[("a", 7), ("b", 6)]));
        assert_eq!(result, EvalResult::Bv(42));
    }

    #[test]
    fn test_bvurem() {
        let a = SmtExpr::var("a", 32);
        let b = SmtExpr::var("b", 32);
        let expr = a.bvurem(b);
        let result = expr.eval(&env(&[("a", 10), ("b", 4)]));
        assert_eq!(result, EvalResult::Bv(2));
    }

    #[test]
    fn test_bvurem_by_zero_returns_dividend() {
        let a = SmtExpr::var("a", 32);
        let zero = SmtExpr::bv_const(0, 32);
        let expr = a.bvurem(zero);
        let result = expr.eval(&env(&[("a", 10)]));
        assert_eq!(result, EvalResult::Bv(10));
    }

    #[test]
    fn test_bvneg() {
        let a = SmtExpr::var("a", 32);
        let expr = a.bvneg();
        // neg(1) = 0xFFFFFFFF in 32-bit
        let result = expr.eval(&env(&[("a", 1)]));
        assert_eq!(result, EvalResult::Bv(0xFFFF_FFFF));
    }

    // 128-bit signed/unsigned division: the x86 IDIV/DIV double-width dividend
    // path. A 64-bit dividend sign/zero-extended to 128 divided by a 128-bit
    // divisor; the result is extracted back to 64. This exercises the new
    // width>64 BvSDiv/BvUDiv branches (a u64-truncated path would diverge).
    #[test]
    fn test_bvsdiv_128bit_negative_dividend() {
        // dividend = sext(-100, 128); divisor = sext(7, 128). -100 / 7 = -14 (RTZ).
        let a = SmtExpr::var("a", 64).sign_ext(64); // 128-bit
        let b = SmtExpr::var("b", 64).sign_ext(64); // 128-bit
        let q = a.bvsdiv(b);
        // Truncate to 64 bits and read as signed.
        let lo = q.extract(63, 0);
        let neg100 = (-100i64) as u64;
        let result = lo.eval(&env(&[("a", neg100), ("b", 7)]));
        assert_eq!(result, EvalResult::Bv((-14i64) as u64));
    }

    #[test]
    fn test_bvudiv_128bit_high_bit_dividend() {
        // dividend = zext(0x8000_0000_0000_0000, 128) (huge positive when unsigned);
        // divisor = zext(2, 128). result = 0x4000_0000_0000_0000.
        let a = SmtExpr::var("a", 64).zero_ext(64);
        let b = SmtExpr::var("b", 64).zero_ext(64);
        let q = a.bvudiv(b).extract(63, 0);
        let result = q.eval(&env(&[("a", 0x8000_0000_0000_0000), ("b", 2)]));
        assert_eq!(result, EvalResult::Bv(0x4000_0000_0000_0000));
    }

    // The SOUNDNESS witness: the SAME 64-bit dividend with the high bit set gives
    // DIFFERENT 128-bit quotients under signed vs unsigned division ⇒ an
    // IDIV-as-DIV mislowering is detectable.
    #[test]
    fn test_signed_vs_unsigned_128bit_divide_diverge_on_negative() {
        let neg = (-100i64) as u64;
        let sa = SmtExpr::var("a", 64).sign_ext(64);
        let sb = SmtExpr::var("b", 64).sign_ext(64);
        let signed_q = sa
            .bvsdiv(sb)
            .extract(63, 0)
            .eval(&env(&[("a", neg), ("b", 7)]));
        let ua = SmtExpr::var("a", 64).zero_ext(64);
        let ub = SmtExpr::var("b", 64).zero_ext(64);
        let unsigned_q = ua
            .bvudiv(ub)
            .extract(63, 0)
            .eval(&env(&[("a", neg), ("b", 7)]));
        assert_ne!(
            signed_q, unsigned_q,
            "signed and unsigned 128-bit divide must differ on a negative dividend"
        );
    }

    #[test]
    fn test_bvneg_zero() {
        let a = SmtExpr::var("a", 32);
        let expr = a.bvneg();
        let result = expr.eval(&env(&[("a", 0)]));
        assert_eq!(result, EvalResult::Bv(0));
    }

    #[test]
    fn test_eq_true() {
        let a = SmtExpr::var("a", 32);
        let b = SmtExpr::var("b", 32);
        let expr = a.eq_expr(b);
        let result = expr.eval(&env(&[("a", 42), ("b", 42)]));
        assert_eq!(result, EvalResult::Bool(true));
    }

    #[test]
    fn test_eq_false() {
        let a = SmtExpr::var("a", 32);
        let b = SmtExpr::var("b", 32);
        let expr = a.eq_expr(b);
        let result = expr.eval(&env(&[("a", 42), ("b", 43)]));
        assert_eq!(result, EvalResult::Bool(false));
    }

    #[test]
    fn test_sign_extend_negative() {
        // -1 in 8 bits = 0xFF
        assert_eq!(sign_extend(0xFF, 8), -1i64);
        // -128 in 8 bits = 0x80
        assert_eq!(sign_extend(0x80, 8), -128i64);
    }

    #[test]
    fn test_bvslt() {
        let a = SmtExpr::var("a", 32);
        let b = SmtExpr::var("b", 32);
        let expr = a.bvslt(b);
        // -1 < 0 in signed
        let neg1_32 = 0xFFFF_FFFFu64;
        let result = expr.eval(&env(&[("a", neg1_32), ("b", 0)]));
        assert_eq!(result, EvalResult::Bool(true));
    }

    #[test]
    fn test_display() {
        let a = SmtExpr::var("a", 32);
        let b = SmtExpr::var("b", 32);
        let expr = a.bvadd(b);
        assert_eq!(format!("{}", expr), "(bvadd a b)");
    }

    #[test]
    fn test_mask_widths() {
        assert_eq!(mask(0xFF, 8), 0xFF);
        assert_eq!(mask(0x1FF, 8), 0xFF);
        assert_eq!(mask(0xFFFF_FFFF_FFFF_FFFF, 32), 0xFFFF_FFFF);
    }

    #[test]
    fn test_concat_basic() {
        // concat(0xAB : 8bit, 0xCD : 8bit) = 0xABCD : 16bit
        let hi = SmtExpr::bv_const(0xAB, 8);
        let lo = SmtExpr::bv_const(0xCD, 8);
        let expr = hi.concat(lo);
        assert_eq!(expr.bv_width(), 16);
        let result = expr.eval(&env(&[]));
        assert_eq!(result, EvalResult::Bv(0xABCD));
    }

    #[test]
    fn test_concat_32bit() {
        // concat(0xDEAD : 16bit, 0xBEEF : 16bit) = 0xDEADBEEF : 32bit
        let hi = SmtExpr::bv_const(0xDEAD, 16);
        let lo = SmtExpr::bv_const(0xBEEF, 16);
        let expr = hi.concat(lo);
        assert_eq!(expr.bv_width(), 32);
        let result = expr.eval(&env(&[]));
        assert_eq!(result, EvalResult::Bv(0xDEAD_BEEF));
    }

    #[test]
    fn test_zero_extend() {
        // zero_extend(0xFF : 8bit, 8) = 0x00FF : 16bit
        let a = SmtExpr::bv_const(0xFF, 8);
        let expr = a.zero_ext(8);
        assert_eq!(expr.bv_width(), 16);
        let result = expr.eval(&env(&[]));
        assert_eq!(result, EvalResult::Bv(0xFF));
    }

    #[test]
    fn test_sign_extend_expr() {
        // sign_extend(0xFF : 8bit, 8) = 0xFFFF : 16bit (since 0xFF is -1 in 8-bit)
        let a = SmtExpr::bv_const(0xFF, 8);
        let expr = a.sign_ext(8);
        assert_eq!(expr.bv_width(), 16);
        let result = expr.eval(&env(&[]));
        assert_eq!(result, EvalResult::Bv(0xFFFF));
    }

    #[test]
    fn test_sign_extend_positive() {
        // sign_extend(0x7F : 8bit, 8) = 0x007F : 16bit (positive stays positive)
        let a = SmtExpr::bv_const(0x7F, 8);
        let expr = a.sign_ext(8);
        assert_eq!(expr.bv_width(), 16);
        let result = expr.eval(&env(&[]));
        assert_eq!(result, EvalResult::Bv(0x7F));
    }

    #[test]
    fn test_extract_then_concat_roundtrip() {
        // Extract two 8-bit lanes from a 16-bit value, then concat back.
        let v = SmtExpr::var("v", 16);
        let lo = v.clone().extract(7, 0); // bits [7:0]
        let hi = v.clone().extract(15, 8); // bits [15:8]
        let reassembled = hi.concat(lo);
        // For v = 0xABCD: lo=0xCD, hi=0xAB, concat=0xABCD
        let result = reassembled.eval(&env(&[("v", 0xABCD)]));
        assert_eq!(result, EvalResult::Bv(0xABCD));
    }

    #[test]
    fn test_lane_extract_2s() {
        // 64-bit vector with 2 x 32-bit lanes: [0x12345678, 0xAABBCCDD]
        // Lane 0 (bits [31:0]) = 0xAABBCCDD, Lane 1 (bits [63:32]) = 0x12345678
        let v = SmtExpr::var("v", 64);
        let lane0 = lane_extract(&v, VectorArrangement::S2, 0);
        let lane1 = lane_extract(&v, VectorArrangement::S2, 1);
        let val = 0x12345678_AABBCCDD_u64;
        let e = env(&[("v", val)]);
        assert_eq!(lane0.eval(&e), EvalResult::Bv(0xAABBCCDD));
        assert_eq!(lane1.eval(&e), EvalResult::Bv(0x12345678));
    }

    #[test]
    fn test_lane_split_concat_roundtrip_128() {
        // A 128-bit vector built from two 64-bit halves, split into 4x32-bit lanes
        // and reassembled — lane_concat ∘ lane_split is the identity.
        let v = SmtExpr::var("hi", 64).concat(SmtExpr::var("lo", 64));
        let lanes = lane_split(&v, 32);
        assert_eq!(lanes.len(), 4, "128 / 32 = 4 lanes");
        let reassembled = lane_concat(&lanes);
        let e = env(&[("lo", 0x1111_1111_2222_2222), ("hi", 0x3333_3333_4444_4444)]);
        assert_eq!(reassembled.eval(&e), v.eval(&e));
    }

    #[test]
    fn test_lane_split_lane0_is_low_bits() {
        // lanes[0] is the LEAST-significant lane.
        let v = SmtExpr::var("hi", 64).concat(SmtExpr::var("lo", 64));
        let lanes = lane_split(&v, 32);
        let e = env(&[("lo", 0xAAAA_AAAA_BBBB_BBBB), ("hi", 0xCCCC_CCCC_DDDD_DDDD)]);
        assert_eq!(lanes[0].eval(&e), EvalResult::Bv(0xBBBB_BBBB));
        assert_eq!(lanes[1].eval(&e), EvalResult::Bv(0xAAAA_AAAA));
        assert_eq!(lanes[2].eval(&e), EvalResult::Bv(0xDDDD_DDDD));
        assert_eq!(lanes[3].eval(&e), EvalResult::Bv(0xCCCC_CCCC));
    }

    #[test]
    fn test_concat_lanes_roundtrip() {
        // Decompose a 64-bit value as 2 x 32-bit lanes (S2), then reassemble.
        let v64 = SmtExpr::var("v64", 64);
        let l0 = lane_extract(&v64, VectorArrangement::S2, 0);
        let l1 = lane_extract(&v64, VectorArrangement::S2, 1);
        let reassembled = concat_lanes(&[l0, l1], VectorArrangement::S2);
        let val = 0xDEAD_BEEF_CAFE_BABEu64;
        let result = reassembled.eval(&env(&[("v64", val)]));
        assert_eq!(result, EvalResult::Bv(val));
    }

    #[test]
    fn test_map_lanes_binary_add_s2() {
        // Two 64-bit vectors, each with 2 x 32-bit lanes.
        // a = [0x00000001, 0x00000002], b = [0x00000003, 0x00000004]
        // Result: [(1+3), (2+4)] = [0x00000004, 0x00000006]
        let a = SmtExpr::var("a", 64);
        let b = SmtExpr::var("b", 64);
        let result = map_lanes_binary(&a, &b, VectorArrangement::S2, |x, y| x.bvadd(y));
        // a: lane0=0x00000002, lane1=0x00000001 (little-endian bit layout)
        // Encoding: 0x00000001_00000002
        let a_val = (1u64 << 32) | 2;
        let b_val = (3u64 << 32) | 4;
        let e = env(&[("a", a_val), ("b", b_val)]);
        let r = result.eval(&e);
        // Expected: lane0=2+4=6, lane1=1+3=4 => (4 << 32) | 6
        assert_eq!(r, EvalResult::Bv((4u64 << 32) | 6));
    }

    #[test]
    fn test_concat_display() {
        let hi = SmtExpr::var("hi", 8);
        let lo = SmtExpr::var("lo", 8);
        let expr = hi.concat(lo);
        assert_eq!(format!("{}", expr), "(concat hi lo)");
    }

    // -----------------------------------------------------------------------
    // Array theory tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_const_array_select() {
        // Create a constant array filled with 42, then select index 0.
        let arr = SmtExpr::const_array(SmtSort::BitVec(32), SmtExpr::bv_const(42, 32));
        let expr = SmtExpr::select(arr, SmtExpr::bv_const(0, 32));
        let result = expr.try_eval(&HashMap::new()).unwrap();
        assert_eq!(result, EvalResult::Bv(42));
    }

    #[test]
    fn test_const_array_select_any_index() {
        // Constant array: any index should return the default.
        let arr = SmtExpr::const_array(SmtSort::BitVec(8), SmtExpr::bv_const(0xFF, 8));
        let expr = SmtExpr::select(arr, SmtExpr::bv_const(99, 8));
        let result = expr.try_eval(&HashMap::new()).unwrap();
        assert_eq!(result, EvalResult::Bv(0xFF));
    }

    #[test]
    fn test_store_then_select() {
        // store(const_array(0), idx=5, val=100) then select idx=5
        let arr = SmtExpr::const_array(SmtSort::BitVec(8), SmtExpr::bv_const(0, 32));
        let arr = SmtExpr::store(arr, SmtExpr::bv_const(5, 8), SmtExpr::bv_const(100, 32));
        let expr = SmtExpr::select(arr, SmtExpr::bv_const(5, 8));
        let result = expr.try_eval(&HashMap::new()).unwrap();
        assert_eq!(result, EvalResult::Bv(100));
    }

    #[test]
    fn test_store_preserves_other_indices() {
        // store at index 5, select at index 3 should return default.
        let arr = SmtExpr::const_array(SmtSort::BitVec(8), SmtExpr::bv_const(0, 32));
        let arr = SmtExpr::store(arr, SmtExpr::bv_const(5, 8), SmtExpr::bv_const(100, 32));
        let expr = SmtExpr::select(arr, SmtExpr::bv_const(3, 8));
        let result = expr.try_eval(&HashMap::new()).unwrap();
        assert_eq!(result, EvalResult::Bv(0));
    }

    #[test]
    fn test_array_sort() {
        let arr = SmtExpr::const_array(SmtSort::BitVec(32), SmtExpr::bv_const(0, 64));
        assert_eq!(
            arr.sort(),
            SmtSort::Array(Box::new(SmtSort::BitVec(32)), Box::new(SmtSort::BitVec(64)),)
        );
    }

    #[test]
    fn test_array_display() {
        let arr = SmtExpr::const_array(SmtSort::BitVec(32), SmtExpr::bv_const(0, 32));
        let sel = SmtExpr::select(arr.clone(), SmtExpr::bv_const(1, 32));
        assert_eq!(
            format!("{}", sel),
            "(select ((as const (Array (_ BitVec 32) (_ BitVec 32))) (_ bv0 32)) (_ bv1 32))"
        );

        let st = SmtExpr::store(arr, SmtExpr::bv_const(1, 32), SmtExpr::bv_const(42, 32));
        assert_eq!(
            format!("{}", st),
            "(store ((as const (Array (_ BitVec 32) (_ BitVec 32))) (_ bv0 32)) (_ bv1 32) (_ bv42 32))"
        );
    }

    // -----------------------------------------------------------------------
    // Floating-point theory tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_fp32_add() {
        let a = SmtExpr::fp32_const(1.5f32);
        let b = SmtExpr::fp32_const(2.5f32);
        let expr = SmtExpr::fp_add(RoundingMode::RNE, a, b);
        let result = expr.try_eval(&HashMap::new()).unwrap();
        assert_eq!(result, EvalResult::Float(4.0));
    }

    #[test]
    fn test_fp64_mul() {
        let a = SmtExpr::fp64_const(3.0f64);
        let b = SmtExpr::fp64_const(7.0f64);
        let expr = SmtExpr::fp_mul(RoundingMode::RNE, a, b);
        let result = expr.try_eval(&HashMap::new()).unwrap();
        assert_eq!(result, EvalResult::Float(21.0));
    }

    #[test]
    fn test_fp_div() {
        let a = SmtExpr::fp64_const(10.0);
        let b = SmtExpr::fp64_const(4.0);
        let expr = SmtExpr::fp_div(RoundingMode::RNE, a, b);
        let result = expr.try_eval(&HashMap::new()).unwrap();
        assert_eq!(result, EvalResult::Float(2.5));
    }

    #[test]
    fn test_fp_neg() {
        let a = SmtExpr::fp64_const(42.0);
        let expr = a.fp_neg();
        let result = expr.try_eval(&HashMap::new()).unwrap();
        assert_eq!(result, EvalResult::Float(-42.0));
    }

    #[test]
    fn test_fp_eq() {
        let a = SmtExpr::fp64_const(1.0);
        let b = SmtExpr::fp64_const(1.0);
        let expr = a.fp_eq(b);
        let result = expr.try_eval(&HashMap::new()).unwrap();
        assert_eq!(result, EvalResult::Bool(true));
    }

    #[test]
    fn test_fp_lt() {
        let a = SmtExpr::fp64_const(1.0);
        let b = SmtExpr::fp64_const(2.0);
        let expr = a.fp_lt(b);
        let result = expr.try_eval(&HashMap::new()).unwrap();
        assert_eq!(result, EvalResult::Bool(true));
    }

    #[test]
    fn test_fp_sort() {
        let a = SmtExpr::fp32_const(1.0f32);
        assert_eq!(a.sort(), SmtSort::FloatingPoint(8, 24));

        let b = SmtExpr::fp64_const(1.0);
        assert_eq!(b.sort(), SmtSort::FloatingPoint(11, 53));
    }

    #[test]
    fn test_fp_display() {
        let expr = SmtExpr::fp_add(
            RoundingMode::RNE,
            SmtExpr::fp64_const(1.0),
            SmtExpr::fp64_const(2.0),
        );
        let s = format!("{}", expr);
        assert!(s.starts_with("(fp.add RNE"));
    }

    #[test]
    fn test_smt_sort_constructors() {
        assert_eq!(SmtSort::fp16(), SmtSort::FloatingPoint(5, 11));
        assert_eq!(SmtSort::fp32(), SmtSort::FloatingPoint(8, 24));
        assert_eq!(SmtSort::fp64(), SmtSort::FloatingPoint(11, 53));
        assert_eq!(
            SmtSort::bv_array(32, 64),
            SmtSort::Array(Box::new(SmtSort::BitVec(32)), Box::new(SmtSort::BitVec(64)))
        );
    }

    #[test]
    fn test_smt_sort_try_from_f16() {
        assert_eq!(SmtSort::try_from(Type::F16).unwrap(), SmtSort::fp16());
    }

    #[test]
    fn test_smt_sort_try_from_enum_rejects_explicitly() {
        let enum_ty = Type::Enum {
            tag_width: trust_cg_ir::function::EnumTagWidth::U8,
            variants: vec![vec![], vec![Type::I64]],
        };
        let err = SmtSort::try_from(enum_ty).unwrap_err();
        match err {
            SmtError::UnsupportedType(msg) => assert!(msg.contains("enum")),
            other => panic!("expected UnsupportedType, got {other:?}"),
        }
    }

    #[test]
    fn test_smt_sort_display() {
        assert_eq!(format!("{}", SmtSort::BitVec(32)), "(_ BitVec 32)");
        assert_eq!(format!("{}", SmtSort::Bool), "Bool");
        assert_eq!(format!("{}", SmtSort::fp32()), "(_ FloatingPoint 8 24)");
        assert_eq!(
            format!("{}", SmtSort::bv_array(32, 8)),
            "(Array (_ BitVec 32) (_ BitVec 8))"
        );
    }

    // -----------------------------------------------------------------------
    // Uninterpreted function tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_uf_display() {
        let uf = SmtExpr::uf("hash", vec![SmtExpr::bv_const(42, 32)], SmtSort::BitVec(64));
        assert_eq!(format!("{}", uf), "(hash (_ bv42 32))");
    }

    #[test]
    fn test_uf_decl_display() {
        let decl = SmtExpr::uf_decl("hash", vec![SmtSort::BitVec(32)], SmtSort::BitVec(64));
        assert_eq!(
            format!("{}", decl),
            "(declare-fun hash ((_ BitVec 32)) (_ BitVec 64))"
        );
    }

    #[test]
    fn test_uf_sort() {
        let uf = SmtExpr::uf("f", vec![], SmtSort::BitVec(32));
        assert_eq!(uf.sort(), SmtSort::BitVec(32));
    }

    #[test]
    fn test_uf_eval_errors() {
        let uf = SmtExpr::uf("f", vec![], SmtSort::BitVec(32));
        assert!(uf.try_eval(&HashMap::new()).is_err());
    }

    #[test]
    fn test_rounding_mode_display() {
        assert_eq!(format!("{}", RoundingMode::RNE), "RNE");
        assert_eq!(format!("{}", RoundingMode::RNA), "RNA");
        assert_eq!(format!("{}", RoundingMode::RTP), "RTP");
        assert_eq!(format!("{}", RoundingMode::RTN), "RTN");
        assert_eq!(format!("{}", RoundingMode::RTZ), "RTZ");
    }

    #[test]
    fn test_free_vars_with_new_exprs() {
        // Array expression references no free vars if built from constants.
        let arr = SmtExpr::const_array(SmtSort::BitVec(8), SmtExpr::bv_const(0, 32));
        let sel = SmtExpr::select(arr, SmtExpr::var("idx", 8));
        assert_eq!(sel.free_vars(), vec!["idx".to_string()]);

        // FP expression
        let fp_expr = SmtExpr::fp_add(
            RoundingMode::RNE,
            SmtExpr::fp64_const(1.0),
            SmtExpr::fp64_const(2.0),
        );
        assert!(fp_expr.free_vars().is_empty());

        // UF with args
        let uf = SmtExpr::uf("f", vec![SmtExpr::var("x", 32)], SmtSort::BitVec(32));
        assert_eq!(uf.free_vars(), vec!["x".to_string()]);
    }

    // -----------------------------------------------------------------------
    // ConstArray index sort validation tests (#167)
    // -----------------------------------------------------------------------

    #[test]
    fn test_const_array_bv_index_sort_ok() {
        // Valid: BitVec index sort should succeed.
        let result = SmtExpr::try_const_array(SmtSort::BitVec(32), SmtExpr::bv_const(0, 64));
        assert!(result.is_ok());
        let arr = result.unwrap();
        assert_eq!(
            arr.sort(),
            SmtSort::Array(Box::new(SmtSort::BitVec(32)), Box::new(SmtSort::BitVec(64)))
        );
    }

    #[test]
    fn test_const_array_bool_index_sort_rejected() {
        // Invalid: Bool index sort should fail.
        let result = SmtExpr::try_const_array(SmtSort::Bool, SmtExpr::bv_const(0, 32));
        assert!(result.is_err());
        match result.unwrap_err() {
            SmtError::InvalidArrayIndexSort(msg) => {
                assert!(
                    msg.contains("Bool"),
                    "error should mention Bool sort: {}",
                    msg
                );
            }
            other => panic!("expected InvalidArrayIndexSort, got: {:?}", other),
        }
    }

    #[test]
    fn test_const_array_array_index_sort_rejected() {
        // Invalid: Array index sort should fail.
        let nested_sort =
            SmtSort::Array(Box::new(SmtSort::BitVec(8)), Box::new(SmtSort::BitVec(8)));
        let result = SmtExpr::try_const_array(nested_sort, SmtExpr::bv_const(0, 32));
        assert!(result.is_err());
        match result.unwrap_err() {
            SmtError::InvalidArrayIndexSort(msg) => {
                assert!(
                    msg.contains("Array"),
                    "error should mention Array sort: {}",
                    msg
                );
            }
            other => panic!("expected InvalidArrayIndexSort, got: {:?}", other),
        }
    }

    #[test]
    fn test_const_array_fp_index_sort_rejected() {
        // Invalid: FloatingPoint index sort should fail.
        let result = SmtExpr::try_const_array(SmtSort::fp32(), SmtExpr::bv_const(0, 32));
        assert!(result.is_err());
        match result.unwrap_err() {
            SmtError::InvalidArrayIndexSort(msg) => {
                assert!(
                    msg.contains("FloatingPoint"),
                    "error should mention FP sort: {}",
                    msg
                );
            }
            other => panic!("expected InvalidArrayIndexSort, got: {:?}", other),
        }
    }

    #[test]
    #[should_panic(expected = "index_sort must be BitVec")]
    fn test_const_array_panics_on_bool_index() {
        // The non-try version should panic.
        let _ = SmtExpr::const_array(SmtSort::Bool, SmtExpr::bv_const(0, 32));
    }

    // -----------------------------------------------------------------------
    // Select/Store sort validation tests (#167)
    // -----------------------------------------------------------------------

    #[test]
    fn test_select_on_array_ok() {
        // Valid: selecting from a ConstArray.
        let arr = SmtExpr::const_array(SmtSort::BitVec(8), SmtExpr::bv_const(42, 32));
        let result = SmtExpr::try_select(arr, SmtExpr::bv_const(0, 8));
        assert!(result.is_ok());
    }

    #[test]
    fn test_store_on_array_ok() {
        // Valid: storing to a ConstArray.
        let arr = SmtExpr::const_array(SmtSort::BitVec(8), SmtExpr::bv_const(0, 32));
        let result = SmtExpr::try_store(arr, SmtExpr::bv_const(1, 8), SmtExpr::bv_const(99, 32));
        assert!(result.is_ok());
    }

    #[test]
    fn test_select_on_non_array_rejected() {
        // Invalid: selecting from a BvConst should fail.
        let result = SmtExpr::try_select(SmtExpr::bv_const(0, 32), SmtExpr::bv_const(0, 8));
        assert!(result.is_err());
        match result.unwrap_err() {
            SmtError::NotAnArraySort(msg) => {
                assert!(msg.contains("BitVec"), "error should mention sort: {}", msg);
            }
            other => panic!("expected NotAnArraySort, got: {:?}", other),
        }
    }

    #[test]
    fn test_store_on_non_array_rejected() {
        // Invalid: storing to a BoolConst should fail.
        let result = SmtExpr::try_store(
            SmtExpr::bool_const(true),
            SmtExpr::bv_const(0, 8),
            SmtExpr::bv_const(42, 32),
        );
        assert!(result.is_err());
        match result.unwrap_err() {
            SmtError::NotAnArraySort(msg) => {
                assert!(msg.contains("Bool"), "error should mention sort: {}", msg);
            }
            other => panic!("expected NotAnArraySort, got: {:?}", other),
        }
    }

    #[test]
    #[should_panic(expected = "must have Array sort")]
    fn test_select_panics_on_non_array() {
        let _ = SmtExpr::select(SmtExpr::bv_const(0, 32), SmtExpr::bv_const(0, 8));
    }

    #[test]
    #[should_panic(expected = "must have Array sort")]
    fn test_store_panics_on_non_array() {
        let _ = SmtExpr::store(
            SmtExpr::bv_const(0, 32),
            SmtExpr::bv_const(0, 8),
            SmtExpr::bv_const(42, 32),
        );
    }

    #[test]
    fn test_select_on_var_allowed() {
        // Var sort can't be statically determined as Array, but we defer
        // validation to eval time for flexibility.
        let result = SmtExpr::try_select(SmtExpr::var("mem", 64), SmtExpr::bv_const(0, 8));
        assert!(result.is_ok());
    }

    #[test]
    fn test_store_then_select_well_typed() {
        // Full roundtrip: const_array -> store -> select with matching types.
        let arr = SmtExpr::const_array(SmtSort::BitVec(8), SmtExpr::bv_const(0, 32));
        let arr = SmtExpr::store(arr, SmtExpr::bv_const(7, 8), SmtExpr::bv_const(255, 32));
        let sel = SmtExpr::select(arr, SmtExpr::bv_const(7, 8));
        let result = sel.try_eval(&HashMap::new()).unwrap();
        assert_eq!(result, EvalResult::Bv(255));
    }

    // -----------------------------------------------------------------------
    // 128-bit shift operation tests (BvShl, BvLshr, BvAshr with width > 64)
    // -----------------------------------------------------------------------

    /// Helper: build a 128-bit BvShl expression from two concatenated 64-bit halves.
    fn make_128bit_shl(hi_val: u64, lo_val: u64, shift: u64) -> EvalResult {
        let hi = SmtExpr::var("hi", 64);
        let lo = SmtExpr::var("lo", 64);
        let vec128 = hi.concat(lo); // 128-bit value
        let shift_amt = SmtExpr::bv_const(shift, 128);
        let expr = SmtExpr::BvShl {
            lhs: Arc::new(vec128),
            rhs: Arc::new(shift_amt),
            width: 128,
        };
        expr.eval(&env(&[("hi", hi_val), ("lo", lo_val)]))
    }

    #[test]
    fn test_bvshl_128bit_basic() {
        // 1 << 64 should set bit 64
        let result = make_128bit_shl(0, 1, 64);
        assert_eq!(result, EvalResult::Bv128(1u128 << 64));
    }

    #[test]
    fn test_bvshl_128bit_shift_by_zero() {
        // Shift by 0 = identity
        let result = make_128bit_shl(0xDEAD, 0xBEEF, 0);
        let expected = (0xDEADu128 << 64) | 0xBEEFu128;
        assert_eq!(result, EvalResult::Bv128(expected));
    }

    #[test]
    fn test_bvshl_128bit_shift_by_width_minus_1() {
        // 1 << 127 should produce the sign bit
        let result = make_128bit_shl(0, 1, 127);
        assert_eq!(result, EvalResult::Bv128(1u128 << 127));
    }

    #[test]
    fn test_bvshl_128bit_shift_by_width() {
        // Shift by >= width produces 0
        let result = make_128bit_shl(0xFFFF_FFFF_FFFF_FFFF, 0xFFFF_FFFF_FFFF_FFFF, 128);
        assert_eq!(result, EvalResult::Bv128(0));
    }

    #[test]
    fn test_bvshl_128bit_shift_exceeds_width() {
        // Shift by > width produces 0
        let result = make_128bit_shl(0xFFFF_FFFF_FFFF_FFFF, 0xFFFF_FFFF_FFFF_FFFF, 200);
        assert_eq!(result, EvalResult::Bv128(0));
    }

    /// Helper: build a 128-bit BvLshr expression.
    fn make_128bit_lshr(hi_val: u64, lo_val: u64, shift: u64) -> EvalResult {
        let hi = SmtExpr::var("hi", 64);
        let lo = SmtExpr::var("lo", 64);
        let vec128 = hi.concat(lo);
        let shift_amt = SmtExpr::bv_const(shift, 128);
        let expr = SmtExpr::BvLshr {
            lhs: Arc::new(vec128),
            rhs: Arc::new(shift_amt),
            width: 128,
        };
        expr.eval(&env(&[("hi", hi_val), ("lo", lo_val)]))
    }

    #[test]
    fn test_bvlshr_128bit_basic() {
        // (1 << 64) >> 64 = 1
        let result = make_128bit_lshr(1, 0, 64);
        assert_eq!(result, EvalResult::Bv128(1));
    }

    #[test]
    fn test_bvlshr_128bit_shift_by_zero() {
        let result = make_128bit_lshr(0xDEAD, 0xBEEF, 0);
        let expected = (0xDEADu128 << 64) | 0xBEEFu128;
        assert_eq!(result, EvalResult::Bv128(expected));
    }

    #[test]
    fn test_bvlshr_128bit_shift_by_width_minus_1() {
        // All 1s >> 127 = 1 (only the top bit survives)
        let result = make_128bit_lshr(u64::MAX, u64::MAX, 127);
        assert_eq!(result, EvalResult::Bv128(1));
    }

    #[test]
    fn test_bvlshr_128bit_shift_by_width() {
        let result = make_128bit_lshr(u64::MAX, u64::MAX, 128);
        assert_eq!(result, EvalResult::Bv128(0));
    }

    /// Helper: build a 128-bit BvAshr expression.
    fn make_128bit_ashr(hi_val: u64, lo_val: u64, shift: u64) -> EvalResult {
        let hi = SmtExpr::var("hi", 64);
        let lo = SmtExpr::var("lo", 64);
        let vec128 = hi.concat(lo);
        let shift_amt = SmtExpr::bv_const(shift, 128);
        let expr = SmtExpr::BvAshr {
            lhs: Arc::new(vec128),
            rhs: Arc::new(shift_amt),
            width: 128,
        };
        expr.eval(&env(&[("hi", hi_val), ("lo", lo_val)]))
    }

    #[test]
    fn test_bvashr_128bit_positive() {
        // Positive value (MSB = 0): same as logical shift right
        let result = make_128bit_ashr(0x7FFF_FFFF_FFFF_FFFF, 0, 64);
        // 0x7FFFFFFFFFFFFFFF_0000000000000000 >> 64 = 0x7FFFFFFFFFFFFFFF
        assert_eq!(result, EvalResult::Bv128(0x7FFF_FFFF_FFFF_FFFF));
    }

    #[test]
    fn test_bvashr_128bit_negative() {
        // Negative value (MSB = 1): sign-extends with 1s
        // All 1s >> 1 should stay all 1s (arithmetic)
        let result = make_128bit_ashr(u64::MAX, u64::MAX, 1);
        assert_eq!(result, EvalResult::Bv128(u128::MAX)); // all 1s
    }

    #[test]
    fn test_bvashr_128bit_negative_shift_by_width() {
        // Negative >> width = all 1s (sign fill)
        let result = make_128bit_ashr(0x8000_0000_0000_0000, 0, 128);
        assert_eq!(result, EvalResult::Bv128(u128::MAX));
    }

    #[test]
    fn test_bvashr_128bit_positive_shift_by_width() {
        // Positive >> width = 0
        let result = make_128bit_ashr(0x7FFF_FFFF_FFFF_FFFF, u64::MAX, 128);
        assert_eq!(result, EvalResult::Bv128(0));
    }

    #[test]
    fn test_bvashr_128bit_shift_by_zero() {
        let result = make_128bit_ashr(0xDEAD, 0xBEEF, 0);
        let expected = (0xDEADu128 << 64) | 0xBEEFu128;
        assert_eq!(result, EvalResult::Bv128(expected));
    }

    #[test]
    fn test_bvshl_128bit_mixed_operands() {
        // One operand from Concat (Bv128), shift amount from BvConst (Bv).
        // This tests the as_u128() promotion on Bv values.
        let hi = SmtExpr::bv_const(0, 64);
        let lo = SmtExpr::bv_const(0xFF, 64);
        let vec128 = hi.concat(lo); // Bv128
        // Shift amount is a plain 128-bit const (internally Bv since value fits u64)
        let shift = SmtExpr::bv_const(8, 128);
        let expr = SmtExpr::BvShl {
            lhs: Arc::new(vec128),
            rhs: Arc::new(shift),
            width: 128,
        };
        let result = expr.eval(&env(&[]));
        assert_eq!(result, EvalResult::Bv128(0xFF00));
    }

    #[test]
    fn test_bvlshr_128bit_mixed_operands() {
        let hi = SmtExpr::bv_const(0, 64);
        let lo = SmtExpr::bv_const(0xFF00, 64);
        let vec128 = hi.concat(lo);
        let shift = SmtExpr::bv_const(8, 128);
        let expr = SmtExpr::BvLshr {
            lhs: Arc::new(vec128),
            rhs: Arc::new(shift),
            width: 128,
        };
        let result = expr.eval(&env(&[]));
        assert_eq!(result, EvalResult::Bv128(0xFF));
    }

    #[test]
    fn test_bvashr_128bit_mixed_operands() {
        // Negative 128-bit value with sign bit set, shift from BvConst
        let hi = SmtExpr::bv_const(0x8000_0000_0000_0000, 64);
        let lo = SmtExpr::bv_const(0, 64);
        let vec128 = hi.concat(lo); // MSB set = negative
        let shift = SmtExpr::bv_const(64, 128);
        let expr = SmtExpr::BvAshr {
            lhs: Arc::new(vec128),
            rhs: Arc::new(shift),
            width: 128,
        };
        let result = expr.eval(&env(&[]));
        // Arithmetic shift right of a negative value:
        // 0x80000000_00000000_00000000_00000000 (i128::MIN) >> 64 (arithmetic)
        // = 0xFFFFFFFF_FFFFFFFF_80000000_00000000
        // The upper 64 bits fill with 1s (sign extension), the original MSB
        // (0x80000000_00000000) moves to the lower 64 bits.
        let expected: u128 = 0xFFFF_FFFF_FFFF_FFFF_8000_0000_0000_0000;
        assert_eq!(result, EvalResult::Bv128(expected));
    }

    #[test]
    fn test_bvadd_65bit_preserves_carry() {
        let max = SmtExpr::bv_const(u64::MAX, 64).zero_ext(1);
        let one = SmtExpr::bv_const(1, 64).zero_ext(1);
        let result = max.bvadd(one).eval(&env(&[]));
        assert_eq!(result, EvalResult::Bv128(1u128 << 64));
    }

    #[test]
    fn test_sign_extend_64_to_128_preserves_negative_bits() {
        let neg_one = SmtExpr::bv_const(u64::MAX, 64).sign_ext(64);
        let result = neg_one.eval(&env(&[]));
        assert_eq!(result, EvalResult::Bv128(u128::MAX));
    }

    #[test]
    fn test_bvmul_128bit_preserves_high_half() {
        let lhs = SmtExpr::bv_const(u64::MAX, 64).zero_ext(64);
        let rhs = SmtExpr::bv_const(2, 64).zero_ext(64);
        let product = lhs.bvmul(rhs);
        let high = product.extract(127, 64);
        let result = high.eval(&env(&[]));
        assert_eq!(result, EvalResult::Bv(1));
    }

    #[test]
    fn test_sign_extend128_helper() {
        // -1 in 8 bits = 0xFF
        assert_eq!(sign_extend128(0xFF, 8), -1i128);
        // -128 in 8 bits = 0x80
        assert_eq!(sign_extend128(0x80, 8), -128i128);
        // Positive: 0x7F in 8 bits = 127
        assert_eq!(sign_extend128(0x7F, 8), 127i128);
        // Full width: passthrough
        assert_eq!(sign_extend128(u128::MAX, 128), -1i128);
        // Zero width
        assert_eq!(sign_extend128(0xFF, 0), 0i128);
    }

    // -----------------------------------------------------------------------
    // QF_FP extended operations tests (#123)
    // -----------------------------------------------------------------------

    #[test]
    fn test_fp_sqrt() {
        let a = SmtExpr::fp64_const(9.0);
        let expr = SmtExpr::fp_sqrt(RoundingMode::RNE, a);
        let result = expr.try_eval(&HashMap::new()).unwrap();
        assert_eq!(result, EvalResult::Float(3.0));
    }

    #[test]
    fn test_fp_sqrt_display() {
        let expr = SmtExpr::fp_sqrt(RoundingMode::RTZ, SmtExpr::fp64_const(4.0));
        assert_eq!(format!("{}", expr).split_once(' ').unwrap().0, "(fp.sqrt");
    }

    #[test]
    fn test_fp_abs_positive() {
        let a = SmtExpr::fp64_const(3.5);
        let expr = a.fp_abs();
        let result = expr.try_eval(&HashMap::new()).unwrap();
        assert_eq!(result, EvalResult::Float(3.5));
    }

    #[test]
    fn test_fp_abs_negative() {
        let a = SmtExpr::fp64_const(-7.25);
        let expr = a.fp_abs();
        let result = expr.try_eval(&HashMap::new()).unwrap();
        assert_eq!(result, EvalResult::Float(7.25));
    }

    #[test]
    fn test_fp_abs_display() {
        let expr = SmtExpr::fp64_const(-1.0).fp_abs();
        assert!(format!("{}", expr).starts_with("(fp.abs"));
    }

    #[test]
    fn test_fp_fma() {
        // fma(2.0, 3.0, 4.0) = 2.0 * 3.0 + 4.0 = 10.0
        let expr = SmtExpr::fp_fma(
            RoundingMode::RNE,
            SmtExpr::fp64_const(2.0),
            SmtExpr::fp64_const(3.0),
            SmtExpr::fp64_const(4.0),
        );
        let result = expr.try_eval(&HashMap::new()).unwrap();
        assert_eq!(result, EvalResult::Float(10.0));
    }

    #[test]
    fn test_fp_fma_display() {
        let expr = SmtExpr::fp_fma(
            RoundingMode::RNE,
            SmtExpr::fp64_const(1.0),
            SmtExpr::fp64_const(2.0),
            SmtExpr::fp64_const(3.0),
        );
        assert!(format!("{}", expr).starts_with("(fp.fma RNE"));
    }

    #[test]
    fn test_fp_gt() {
        let a = SmtExpr::fp64_const(3.0);
        let b = SmtExpr::fp64_const(2.0);
        let expr = a.fp_gt(b);
        let result = expr.try_eval(&HashMap::new()).unwrap();
        assert_eq!(result, EvalResult::Bool(true));
    }

    #[test]
    fn test_fp_ge() {
        let a = SmtExpr::fp64_const(2.0);
        let b = SmtExpr::fp64_const(2.0);
        let expr = a.fp_ge(b);
        let result = expr.try_eval(&HashMap::new()).unwrap();
        assert_eq!(result, EvalResult::Bool(true));
    }

    #[test]
    fn test_fp_le() {
        let a = SmtExpr::fp64_const(1.0);
        let b = SmtExpr::fp64_const(2.0);
        let expr = a.fp_le(b);
        let result = expr.try_eval(&HashMap::new()).unwrap();
        assert_eq!(result, EvalResult::Bool(true));
    }

    #[test]
    fn test_fp_comparison_display() {
        let a = SmtExpr::fp64_const(1.0);
        let b = SmtExpr::fp64_const(2.0);
        assert!(format!("{}", a.clone().fp_gt(b.clone())).starts_with("(fp.gt"));
        assert!(format!("{}", a.clone().fp_ge(b.clone())).starts_with("(fp.geq"));
        assert!(format!("{}", a.fp_le(b)).starts_with("(fp.leq"));
    }

    #[test]
    fn test_fp_is_nan() {
        let nan = SmtExpr::fp64_const(f64::NAN);
        let expr = nan.fp_is_nan();
        let result = expr.try_eval(&HashMap::new()).unwrap();
        assert_eq!(result, EvalResult::Bool(true));

        let normal = SmtExpr::fp64_const(1.0);
        let expr2 = normal.fp_is_nan();
        let result2 = expr2.try_eval(&HashMap::new()).unwrap();
        assert_eq!(result2, EvalResult::Bool(false));
    }

    #[test]
    fn test_fp_is_inf() {
        let inf = SmtExpr::fp64_const(f64::INFINITY);
        let expr = inf.fp_is_inf();
        let result = expr.try_eval(&HashMap::new()).unwrap();
        assert_eq!(result, EvalResult::Bool(true));

        let neg_inf = SmtExpr::fp64_const(f64::NEG_INFINITY);
        let expr2 = neg_inf.fp_is_inf();
        let result2 = expr2.try_eval(&HashMap::new()).unwrap();
        assert_eq!(result2, EvalResult::Bool(true));

        let normal = SmtExpr::fp64_const(42.0);
        let expr3 = normal.fp_is_inf();
        let result3 = expr3.try_eval(&HashMap::new()).unwrap();
        assert_eq!(result3, EvalResult::Bool(false));
    }

    #[test]
    fn test_fp_is_zero() {
        let zero = SmtExpr::fp64_const(0.0);
        let expr = zero.fp_is_zero();
        let result = expr.try_eval(&HashMap::new()).unwrap();
        assert_eq!(result, EvalResult::Bool(true));

        let neg_zero = SmtExpr::fp64_const(-0.0);
        let expr2 = neg_zero.fp_is_zero();
        let result2 = expr2.try_eval(&HashMap::new()).unwrap();
        assert_eq!(result2, EvalResult::Bool(true));

        let nonzero = SmtExpr::fp64_const(1.0);
        let expr3 = nonzero.fp_is_zero();
        let result3 = expr3.try_eval(&HashMap::new()).unwrap();
        assert_eq!(result3, EvalResult::Bool(false));
    }

    #[test]
    fn test_fp_is_normal() {
        let normal = SmtExpr::fp64_const(1.0);
        let expr = normal.fp_is_normal();
        let result = expr.try_eval(&HashMap::new()).unwrap();
        assert_eq!(result, EvalResult::Bool(true));

        // Subnormals are not normal
        let subnormal = SmtExpr::fp64_const(5e-324);
        let expr2 = subnormal.fp_is_normal();
        let result2 = expr2.try_eval(&HashMap::new()).unwrap();
        assert_eq!(result2, EvalResult::Bool(false));

        // Zero is not normal
        let zero = SmtExpr::fp64_const(0.0);
        let expr3 = zero.fp_is_normal();
        let result3 = expr3.try_eval(&HashMap::new()).unwrap();
        assert_eq!(result3, EvalResult::Bool(false));
    }

    #[test]
    fn test_fp_predicate_display() {
        let a = SmtExpr::fp64_const(1.0);
        assert!(format!("{}", a.clone().fp_is_nan()).starts_with("(fp.isNaN"));
        assert!(format!("{}", a.clone().fp_is_inf()).starts_with("(fp.isInfinite"));
        assert!(format!("{}", a.clone().fp_is_zero()).starts_with("(fp.isZero"));
        assert!(format!("{}", a.fp_is_normal()).starts_with("(fp.isNormal"));
    }

    #[test]
    fn test_fp_to_sbv() {
        let a = SmtExpr::fp64_const(42.7);
        let expr = SmtExpr::fp_to_sbv(RoundingMode::RTZ, a, 32);
        let result = expr.try_eval(&HashMap::new()).unwrap();
        assert_eq!(result, EvalResult::Bv(42));
    }

    #[test]
    fn test_fp_to_sbv_negative() {
        let a = SmtExpr::fp64_const(-10.9);
        let expr = SmtExpr::fp_to_sbv(RoundingMode::RTZ, a, 32);
        let result = expr.try_eval(&HashMap::new()).unwrap();
        // -10 as u32 = 0xFFFFFFF6
        assert_eq!(result, EvalResult::Bv(mask((-10i64) as u64, 32)));
    }

    #[test]
    fn test_fp_to_ubv() {
        let a = SmtExpr::fp64_const(255.9);
        let expr = SmtExpr::fp_to_ubv(RoundingMode::RTZ, a, 8);
        let result = expr.try_eval(&HashMap::new()).unwrap();
        assert_eq!(result, EvalResult::Bv(255));
    }

    #[test]
    fn test_fp_to_bv_display() {
        let a = SmtExpr::fp64_const(1.0);
        let sbv = SmtExpr::fp_to_sbv(RoundingMode::RTZ, a.clone(), 32);
        assert!(format!("{}", sbv).starts_with("((_ fp.to_sbv 32)"));

        let ubv = SmtExpr::fp_to_ubv(RoundingMode::RNE, a, 64);
        assert!(format!("{}", ubv).starts_with("((_ fp.to_ubv 64)"));
    }

    #[test]
    fn test_bv_to_fp() {
        let bv = SmtExpr::bv_const(42, 32);
        let expr = SmtExpr::bv_to_fp(RoundingMode::RNE, bv, 8, 24);
        let result = expr.try_eval(&HashMap::new()).unwrap();
        assert_eq!(result, EvalResult::Float(42.0f32 as f64));
    }

    #[test]
    fn test_bv_to_fp_negative() {
        // -1 in 8 bits = 0xFF
        let bv = SmtExpr::bv_const(0xFF, 8);
        let expr = SmtExpr::bv_to_fp(RoundingMode::RNE, bv, 11, 53);
        let result = expr.try_eval(&HashMap::new()).unwrap();
        assert_eq!(result, EvalResult::Float(-1.0));
    }

    #[test]
    fn test_fp16_const_decodes_canonical_bits() {
        let expr = SmtExpr::fp_const(0x3c00, 5, 11);
        let result = expr.try_eval(&HashMap::new()).unwrap();
        assert_eq!(result, EvalResult::Float(1.0));
    }

    #[test]
    fn test_fp16_const_decodes_f64_bit_encoding() {
        let expr = SmtExpr::fp_const(1.5f64.to_bits(), 5, 11);
        let result = expr.try_eval(&HashMap::new()).unwrap();
        assert_eq!(result, EvalResult::Float(1.5));
    }

    #[test]
    fn test_bv_to_fp_fp16_rounds_past_exact_boundary() {
        let bv = SmtExpr::bv_const(2049, 16);
        let expr = SmtExpr::bv_to_fp(RoundingMode::RNE, bv, 5, 11);
        let result = expr.try_eval(&HashMap::new()).unwrap();
        assert_eq!(result, EvalResult::Float(2048.0));
    }

    #[test]
    fn test_fp16_add_rounds_to_fp16_precision() {
        let one = SmtExpr::fp_const(1.0f64.to_bits(), 5, 11);
        let half_ulp = SmtExpr::fp_const((2f64.powi(-11)).to_bits(), 5, 11);
        let expr = SmtExpr::fp_add(RoundingMode::RNE, one, half_ulp);
        let result = expr.try_eval(&HashMap::new()).unwrap();
        assert_eq!(result, EvalResult::Float(1.0));
    }

    #[test]
    fn test_bv_to_fp_display() {
        let bv = SmtExpr::bv_const(42, 32);
        let expr = SmtExpr::bv_to_fp(RoundingMode::RNE, bv, 8, 24);
        assert!(format!("{}", expr).starts_with("((_ to_fp 8 24)"));
    }

    #[test]
    fn test_fp_to_fp_downcast() {
        // FP64 -> FP32 (lossy conversion)
        let a = SmtExpr::fp64_const(1.5);
        let expr = SmtExpr::fp_to_fp(RoundingMode::RNE, a, 8, 24);
        let result = expr.try_eval(&HashMap::new()).unwrap();
        assert_eq!(result, EvalResult::Float(1.5f32 as f64));
    }

    #[test]
    fn test_fp_to_fp_display() {
        let a = SmtExpr::fp64_const(1.0);
        let expr = SmtExpr::fp_to_fp(RoundingMode::RTZ, a, 5, 11);
        assert!(format!("{}", expr).starts_with("((_ to_fp 5 11)"));
    }

    #[test]
    fn test_fp_sort_new_variants() {
        // FPSqrt returns same FP sort as operand
        let sqrt = SmtExpr::fp_sqrt(RoundingMode::RNE, SmtExpr::fp32_const(4.0));
        assert_eq!(sqrt.sort(), SmtSort::FloatingPoint(8, 24));

        // FPAbs returns same FP sort as operand
        let abs = SmtExpr::fp64_const(-1.0).fp_abs();
        assert_eq!(abs.sort(), SmtSort::FloatingPoint(11, 53));

        // FPFma returns same FP sort as first operand
        let fma = SmtExpr::fp_fma(
            RoundingMode::RNE,
            SmtExpr::fp32_const(1.0),
            SmtExpr::fp32_const(2.0),
            SmtExpr::fp32_const(3.0),
        );
        assert_eq!(fma.sort(), SmtSort::FloatingPoint(8, 24));

        // FP predicates return Bool
        assert_eq!(SmtExpr::fp64_const(1.0).fp_is_nan().sort(), SmtSort::Bool);
        assert_eq!(SmtExpr::fp64_const(1.0).fp_is_inf().sort(), SmtSort::Bool);
        assert_eq!(SmtExpr::fp64_const(1.0).fp_is_zero().sort(), SmtSort::Bool);
        assert_eq!(
            SmtExpr::fp64_const(1.0).fp_is_normal().sort(),
            SmtSort::Bool
        );
        assert_eq!(
            SmtExpr::fp64_const(1.0)
                .fp_gt(SmtExpr::fp64_const(2.0))
                .sort(),
            SmtSort::Bool
        );
        assert_eq!(
            SmtExpr::fp64_const(1.0)
                .fp_ge(SmtExpr::fp64_const(2.0))
                .sort(),
            SmtSort::Bool
        );
        assert_eq!(
            SmtExpr::fp64_const(1.0)
                .fp_le(SmtExpr::fp64_const(2.0))
                .sort(),
            SmtSort::Bool
        );

        // FP-to-BV conversions return BitVec
        let to_sbv = SmtExpr::fp_to_sbv(RoundingMode::RTZ, SmtExpr::fp64_const(1.0), 32);
        assert_eq!(to_sbv.sort(), SmtSort::BitVec(32));
        let to_ubv = SmtExpr::fp_to_ubv(RoundingMode::RTZ, SmtExpr::fp64_const(1.0), 64);
        assert_eq!(to_ubv.sort(), SmtSort::BitVec(64));

        // BV-to-FP and FP-to-FP conversions return FloatingPoint
        let bv_to_fp = SmtExpr::bv_to_fp(RoundingMode::RNE, SmtExpr::bv_const(42, 32), 8, 24);
        assert_eq!(bv_to_fp.sort(), SmtSort::FloatingPoint(8, 24));
        let fp_to_fp = SmtExpr::fp_to_fp(RoundingMode::RNE, SmtExpr::fp64_const(1.0), 5, 11);
        assert_eq!(fp_to_fp.sort(), SmtSort::FloatingPoint(5, 11));
    }

    #[test]
    fn test_fp_free_vars_new_variants() {
        // FPFma with vars
        let fma = SmtExpr::fp_fma(
            RoundingMode::RNE,
            SmtExpr::fp64_const(1.0),
            SmtExpr::fp64_const(2.0),
            SmtExpr::fp64_const(3.0),
        );
        assert!(fma.free_vars().is_empty());

        // FPSqrt, FPAbs with constants have no free vars
        let sqrt = SmtExpr::fp_sqrt(RoundingMode::RNE, SmtExpr::fp64_const(4.0));
        assert!(sqrt.free_vars().is_empty());

        let abs = SmtExpr::fp64_const(-1.0).fp_abs();
        assert!(abs.free_vars().is_empty());
    }

    #[test]
    fn test_fp_to_sbv_bv_width() {
        // FPToSBv should have a BV width.
        let expr = SmtExpr::fp_to_sbv(RoundingMode::RTZ, SmtExpr::fp64_const(1.0), 32);
        assert_eq!(expr.try_bv_width().unwrap(), 32);
    }

    #[test]
    fn test_fp_to_ubv_bv_width() {
        let expr = SmtExpr::fp_to_ubv(RoundingMode::RTZ, SmtExpr::fp64_const(1.0), 16);
        assert_eq!(expr.try_bv_width().unwrap(), 16);
    }

    #[test]
    fn test_fp_new_ops_no_bv_width() {
        // FP operations should return BoolHasNoWidth.
        assert!(
            SmtExpr::fp_sqrt(RoundingMode::RNE, SmtExpr::fp64_const(4.0))
                .try_bv_width()
                .is_err()
        );
        assert!(SmtExpr::fp64_const(-1.0).fp_abs().try_bv_width().is_err());
        assert!(SmtExpr::fp64_const(1.0).fp_is_nan().try_bv_width().is_err());
        assert!(
            SmtExpr::bv_to_fp(RoundingMode::RNE, SmtExpr::bv_const(0, 32), 8, 24)
                .try_bv_width()
                .is_err()
        );
    }

    // -----------------------------------------------------------------------
    // Bounded quantifier tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_forall_all_true() {
        // ForAll i in [0, 4): i < 4 (always true in unsigned 8-bit)
        let body = SmtExpr::var("i", 8).bvult(SmtExpr::bv_const(4, 8));
        let expr = SmtExpr::forall(
            "i",
            8,
            SmtExpr::bv_const(0, 8),
            SmtExpr::bv_const(4, 8),
            body,
        );
        let result = expr.try_eval(&HashMap::new()).unwrap();
        assert_eq!(result, EvalResult::Bool(true));
    }

    #[test]
    fn test_forall_one_false() {
        // ForAll i in [0, 4): i < 3 (false when i=3)
        let body = SmtExpr::var("i", 8).bvult(SmtExpr::bv_const(3, 8));
        let expr = SmtExpr::forall(
            "i",
            8,
            SmtExpr::bv_const(0, 8),
            SmtExpr::bv_const(4, 8),
            body,
        );
        let result = expr.try_eval(&HashMap::new()).unwrap();
        assert_eq!(result, EvalResult::Bool(false));
    }

    #[test]
    fn test_forall_empty_range() {
        // ForAll i in [5, 3): body — empty range is vacuously true.
        let body = SmtExpr::bool_const(false);
        let expr = SmtExpr::forall(
            "i",
            8,
            SmtExpr::bv_const(5, 8),
            SmtExpr::bv_const(3, 8),
            body,
        );
        let result = expr.try_eval(&HashMap::new()).unwrap();
        assert_eq!(result, EvalResult::Bool(true));
    }

    #[test]
    fn test_exists_one_true() {
        // Exists i in [0, 4): i == 2 (true for i=2)
        let body = SmtExpr::var("i", 8).eq_expr(SmtExpr::bv_const(2, 8));
        let expr = SmtExpr::exists(
            "i",
            8,
            SmtExpr::bv_const(0, 8),
            SmtExpr::bv_const(4, 8),
            body,
        );
        let result = expr.try_eval(&HashMap::new()).unwrap();
        assert_eq!(result, EvalResult::Bool(true));
    }

    #[test]
    fn test_exists_none_true() {
        // Exists i in [0, 4): i == 10 (false for all i in [0,4))
        let body = SmtExpr::var("i", 8).eq_expr(SmtExpr::bv_const(10, 8));
        let expr = SmtExpr::exists(
            "i",
            8,
            SmtExpr::bv_const(0, 8),
            SmtExpr::bv_const(4, 8),
            body,
        );
        let result = expr.try_eval(&HashMap::new()).unwrap();
        assert_eq!(result, EvalResult::Bool(false));
    }

    #[test]
    fn test_exists_empty_range() {
        // Exists i in [5, 3): body — empty range is vacuously false.
        let body = SmtExpr::bool_const(true);
        let expr = SmtExpr::exists(
            "i",
            8,
            SmtExpr::bv_const(5, 8),
            SmtExpr::bv_const(3, 8),
            body,
        );
        let result = expr.try_eval(&HashMap::new()).unwrap();
        assert_eq!(result, EvalResult::Bool(false));
    }

    #[test]
    fn test_forall_with_array() {
        // ForAll i in [0, 3): select(store(store(store(const(0), 0, 42), 1, 42), 2, 42), i) == 42
        let arr = SmtExpr::const_array(SmtSort::BitVec(8), SmtExpr::bv_const(0, 8));
        let arr = SmtExpr::store(arr, SmtExpr::bv_const(0, 8), SmtExpr::bv_const(42, 8));
        let arr = SmtExpr::store(arr, SmtExpr::bv_const(1, 8), SmtExpr::bv_const(42, 8));
        let arr = SmtExpr::store(arr, SmtExpr::bv_const(2, 8), SmtExpr::bv_const(42, 8));
        let body = SmtExpr::select(arr, SmtExpr::var("i", 8)).eq_expr(SmtExpr::bv_const(42, 8));
        let expr = SmtExpr::forall(
            "i",
            8,
            SmtExpr::bv_const(0, 8),
            SmtExpr::bv_const(3, 8),
            body,
        );
        let result = expr.try_eval(&HashMap::new()).unwrap();
        assert_eq!(result, EvalResult::Bool(true));
    }

    #[test]
    fn test_forall_with_env() {
        // ForAll i in [0, n): select(arr, i) == val
        // Test with external variable n=2
        let arr = SmtExpr::const_array(SmtSort::BitVec(8), SmtExpr::bv_const(0xFF, 8));
        let body = SmtExpr::select(arr, SmtExpr::var("i", 8)).eq_expr(SmtExpr::bv_const(0xFF, 8));
        let expr = SmtExpr::forall("i", 8, SmtExpr::bv_const(0, 8), SmtExpr::var("n", 8), body);
        let result = expr.try_eval(&env(&[("n", 5)])).unwrap();
        assert_eq!(result, EvalResult::Bool(true));
    }

    #[test]
    fn test_forall_range_too_large() {
        let body = SmtExpr::bool_const(true);
        let expr = SmtExpr::forall(
            "i",
            32,
            SmtExpr::bv_const(0, 32),
            SmtExpr::bv_const(1000, 32),
            body,
        );
        let result = expr.try_eval(&HashMap::new());
        assert!(result.is_err());
    }

    #[test]
    fn test_forall_sort_is_bool() {
        let body = SmtExpr::bool_const(true);
        let expr = SmtExpr::forall(
            "i",
            8,
            SmtExpr::bv_const(0, 8),
            SmtExpr::bv_const(1, 8),
            body,
        );
        assert_eq!(expr.sort(), SmtSort::Bool);
    }

    #[test]
    fn test_exists_sort_is_bool() {
        let body = SmtExpr::bool_const(true);
        let expr = SmtExpr::exists(
            "i",
            8,
            SmtExpr::bv_const(0, 8),
            SmtExpr::bv_const(1, 8),
            body,
        );
        assert_eq!(expr.sort(), SmtSort::Bool);
    }

    #[test]
    fn test_forall_free_vars() {
        // ForAll i in [0, n): body(i, x)
        // Free vars: n, x (not i)
        let body = SmtExpr::var("i", 8)
            .bvadd(SmtExpr::var("x", 8))
            .eq_expr(SmtExpr::bv_const(0, 8));
        let expr = SmtExpr::forall("i", 8, SmtExpr::bv_const(0, 8), SmtExpr::var("n", 8), body);
        let vars = expr.free_vars();
        assert!(vars.contains(&"n".to_string()));
        assert!(vars.contains(&"x".to_string()));
        assert!(!vars.contains(&"i".to_string()));
    }

    #[test]
    fn test_forall_display() {
        let body = SmtExpr::var("i", 32).bvult(SmtExpr::var("n", 32));
        let expr = SmtExpr::forall(
            "i",
            32,
            SmtExpr::bv_const(0, 32),
            SmtExpr::bv_const(10, 32),
            body,
        );
        let s = format!("{}", expr);
        assert!(s.contains("forall"));
        assert!(s.contains("(_ BitVec 32)"));
        assert!(s.contains("bvuge"));
        assert!(s.contains("bvult"));
    }

    #[test]
    fn test_exists_display() {
        let body = SmtExpr::var("i", 8).eq_expr(SmtExpr::bv_const(5, 8));
        let expr = SmtExpr::exists(
            "i",
            8,
            SmtExpr::bv_const(0, 8),
            SmtExpr::bv_const(10, 8),
            body,
        );
        let s = format!("{}", expr);
        assert!(s.contains("exists"));
        assert!(s.contains("(_ BitVec 8)"));
        assert!(s.contains("bvuge"));
        assert!(s.contains("bvult"));
    }

    // -----------------------------------------------------------------------
    // NaN-aware equality (#388)
    // -----------------------------------------------------------------------

    #[test]
    fn test_semantically_equal_nan_vs_nan() {
        let a = EvalResult::Float(f64::NAN);
        let b = EvalResult::Float(f64::NAN);
        // IEEE-754: NaN != NaN. PartialEq reflects that and reports not-equal.
        assert!(!(a == b));
        // Semantic equality: both NaN = equal for verification purposes.
        assert!(a.semantically_equal(&b));
    }

    #[test]
    fn test_semantically_equal_distinct_nan_payloads() {
        // f64::NAN and a custom NaN bit pattern are both NaN and must compare equal.
        let a = EvalResult::Float(f64::NAN);
        let b = EvalResult::Float(f64::from_bits(0x7ff0_0000_0000_0001));
        assert!(b.as_f64().is_nan());
        assert!(a.semantically_equal(&b));
        assert!(b.semantically_equal(&a));
    }

    #[test]
    fn test_semantically_equal_nan_vs_finite() {
        let nan = EvalResult::Float(f64::NAN);
        let zero = EvalResult::Float(0.0);
        let one = EvalResult::Float(1.0);
        assert!(!nan.semantically_equal(&zero));
        assert!(!zero.semantically_equal(&nan));
        assert!(!nan.semantically_equal(&one));
    }

    #[test]
    fn test_semantically_equal_finite_bit_exact() {
        // Zero sign matters for bit-exact comparison (so +0 != -0, matching
        // AArch64 FMOV bit-pattern semantics).
        let plus_zero = EvalResult::Float(0.0);
        let neg_zero = EvalResult::Float(-0.0);
        assert!(!plus_zero.semantically_equal(&neg_zero));

        // Equal finite values with identical bit pattern.
        let a = EvalResult::Float(3.125);
        let b = EvalResult::Float(3.125);
        assert!(a.semantically_equal(&b));
    }

    #[test]
    fn test_semantically_equal_non_float_unchanged() {
        let a = EvalResult::Bv(42);
        let b = EvalResult::Bv(42);
        let c = EvalResult::Bv(7);
        assert!(a.semantically_equal(&b));
        assert!(!a.semantically_equal(&c));

        let t = EvalResult::Bool(true);
        let f = EvalResult::Bool(false);
        assert!(t.semantically_equal(&EvalResult::Bool(true)));
        assert!(!t.semantically_equal(&f));
    }
}
