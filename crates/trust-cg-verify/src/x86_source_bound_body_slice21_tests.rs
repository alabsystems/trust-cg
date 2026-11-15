// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Slice 21 of the x86-64 source-bound body theorem: floating-point
//! operations as paired rounding events (OD-198), the saturating
//! float-to-integer conversion (OD-199), an abstract theorem's satisfying
//! model as no counterexample (OD-200), and the `I128` atomic load and the
//! atomic exchange (OD-201).
//!
//! Fixtures are real: LIR from the trust-ir adapter (translated with an
//! explicit `Permit`), the machine stream from the real x86-64 instruction
//! selector (`super::select`). Every test here runs without a solver (the
//! `x86_source_bound_body::tests::slice21::` library gate); the replay on AY
//! and Clean is in `slice21_qualification`.
//!
//! The controls are UNIT fixtures, never root replays: several mis-models
//! are invisible in the census roots' own theorems (the design's §5.5: a
//! NaN reaches `false` either way in `already_rounded_value_should_use_
//! exponential`, a quotient of an `i64` by a constant is never NaN, the
//! `Lemire` roots convert under `x <= 2^53`, and `atomic_store` drops the
//! exchange's result).

use super::slice5::describe;
use super::slice6::describe_lir;
use super::slice9::{dag_holds_on_samples, dag_refuted_on_samples};
use super::*;
use trust_cg_ir::X86CondCode;
use trust_ir::{AtomicRMWOp, BinOp, CastOp, FCmpOp, Ordering, Ty};

/// Slice-21 fixture shapes: each a source one of the slice's rules admits.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Shape21 {
    /// `<f64 as Mul>::mul`: `fn(a: f64, b: f64, _: u64) -> f64 { a * b }`
    /// (the root's third, unread parameter included).
    FmulF64,
    /// `<f32 as Mul>::mul`.
    FmulF32,
    /// `<f64 as Div>::div`.
    FdivF64,
    /// `<f32 as Div>::div`.
    FdivF32,
    /// `fn(a: f64, b: f64) -> f64 { a + b }`.
    FaddF64,
    /// `fn(a: f32, b: f32) -> f32 { a - b }`.
    FsubF32,
    /// `fn(a: f64, b: f64) -> f64 { (a * b) / (a + b) }`: three events in
    /// one trace.
    FmaChainF64,
    /// `fn(a: f64, b: f64) -> bool { fcmp <op> a, b }`, every trust-ir
    /// predicate at `f64` (the census roots need `une`, `olt` and `oge`).
    Fcmp64(FCmpOp),
    /// The same at `f32`, for the three the roots need.
    Fcmp32(FCmpOp),
    /// `GeneralFormat<f64>::already_rounded_value_should_use_exponential`:
    /// `fn(p: *const f64) -> bool { let a = abs(*p); if a != 0.0 && a < 1e-4
    /// { true } else { a >= 1e16 } }` (`une`, `olt`, `oge` over a DAG, after
    /// a call).
    ShouldUseExponential64,
    /// The same at `f32`.
    ShouldUseExponential32,
    /// `pow2_to_pow10`: `fn(a: i64) -> i64 { ((a as f64) / LOG2_10) as i64 }`
    /// (`SIToFP`, `FDiv` by a constant, `FPToSISat`).
    Pow2ToPow10,
    /// `fn(x: f64) -> i64 { x as i64 }`: the saturating conversion of a free
    /// `f64` (NaN reaches it).
    F64ToI64,
    /// `fn(x: i64) -> f64 { x as f64 }`.
    I64ToF64,
    /// `fn(x: i64) -> f32 { x as f32 }`.
    I64ToF32,
    /// `Lemire<f64>::from_u64`: `fn(x: u64) -> f64 { if x <= 2^53 { x as f64 }
    /// else { panic_bounds(x, 53); unreachable } }`.
    U64ToF64Bounded,
    /// `Lemire<f32>::from_u64`: the same at `f32` under `x <= 2^24`.
    U64ToF32Bounded,
    /// `atomic_load::<u128>`'s SeqCst arm: `fn(p: *const u128) -> u128 {
    /// atomic_load(p, SeqCst) }`.
    AtomicLoadU128,
    /// `fn(p: *const i128) -> i128 { atomic_load(p, Relaxed) ^ atomic_load(p,
    /// Acquire) }`: two pseudo rows in one trace.
    AtomicLoadI128Twice,
    /// `fn(p: *mut u64, v: u64) -> u64 { atomic_xchg(p, v, SeqCst) }`.
    AtomicXchgU64,
    /// `fn(p: *mut u32, v: u32) -> u32 { atomic_xchg(p, v, AcqRel) }`.
    AtomicXchgU32,
    /// `atomic_store::<*const T>`'s SeqCst arm: `fn(p: *mut u64, v: u64) {
    /// atomic_xchg(p, v, SeqCst); }`, the exchange's result unused.
    AtomicStoreSeqCst,
}

/// The twelve trust-ir float predicates.
pub(crate) const FCMP_OPS: [FCmpOp; 12] = [
    FCmpOp::OEq,
    FCmpOp::ONe,
    FCmpOp::OLt,
    FCmpOp::OLe,
    FCmpOp::OGt,
    FCmpOp::OGe,
    FCmpOp::UEq,
    FCmpOp::UNe,
    FCmpOp::ULt,
    FCmpOp::ULe,
    FCmpOp::UGt,
    FCmpOp::UGe,
];

/// Every slice-21 fixture shape the owner states.
pub(crate) fn slice_twenty_one() -> Vec<Shape21> {
    use Shape21::*;
    let mut shapes = vec![
        FmulF64,
        FmulF32,
        FdivF64,
        FdivF32,
        FaddF64,
        FsubF32,
        FmaChainF64,
    ];
    shapes.extend(FCMP_OPS.map(Fcmp64));
    shapes.extend([FCmpOp::UNe, FCmpOp::OLt, FCmpOp::OGe].map(Fcmp32));
    shapes.extend([
        ShouldUseExponential64,
        ShouldUseExponential32,
        Pow2ToPow10,
        F64ToI64,
        I64ToF64,
        I64ToF32,
        U64ToF64Bounded,
        U64ToF32Bounded,
        AtomicLoadU128,
        AtomicLoadI128Twice,
        AtomicXchgU64,
        AtomicXchgU32,
        AtomicStoreSeqCst,
    ]);
    shapes
}

/// Variants the slice states but whose theorem the abstraction cannot prove,
/// or that stay outside by name.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Variant21 {
    /// `fn(x: u64) -> f64 { x as f64 }`, unbounded: the selector's correct
    /// round-to-odd halving, whose correctness IS a rounding theorem (the
    /// top bit set): the theorem claims bit 63 clear for its pairing and is
    /// satisfiable, an incompleteness the abstraction states, never a
    /// refutation (OD-200).
    U64ToF64,
    /// `fn(x: f32) -> i64 { x as i64 }`: an `F32` source of the conversion,
    /// outside by name (OD-199).
    F32ToI64,
    /// `fn(x: i32) -> f64 { x as f64 }`: a narrower integer, outside by name.
    I32ToF64,
    /// `fn(x: f64) -> f64 { x.sqrt() }`, outside by name.
    SqrtF64,
    /// `fn(p: *mut u64, v: u64) -> u64 { atomic_add(p, v) }`, outside by name.
    AtomicAddU64,
    /// `fn(p: *mut u128, v: u128) { atomic_store(p, v, Relaxed) }`, outside by
    /// name.
    AtomicStoreU128,
    /// `fn(p: *const u128) -> u128 { *p }`: a plain `I128` load (slice 11),
    /// stated; the source of a pairing control.
    LoadU128,
}

pub(crate) const SLICE_TWENTY_ONE_VARIANTS: [Variant21; 7] = [
    Variant21::U64ToF64,
    Variant21::F32ToI64,
    Variant21::I32ToF64,
    Variant21::SqrtF64,
    Variant21::AtomicAddU64,
    Variant21::AtomicStoreU128,
    Variant21::LoadU128,
];

trait ShapeName: std::fmt::Debug {
    fn name(&self) -> String {
        let name = format!("{self:?}");
        let mut snake = String::from("s21_");
        let mut previous_lower = false;
        for c in name.chars() {
            if c.is_ascii_alphanumeric() {
                if c.is_ascii_uppercase() && previous_lower {
                    snake.push('_');
                }
                previous_lower = c.is_ascii_lowercase() || c.is_ascii_digit();
                snake.push(c.to_ascii_lowercase());
            } else if !snake.ends_with('_') {
                snake.push('_');
                previous_lower = false;
            }
        }
        snake.trim_end_matches('_').to_owned()
    }
}
impl ShapeName for Shape21 {}
impl ShapeName for Variant21 {}

type V = trust_ir::value::ValueId;

/// `log2(10)`, the constant `pow2_to_pow10` divides by.
const LOG2_10: f64 = std::f64::consts::LOG2_10;

fn slice21_function(name: String, shape: Option<Shape21>, variant: Option<Variant21>) -> Function {
    use Shape21::*;
    use Variant21::*;
    let mut builder = ModuleBuilder::new("x86_source_bound_body_slice21");
    let ptr = |ty: Ty| Ty::PtrMut(Box::new(ty));
    let mut declare = |name: &str, params: Vec<Ty>, results: Vec<Ty>| {
        let ty = builder.add_func_type(params, results);
        builder.declare_function(name, ty)
    };
    let fabs64 = declare("fabs64", vec![Ty::F64], vec![Ty::F64]);
    let fabs32 = declare("fabs32", vec![Ty::F32], vec![Ty::F32]);
    let panic = declare("panic_bounds", vec![Ty::U64, Ty::U64], vec![]);
    let (params, results): (Vec<Ty>, Vec<Ty>) = match (shape, variant) {
        (Some(FmulF64), _) => (vec![Ty::F64, Ty::F64, Ty::U64], vec![Ty::F64]),
        (Some(FdivF64 | FaddF64 | FmaChainF64), _) => (vec![Ty::F64, Ty::F64], vec![Ty::F64]),
        (Some(FmulF32 | FdivF32 | FsubF32), _) => (vec![Ty::F32, Ty::F32], vec![Ty::F32]),
        (Some(Fcmp64(_)), _) => (vec![Ty::F64, Ty::F64], vec![Ty::Bool]),
        (Some(Fcmp32(_)), _) => (vec![Ty::F32, Ty::F32], vec![Ty::Bool]),
        (Some(ShouldUseExponential64), _) => (vec![ptr(Ty::F64)], vec![Ty::Bool]),
        (Some(ShouldUseExponential32), _) => (vec![ptr(Ty::F32)], vec![Ty::Bool]),
        (Some(Pow2ToPow10), _) => (vec![Ty::I64], vec![Ty::I64]),
        (Some(F64ToI64), _) => (vec![Ty::F64], vec![Ty::I64]),
        (Some(I64ToF64), _) => (vec![Ty::I64], vec![Ty::F64]),
        (Some(I64ToF32), _) => (vec![Ty::I64], vec![Ty::F32]),
        (Some(U64ToF64Bounded), _) | (_, Some(U64ToF64)) => (vec![Ty::U64], vec![Ty::F64]),
        (Some(U64ToF32Bounded), _) => (vec![Ty::U64], vec![Ty::F32]),
        (Some(AtomicLoadU128), _) | (_, Some(LoadU128)) => (vec![ptr(Ty::U128)], vec![Ty::U128]),
        (Some(AtomicLoadI128Twice), _) => (vec![ptr(Ty::I128)], vec![Ty::I128]),
        (Some(AtomicXchgU64), _) | (_, Some(AtomicAddU64)) => {
            (vec![ptr(Ty::U64), Ty::U64], vec![Ty::U64])
        }
        (Some(AtomicXchgU32), _) => (vec![ptr(Ty::U32), Ty::U32], vec![Ty::U32]),
        (Some(AtomicStoreSeqCst), _) => (vec![ptr(Ty::U64), Ty::U64], vec![]),
        (_, Some(F32ToI64)) => (vec![Ty::F32], vec![Ty::I64]),
        (_, Some(I32ToF64)) => (vec![Ty::I32], vec![Ty::F64]),
        (_, Some(SqrtF64)) => (vec![Ty::F64], vec![Ty::F64]),
        (_, Some(AtomicStoreU128)) => (vec![ptr(Ty::U128), Ty::U128], vec![]),
        other => unreachable!("{other:?}"),
    };
    let signature = builder.add_func_type(params.clone(), results);
    let mut f = builder.function(name.clone(), signature);
    // The `I128` atomics need the function's `cmpxchg16b` claim (the
    // adapter refuses them otherwise: the x86-64 baseline lacks CX16).
    if matches!(shape, Some(AtomicLoadU128 | AtomicLoadI128Twice))
        || variant == Some(AtomicStoreU128)
    {
        f.set_attrs(trust_ir::FuncAttrs {
            target_features: vec!["cmpxchg16b".to_owned()],
            ..trust_ir::FuncAttrs::default()
        });
    }
    let entry = f.create_block();
    let args: Vec<V> = params
        .iter()
        .map(|ty| f.add_block_param(entry, ty.clone()))
        .collect();
    f.switch_to_block(entry);
    match (shape, variant) {
        (Some(FmulF64), _) => {
            let product = f.fmul(Ty::F64, args[0], args[1]);
            f.ret(vec![product]);
        }
        (Some(FmulF32), _) => {
            let product = f.fmul(Ty::F32, args[0], args[1]);
            f.ret(vec![product]);
        }
        (Some(FdivF64), _) => {
            let quotient = f.binop(BinOp::FDiv, Ty::F64, args[0], args[1]);
            f.ret(vec![quotient]);
        }
        (Some(FdivF32), _) => {
            let quotient = f.binop(BinOp::FDiv, Ty::F32, args[0], args[1]);
            f.ret(vec![quotient]);
        }
        (Some(FaddF64), _) => {
            let sum = f.fadd(Ty::F64, args[0], args[1]);
            f.ret(vec![sum]);
        }
        (Some(FsubF32), _) => {
            let difference = f.binop(BinOp::FSub, Ty::F32, args[0], args[1]);
            f.ret(vec![difference]);
        }
        (Some(FmaChainF64), _) => {
            let product = f.fmul(Ty::F64, args[0], args[1]);
            let sum = f.fadd(Ty::F64, args[0], args[1]);
            let quotient = f.binop(BinOp::FDiv, Ty::F64, product, sum);
            f.ret(vec![quotient]);
        }
        (Some(Fcmp64(op)), _) => {
            let holds = f.fcmp(op, Ty::F64, args[0], args[1]);
            f.ret(vec![holds]);
        }
        (Some(Fcmp32(op)), _) => {
            let holds = f.fcmp(op, Ty::F32, args[0], args[1]);
            f.ret(vec![holds]);
        }
        (Some(ShouldUseExponential64 | ShouldUseExponential32), _) => {
            let (ty, abs, small, large) = if shape == Some(ShouldUseExponential64) {
                (Ty::F64, fabs64, 1e-4, 1e16)
            } else {
                (Ty::F32, fabs32, f64::from(1e-4f32), f64::from(1e16f32))
            };
            let value = f.load(ty.clone(), args[0]);
            let a = f.call(abs, vec![value]);
            let (nonzero, tiny, other, done) = (
                f.create_block(),
                f.create_block(),
                f.create_block(),
                f.create_block(),
            );
            let result = f.add_block_param(done, Ty::Bool);
            let zero = f.fconst(ty.clone(), 0.0);
            let ne = f.fcmp(FCmpOp::UNe, ty.clone(), a, zero);
            f.condbr(ne, nonzero, vec![], other, vec![]);
            f.switch_to_block(nonzero);
            let bound = f.fconst(ty.clone(), small);
            let lt = f.fcmp(FCmpOp::OLt, ty.clone(), a, bound);
            f.condbr(lt, tiny, vec![], other, vec![]);
            f.switch_to_block(tiny);
            let yes = f.bool_const(true);
            f.br(done, vec![yes]);
            f.switch_to_block(other);
            let bound = f.fconst(ty.clone(), large);
            let ge = f.fcmp(FCmpOp::OGe, ty, a, bound);
            f.br(done, vec![ge]);
            f.switch_to_block(done);
            f.ret(vec![result]);
        }
        (Some(Pow2ToPow10), _) => {
            let a = f.cast(CastOp::SIToFP, Ty::I64, Ty::F64, args[0]);
            let log = f.fconst(Ty::F64, LOG2_10);
            let q = f.binop(BinOp::FDiv, Ty::F64, a, log);
            let r = f.cast(CastOp::FPToSISat, Ty::F64, Ty::I64, q);
            f.ret(vec![r]);
        }
        (Some(F64ToI64), _) => {
            let r = f.cast(CastOp::FPToSISat, Ty::F64, Ty::I64, args[0]);
            f.ret(vec![r]);
        }
        (Some(I64ToF64), _) => {
            let r = f.cast(CastOp::SIToFP, Ty::I64, Ty::F64, args[0]);
            f.ret(vec![r]);
        }
        (Some(I64ToF32), _) => {
            let r = f.cast(CastOp::SIToFP, Ty::I64, Ty::F32, args[0]);
            f.ret(vec![r]);
        }
        (Some(U64ToF64Bounded | U64ToF32Bounded), _) => {
            let (ty, bound, digits) = if shape == Some(U64ToF64Bounded) {
                (Ty::F64, 1i128 << 53, 53)
            } else {
                (Ty::F32, 1i128 << 24, 24)
            };
            let (exact, too_big) = (f.create_block(), f.create_block());
            let limit = f.iconst(Ty::U64, bound);
            let fits = f.icmp(trust_ir::ICmpOp::Ule, Ty::U64, args[0], limit);
            f.condbr(fits, exact, vec![], too_big, vec![]);
            f.switch_to_block(exact);
            let r = f.cast(CastOp::UIToFP, Ty::U64, ty, args[0]);
            f.ret(vec![r]);
            f.switch_to_block(too_big);
            let digits = f.iconst(Ty::U64, digits);
            f.call_void(panic, vec![args[0], digits]);
            f.unreachable();
        }
        (_, Some(U64ToF64)) => {
            let r = f.cast(CastOp::UIToFP, Ty::U64, Ty::F64, args[0]);
            f.ret(vec![r]);
        }
        (Some(AtomicLoadU128), _) => {
            let value = f.atomic_load(Ty::U128, args[0], Ordering::SeqCst);
            f.ret(vec![value]);
        }
        (Some(AtomicLoadI128Twice), _) => {
            let first = f.atomic_load(Ty::I128, args[0], Ordering::Relaxed);
            let second = f.atomic_load(Ty::I128, args[0], Ordering::Acquire);
            let both = f.binop(BinOp::Xor, Ty::I128, first, second);
            f.ret(vec![both]);
        }
        (Some(AtomicXchgU64), _) => {
            let old = f.atomic_rmw(
                AtomicRMWOp::Xchg,
                Ty::U64,
                args[0],
                args[1],
                Ordering::SeqCst,
            );
            f.ret(vec![old]);
        }
        (Some(AtomicXchgU32), _) => {
            let old = f.atomic_rmw(
                AtomicRMWOp::Xchg,
                Ty::U32,
                args[0],
                args[1],
                Ordering::AcqRel,
            );
            f.ret(vec![old]);
        }
        (Some(AtomicStoreSeqCst), _) => {
            f.atomic_rmw(
                AtomicRMWOp::Xchg,
                Ty::U64,
                args[0],
                args[1],
                Ordering::SeqCst,
            );
            f.ret(vec![]);
        }
        (_, Some(F32ToI64)) => {
            let r = f.cast(CastOp::FPToSISat, Ty::F32, Ty::I64, args[0]);
            f.ret(vec![r]);
        }
        (_, Some(I32ToF64)) => {
            let r = f.cast(CastOp::SIToFP, Ty::I32, Ty::F64, args[0]);
            f.ret(vec![r]);
        }
        (_, Some(SqrtF64)) => {
            let r = f.unop(trust_ir::UnOp::FSqrt, Ty::F64, args[0]);
            f.ret(vec![r]);
        }
        (_, Some(AtomicAddU64)) => {
            let old = f.atomic_rmw(
                AtomicRMWOp::Add,
                Ty::U64,
                args[0],
                args[1],
                Ordering::SeqCst,
            );
            f.ret(vec![old]);
        }
        (_, Some(AtomicStoreU128)) => {
            f.atomic_store(Ty::U128, args[0], args[1], Ordering::Relaxed);
            f.ret(vec![]);
        }
        (_, Some(LoadU128)) => {
            let value = f.load(Ty::U128, args[0]);
            f.ret(vec![value]);
        }
        other => unreachable!("{other:?}"),
    }
    f.build();
    let module = builder.build().expect("ModuleBuilder::build: test fixture");
    trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        &module,
        trust_cg_lower::GuardCarrierArch::X86_64,
        trust_cg_lower::TlsDialect::default(),
        &crate::license_test_support::permit_unlicensed(),
    )
    .unwrap_or_else(|error| panic!("{name}: fixture translates: {error:?}"))
    .into_iter()
    .map(|(function, _)| function)
    .find(|function| function.name == name)
    .unwrap_or_else(|| panic!("{name}: no translated function"))
}

pub(crate) fn slice21_lir(shape: Shape21) -> Function {
    slice21_function(shape.name(), Some(shape), None)
}

pub(crate) fn slice21_variant(variant: Variant21) -> Function {
    slice21_function(variant.name(), None, Some(variant))
}

pub(crate) fn slice21_pair(shape: Shape21) -> (Function, X86ISelFunction) {
    let source = slice21_lir(shape);
    let machine = select(&source, X86CallAbi::SystemV);
    (source, machine)
}

pub(crate) fn variant_pair(variant: Variant21) -> (Function, X86ISelFunction) {
    let source = slice21_variant(variant);
    let machine = select(&source, X86CallAbi::SystemV);
    (source, machine)
}

#[track_caller]
pub(crate) fn owner<'a>(
    what: &str,
    source: &'a Function,
    machine: &'a X86ISelFunction,
) -> SourceBoundX86Body<'a> {
    source_bound_x86_body(source, machine, SYSV).unwrap_or_else(|refusal| {
        panic!(
            "{what}: {refusal}\n{}{}",
            describe_lir(source),
            describe(machine)
        )
    })
}

/// The theorem's query as the replay renders it.
fn text(obligation: &ProofObligation) -> String {
    generate_smt2_query_raw(obligation, &replay_config())
}

/// The walk ordinals of the rows of `opcode`, in walk order.
fn rows_of(machine: &X86ISelFunction, opcode: X86Opcode) -> Vec<usize> {
    find(machine, opcode)
}

/// The theorem evaluated at one assignment of its free inputs (every input
/// `assignment` does not name is 0): whether its two sides agree. The
/// premises are definitional, so this is the theorem's value there.
pub(crate) fn holds_at(obligation: &ProofObligation, assignment: &[(&str, u64)]) -> bool {
    use crate::smt::{EvalEnv, EvalResult};
    let mut env = EvalEnv::default();
    for (name, width) in free_inputs_of(obligation) {
        let value = assignment
            .iter()
            .find(|(known, _)| *known == name)
            .map_or(0, |(_, value)| *value);
        env.insert(name, crate::smt::mask(value, width));
    }
    for premise in obligation.preconditions.iter().rev() {
        let E::Eq { lhs, rhs } = premise else {
            panic!("premise {premise} is not an equation")
        };
        let E::Var { name, .. } = lhs.as_ref() else {
            panic!("premise {premise} defines no name")
        };
        let EvalResult::Bv(value) = rhs.eval(&env) else {
            panic!("definition of {name} is not a bitvector")
        };
        env.insert(name.clone(), value);
    }
    obligation.trust_ir_expr.eval(&env) == obligation.aarch64_expr.eval(&env)
}

/// Every slice-21 shape builds a theorem that holds on slice 9's keyed
/// samples; every rounding shape's theorem is FP-abstract (OD-200), and every
/// compare-only and atomic shape's is not (it is pure bit-vector: a
/// refutation of it is a counterexample).
#[test]
fn owner_builds_every_slice_twenty_one_shape() {
    for shape in slice_twenty_one() {
        let (source, machine) = slice21_pair(shape);
        let owner = owner(&format!("{shape:?}"), &source, &machine);
        assert!(
            dag_holds_on_samples(owner.obligation()),
            "{shape:?}: refuted on samples\n{}{}{}",
            describe_lir(&source),
            describe(&machine),
            text(owner.obligation())
        );
        let rounding = !matches!(
            shape,
            Shape21::Fcmp64(_)
                | Shape21::Fcmp32(_)
                | Shape21::ShouldUseExponential64
                | Shape21::ShouldUseExponential32
                | Shape21::AtomicLoadU128
                | Shape21::AtomicLoadI128Twice
                | Shape21::AtomicXchgU64
                | Shape21::AtomicXchgU32
                | Shape21::AtomicStoreSeqCst
        );
        assert_eq!(owner.is_fp_abstract(), rounding, "{shape:?}");
        // NEVER `=>` (OD-198): AY's proofs of an implication come out
        // incomplete; every implication is spelled `(or (not A) B)`.
        assert!(!text(owner.obligation()).contains("=>"), "{shape:?}");
    }
}

/// Every slice-21 theorem is the same on every build (no hash order leaks).
#[test]
fn slice_twenty_one_theorems_are_deterministic() {
    for shape in slice_twenty_one() {
        let render = || {
            let (source, machine) = slice21_pair(shape);
            text(owner(&format!("{shape:?}"), &source, &machine).obligation())
        };
        assert_eq!(render(), render(), "{shape:?}");
    }
}

/// The variants: the unbounded `u64` conversion is stated and is NOT proved
/// by the abstraction (some sample refutes its abstract theorem: the
/// pairing's claimed bit 63), a plain `I128` load is stated and holds, and
/// every other stays outside by name (refused by the source's admission,
/// before the machine is read: the selector cannot even lower the `I128`
/// atomic store).
#[test]
fn slice_twenty_one_variants_are_stated_or_refused_by_name() {
    for variant in SLICE_TWENTY_ONE_VARIANTS {
        match variant {
            Variant21::U64ToF64 => {
                let (source, machine) = variant_pair(variant);
                let owner = owner(&format!("{variant:?}"), &source, &machine);
                assert!(owner.is_fp_abstract());
                assert!(dag_refuted_on_samples(owner.obligation()), "{variant:?}");
                // It holds wherever bit 63 is clear: the claim that fails is
                // the pairing's, not the conversion's value.
                assert!(holds_at(owner.obligation(), &[("e_rdi", 1 << 52)]));
            }
            Variant21::LoadU128 => {
                let (source, machine) = variant_pair(variant);
                let owner = owner(&format!("{variant:?}"), &source, &machine);
                assert!(!owner.is_fp_abstract());
                assert!(dag_holds_on_samples(owner.obligation()), "{variant:?}");
            }
            _ => {
                let needle = match variant {
                    Variant21::F32ToI64 => "other than an F64 to an I64",
                    Variant21::I32ToF64 => "narrower than I64",
                    Variant21::SqrtF64 => "outside the lane's rounding events",
                    Variant21::AtomicAddU64 => "other than an exchange",
                    Variant21::AtomicStoreU128 => "an i128 store or a float",
                    Variant21::U64ToF64 | Variant21::LoadU128 => unreachable!(),
                };
                let source = slice21_variant(variant);
                match admitted_body(&source) {
                    Err(X86BodyRefusal::Unsupported(reason)) => {
                        let reason = reason.to_string();
                        assert!(reason.contains(needle), "{variant:?}: {reason}");
                    }
                    Err(other) => panic!("{variant:?}: expected Unsupported, got {other}"),
                    Ok(_) => panic!("{variant:?}: an out-of-domain source was admitted"),
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// The controls: wrong lowerings as unit fixtures
// ---------------------------------------------------------------------------

/// What a slice-21 control must end as.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Expect21 {
    /// A pure bit-vector theorem (no FP leaf): refuted, and on the
    /// qualification pair an AY counterexample.
    Refuted,
    /// An FP-abstract theorem (OD-200): refuted on samples, and on the
    /// qualification pair a satisfying model that leaves every covered row
    /// uncredited, never failed and never credited.
    Uncredited,
    /// No theorem: refused by name, with this text in the refusal.
    Refused(&'static str),
}

/// One slice-21 control: a wrong lowering of a fixture's source.
pub(crate) struct Control21 {
    pub(crate) label: &'static str,
    pub(crate) source: Function,
    pub(crate) machine: X86ISelFunction,
    pub(crate) expect: Expect21,
}

/// The walk ordinal of the `k`-th row of `opcode`.
#[track_caller]
fn nth(machine: &X86ISelFunction, opcode: X86Opcode, k: usize) -> usize {
    rows_of(machine, opcode)
        .get(k)
        .copied()
        .unwrap_or_else(|| panic!("no row {k} of {opcode:?}\n{}", describe(machine)))
}

/// Set the condition code of the `k`-th row of `opcode` (a `setcc`, whose
/// operand 1 is the code, or a `cmovcc`, whose operand 2 is).
fn set_condition(machine: &mut X86ISelFunction, opcode: X86Opcode, k: usize, cc: X86CondCode) {
    let row = nth(machine, opcode, k);
    let inst = inst_mut(machine, row);
    let slot = if opcode == X86Opcode::Setcc { 1 } else { 2 };
    assert!(matches!(inst.operands[slot], O::CondCode(_)));
    inst.operands[slot] = O::CondCode(cc);
}

/// Insert `inst` after walk ordinal `row`, stamped as that row is.
fn insert_after(machine: &mut X86ISelFunction, row: usize, mut inst: X86ISelInst) {
    let (_, block, index) = rows(machine)[row];
    let body = &mut machine.blocks.get_mut(&block).unwrap().insts;
    inst.lowering_provenance = body[index].lowering_provenance;
    body.insert(index + 1, inst);
}

/// Every slice-21 control, with what it must end as. The mis-models the
/// design lists (§5.5), each a unit fixture: `mulss` for `mulsd`, the
/// operands of a `divsd` swapped, a wrong rounding direction (`cvtsd2si` for
/// `cvttsd2si`) and a wrong operator (`divsd` for `mulsd`), `une` without its
/// `setp`, `olt` without its `setnp`, `oge` as `seta`, the saturating
/// conversion without its NaN `cmovp` and with `cmova` for its `cmovae`, an
/// unsigned conversion lowered as the signed `cvtsi2sd` alone, an exchange
/// returning the new value, an `I128` load with its halves swapped; and the
/// pairing controls: an `I128` atomic load as two plain atomic `mov`s, a plain
/// `I128` load as the pseudo row, and the exchange as a plain atomic store.
pub(crate) fn slice_twenty_one_controls() -> Vec<Control21> {
    let mut controls = Vec::new();
    let mut push = |label, source, machine, expect| {
        controls.push(Control21 {
            label,
            source,
            machine,
            expect,
        })
    };
    let ends = Expect21::Refused("the machine ends its trace after 0 event(s)");
    // `mulss` where `mulsd` belongs: the operator keys differ (format), the
    // row pairs with no event, and the source's event has no partner.
    let (source, mut machine) = slice21_pair(Shape21::FmulF64);
    let row = nth(&machine, X86Opcode::Mulsd, 0);
    inst_mut(&mut machine, row).opcode = X86Opcode::Mulss;
    push("fmul64/mulss", source, machine, ends);
    // `divsd` where `mulsd` belongs (operation).
    let (source, mut machine) = slice21_pair(Shape21::FmulF64);
    let row = nth(&machine, X86Opcode::Mulsd, 0);
    inst_mut(&mut machine, row).opcode = X86Opcode::Divsd;
    push("fmul64/divsd", source, machine, ends);
    // A `mulsd` whose TV-1 stamp names another LIR instruction (the
    // `Return`): the stamps choose the pairing, so it pairs with no event.
    let (source, mut machine) = slice21_pair(Shape21::FmulF64);
    let row = nth(&machine, X86Opcode::Mulsd, 0);
    let inst = inst_mut(&mut machine, row);
    let LoweringProvenance::SourceInst { id, .. } = &mut inst.lowering_provenance else {
        panic!(
            "the selector stamps its mulsd: {:?}",
            inst.lowering_provenance
        );
    };
    id.index += 1;
    push("fmul64/stamped-elsewhere", source, machine, ends);
    // `divsd` with its operands swapped: paired, and its operands observed
    // against the source's.
    let (source, mut machine) = slice21_pair(Shape21::FdivF64);
    let row = nth(&machine, X86Opcode::Divsd, 0);
    inst_mut(&mut machine, row).operands.swap(1, 2);
    push("fdiv64/swapped", source, machine, Expect21::Uncredited);
    // `cvtsd2si` (rounding at MXCSR, to nearest even) where `cvttsd2si`
    // (toward zero) belongs.
    let (source, mut machine) = slice21_pair(Shape21::Pow2ToPow10);
    let row = nth(&machine, X86Opcode::Cvttsd2si, 0);
    inst_mut(&mut machine, row).opcode = X86Opcode::Cvtsd2si;
    push(
        "pow2/cvtsd2si",
        source,
        machine,
        Expect21::Refused("the machine ends its trace after 2 event(s)"),
    );
    // `une` as `setne` alone (the `setp` of the unordered case lost).
    let (source, mut machine) = slice21_pair(Shape21::Fcmp64(FCmpOp::UNe));
    set_condition(&mut machine, X86Opcode::Setcc, 1, X86CondCode::NE);
    push("une64/no-setp", source, machine, Expect21::Refuted);
    // `olt` as `setb` alone (NaN taken as less).
    let (source, mut machine) = slice21_pair(Shape21::Fcmp64(FCmpOp::OLt));
    set_condition(&mut machine, X86Opcode::Setcc, 1, X86CondCode::B);
    push("olt64/no-setnp", source, machine, Expect21::Refuted);
    // `oge` as `seta` (equal operands lost).
    let (source, mut machine) = slice21_pair(Shape21::Fcmp64(FCmpOp::OGe));
    set_condition(&mut machine, X86Opcode::Setcc, 0, X86CondCode::A);
    push("oge64/seta", source, machine, Expect21::Refuted);
    // The saturating conversion without its NaN `cmovp` (NaN reaches MIN).
    let (source, mut machine) = slice21_pair(Shape21::F64ToI64);
    let row = nth(&machine, X86Opcode::Cmovcc, 2);
    *inst_mut(&mut machine, row) = X86ISelInst::new(X86Opcode::Nop, vec![]);
    push("f64toi64/no-cmovp", source, machine, Expect21::Uncredited);
    // Its MAX fix-up on `cmova` (misses exactly `2^63`).
    let (source, mut machine) = slice21_pair(Shape21::F64ToI64);
    set_condition(&mut machine, X86Opcode::Cmovcc, 0, X86CondCode::A);
    push("f64toi64/cmova", source, machine, Expect21::Uncredited);
    // `u64 as f64` lowered as the signed `cvtsi2sd` alone (no top-bit
    // fix-up): the classic miscompile, refuted by the pairing's claim that
    // bit 63 is clear.
    let source = slice21_variant(Variant21::U64ToF64);
    let mut signed = slice21_lir(Shape21::I64ToF64);
    signed.name = source.name.clone();
    let machine = select(&signed, X86CallAbi::SystemV);
    push("u2f64/signed-only", source, machine, Expect21::Uncredited);
    // An exchange that returns the new value (`mov dst, src` after it).
    let (source, mut machine) = slice21_pair(Shape21::AtomicXchgU64);
    let row = nth(&machine, X86Opcode::AtomicRmwCasLoop, 0);
    let (dst, src) = {
        let inst = inst_mut(&mut machine, row);
        (inst.operands[0].clone(), inst.operands[1].clone())
    };
    insert_after(
        &mut machine,
        row,
        X86ISelInst::new(X86Opcode::MovRR, vec![dst, src]),
    );
    push("xchg64/returns-new", source, machine, Expect21::Refuted);
    // An `I128` atomic load whose halves are read back swapped.
    let (source, mut machine) = slice21_pair(Shape21::AtomicLoadU128);
    let pseudo = nth(&machine, X86Opcode::AtomicLoadCmpxchg16b, 0);
    let (low, high) = (pseudo + 1, pseudo + 2);
    let low_source = inst_mut(&mut machine, low).operands[1].clone();
    let high_source = inst_mut(&mut machine, high).operands[1].clone();
    inst_mut(&mut machine, low).operands[1] = high_source;
    inst_mut(&mut machine, high).operands[1] = low_source;
    push("ld128/halves-swapped", source, machine, Expect21::Refuted);
    // An `I128` atomic load as two plain 8-byte atomic loads: never paired.
    let (source, mut machine) = slice21_pair(Shape21::AtomicLoadU128);
    let pseudo = nth(&machine, X86Opcode::AtomicLoadCmpxchg16b, 0);
    let address = inst_mut(&mut machine, pseudo).operands[0].clone();
    let O::MemAddr { base, .. } = &address else {
        unreachable!("the pseudo's operand is its address");
    };
    let load = |disp: i32, register: O| {
        let mut inst = X86ISelInst::new(
            X86Opcode::MovRM,
            vec![
                register,
                O::MemAddr {
                    base: base.clone(),
                    disp,
                },
            ],
        );
        inst.proof_origin = Some(X86ProofOrigin::AtomicLoad);
        inst
    };
    let (low_load, high_load) = (
        load(0, O::PReg(trust_cg_ir::x86_64_regs::RAX)),
        load(8, O::PReg(trust_cg_ir::x86_64_regs::RDX)),
    );
    *inst_mut(&mut machine, pseudo) = low_load;
    insert_after(&mut machine, pseudo, high_load);
    push(
        "ld128/plain-atomic-movs",
        source,
        machine,
        Expect21::Refused("paired with an atomic source access its pseudo row lowers"),
    );
    // A plain `I128` load lowered as the pseudo row: never paired.
    let mut plain = slice21_variant(Variant21::LoadU128);
    let (atomic, machine) = slice21_pair(Shape21::AtomicLoadU128);
    plain.name = atomic.name.clone();
    push(
        "ld128/pseudo-for-plain-load",
        plain,
        machine,
        Expect21::Refused("paired with a source access it does not lower"),
    );
    // The exchange as a plain atomic store: never paired.
    let (source, mut machine) = slice21_pair(Shape21::AtomicStoreSeqCst);
    let row = nth(&machine, X86Opcode::AtomicRmwCasLoop, 0);
    let operands = inst_mut(&mut machine, row).operands.clone();
    let mut store = X86ISelInst::new(
        X86Opcode::MovMR,
        vec![operands[2].clone(), operands[1].clone()],
    );
    store.proof_origin = Some(X86ProofOrigin::AtomicStore);
    *inst_mut(&mut machine, row) = store;
    push(
        "xchg64/plain-store",
        source,
        machine,
        Expect21::Refused("paired with an atomic source access its pseudo row lowers"),
    );
    controls
}

/// Every slice-21 control ends as it must: a pure bit-vector one refuted on
/// samples (and naming no FP leaf), an abstract one refuted on samples and
/// naming one (so its satisfying model is no counterexample, OD-200), and a
/// refused one refused by name.
#[test]
fn every_slice_twenty_one_control_ends_as_it_must() {
    for control in slice_twenty_one_controls() {
        let Control21 {
            label,
            source,
            machine,
            expect,
        } = &control;
        let outcome = source_bound_x86_body(source, machine, SYSV);
        match (expect, outcome) {
            (Expect21::Refuted | Expect21::Uncredited, Ok(owner)) => {
                assert!(
                    dag_refuted_on_samples(owner.obligation()),
                    "{label}: not refuted on samples\n{}{}",
                    describe(machine),
                    text(owner.obligation())
                );
                assert_eq!(
                    owner.is_fp_abstract(),
                    *expect == Expect21::Uncredited,
                    "{label}"
                );
            }
            (Expect21::Refused(needle), Err(X86BodyRefusal::Unsupported(reason))) => {
                let reason = reason.to_string();
                assert!(reason.contains(needle), "{label}: {reason}");
            }
            (expect, outcome) => panic!(
                "{label}: expected {expect:?}, got {:?}\n{}",
                outcome.map(|owner| text(owner.obligation())),
                describe(machine)
            ),
        }
    }
}

/// OD-201's RBX rule is the pseudo row's alone: its fixed `xor ebx, ebx` is a
/// clobber the frame restores (trusted), while any other write of RBX stays
/// a preserved-register mismatch.
#[test]
fn only_the_cmpxchg16b_pseudo_may_write_rbx() {
    let (source, machine) = slice21_pair(Shape21::AtomicLoadU128);
    owner("AtomicLoadU128", &source, &machine);
    let mut written = machine.clone();
    let pseudo = nth(&written, X86Opcode::AtomicLoadCmpxchg16b, 0);
    insert_after(
        &mut written,
        pseudo,
        X86ISelInst::new(
            X86Opcode::MovRI,
            vec![O::PReg(trust_cg_ir::x86_64_regs::RBX), O::Imm(0)],
        ),
    );
    match source_bound_x86_body(&source, &written, SYSV) {
        Err(X86BodyRefusal::Mismatch(X86BodyMismatch::PreservedWrite { register, .. })) => {
            assert_eq!(register, "rbx");
        }
        Err(other) => panic!("expected a preserved-register write, got {other}"),
        Ok(_) => panic!("a body writing RBX outside the pseudo built a theorem"),
    }
}

/// The verify-owned compare meanings ([`FloatRelation::holds`], of the LIR
/// condition the real adapter maps each trust-ir predicate to) and the
/// saturating conversion ([`saturating_f64_to_i64`], its in-range value the
/// truncation) are trust-ir's, measured against the pinned reference
/// interpreter on every class of pattern: zeros of both signs, subnormals,
/// normals, the conversion bounds and their neighbours, infinities, and quiet
/// and signalling NaNs with payloads; `FPToSI` agrees wherever it is defined.
#[test]
fn the_float_compare_and_conversion_meanings_are_trust_irs() {
    use crate::smt::{EvalEnv, EvalResult};
    use trust_ir::interpret::{InterpretValue, InterpretValueKind, Interpreter};
    let mut builder = ModuleBuilder::new("x86_source_bound_body_slice21_meanings");
    for (ty, tag) in [(Ty::F32, "f32"), (Ty::F64, "f64")] {
        for (k, op) in FCMP_OPS.iter().enumerate() {
            let signature = builder.add_func_type(vec![ty.clone(), ty.clone()], vec![Ty::Bool]);
            let mut f = builder.function(format!("fcmp{k}_{tag}"), signature);
            let entry = f.create_block();
            let a = f.add_block_param(entry, ty.clone());
            let b = f.add_block_param(entry, ty.clone());
            f.switch_to_block(entry);
            let holds = f.fcmp(*op, ty.clone(), a, b);
            f.ret(vec![holds]);
            f.build();
        }
    }
    for (cast, tag) in [(CastOp::FPToSISat, "sat"), (CastOp::FPToSI, "raw")] {
        let signature = builder.add_func_type(vec![Ty::F64], vec![Ty::I64]);
        let mut f = builder.function(format!("to_i64_{tag}"), signature);
        let entry = f.create_block();
        let x = f.add_block_param(entry, Ty::F64);
        f.switch_to_block(entry);
        let r = f.cast(cast, Ty::F64, Ty::I64, x);
        f.ret(vec![r]);
        f.build();
    }
    let module = builder.build().expect("ModuleBuilder::build: test fixture");
    // The LIR condition the adapter gives each predicate.
    let lowered = trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        &module,
        trust_cg_lower::GuardCarrierArch::X86_64,
        trust_cg_lower::TlsDialect::default(),
        &crate::license_test_support::permit_unlicensed(),
    )
    .expect("the meanings module translates");
    let condition = |name: &str| -> FloatCC {
        let (function, _) = lowered
            .iter()
            .find(|(function, _)| function.name == name)
            .expect("translated");
        function
            .blocks
            .values()
            .flat_map(|block| &block.instructions)
            .find_map(|inst| match inst.opcode {
                L::Fcmp { cond } => Some(cond),
                _ => None,
            })
            .expect("an Fcmp")
    };
    let interpreter = Interpreter::with_module(&module);
    let run = |name: &str, args: Vec<(Ty, u64)>| {
        let function = module.function_by_name(name).expect("the function");
        interpreter.execute_function(
            function,
            args.into_iter()
                .map(|(ty, bits)| InterpretValue {
                    ty,
                    kind: InterpretValueKind::FloatBits(bits),
                })
                .collect::<Vec<_>>(),
        )
    };
    let patterns32: Vec<u64> = vec![
        0,
        0x8000_0000,
        1,
        0x8000_0001,
        0x0080_0000,
        0x3f80_0000,
        0xbf80_0000,
        0x3f80_0001,
        0x7f7f_ffff,
        0x7f80_0000,
        0xff80_0000,
        0x7fc0_0000,
        0xffc0_0001,
        0x7f80_0001,
        0x7fbf_ffff,
    ];
    let patterns64: Vec<u64> = vec![
        0,
        1 << 63,
        1,
        0x8000_0000_0000_0001,
        0x0010_0000_0000_0000,
        0x3ff0_0000_0000_0000,
        0xbff0_0000_0000_0000,
        0x3ff0_0000_0000_0001,
        F64_TWO_POW_63,
        F64_TWO_POW_63 - 1,
        F64_TWO_POW_63 + 1,
        F64_MINUS_TWO_POW_63,
        F64_MINUS_TWO_POW_63 - 1,
        F64_MINUS_TWO_POW_63 + 1,
        0x43df_ffff_ffff_ffff,
        0x7fef_ffff_ffff_ffff,
        0x7ff0_0000_0000_0000,
        0xfff0_0000_0000_0000,
        0x7ff8_0000_0000_0000,
        0xfff8_0000_0000_0001,
        0x7ff0_0000_0000_0001,
        0x4415_af1d_78b5_8c40,
        0xc0c3_8800_0000_0000,
    ];
    for (format, ty, tag, patterns) in [
        (Carrier::F32, Ty::F32, "f32", &patterns32),
        (Carrier::F64, Ty::F64, "f64", &patterns64),
    ] {
        let bits = format.bits();
        for k in 0..FCMP_OPS.len() {
            let name = format!("fcmp{k}_{tag}");
            let cond = condition(&name);
            for a in patterns {
                for b in patterns {
                    let outcome = run(&name, vec![(ty.clone(), *a), (ty.clone(), *b)])
                        .unwrap_or_else(|error| panic!("{name}: {error:?}"));
                    let [
                        InterpretValue {
                            kind: InterpretValueKind::Bool(expected),
                            ..
                        },
                    ] = &outcome.returns[..]
                    else {
                        panic!("{name}: {:?}", outcome.returns);
                    };
                    let mut env = EvalEnv::default();
                    env.insert("a".into(), *a);
                    env.insert("b".into(), *b);
                    let stated = FloatRelation::of(format, &E::var("a", bits), &E::var("b", bits))
                        .holds(cond)
                        .eval(&env);
                    assert_eq!(
                        stated,
                        EvalResult::Bool(*expected),
                        "{name} ({cond:?}) {a:#x} {b:#x}"
                    );
                }
            }
        }
    }
    for x in &patterns64 {
        let value = f64::from_bits(*x);
        // The conversion's event: the truncation toward zero, which Rust's
        // `as` computes wherever it fits.
        let leaf = (value as i64) as u64;
        let mut env = EvalEnv::default();
        env.insert("x".into(), *x);
        env.insert("leaf".into(), leaf);
        let EvalResult::Bv(stated) =
            saturating_f64_to_i64(&E::var("x", 64), E::var("leaf", 64)).eval(&env)
        else {
            panic!("a bit-vector");
        };
        let fits = f64_fits_i64(&E::var("x", 64)).eval(&env) == EvalResult::Bool(true);
        assert_eq!(
            fits,
            value >= -(2f64.powi(63)) && value < 2f64.powi(63),
            "{x:#x}"
        );
        let int = |outcome: Result<trust_ir::InterpretOutcome, _>| match outcome {
            Ok(outcome) => match &outcome.returns[..] {
                [
                    InterpretValue {
                        kind: InterpretValueKind::Int(result),
                        ..
                    },
                ] => Some(result.raw as u64),
                other => panic!("{other:?}"),
            },
            Err(_) => None,
        };
        assert_eq!(
            int(run("to_i64_sat", vec![(Ty::F64, *x)])),
            Some(stated),
            "FPToSISat {x:#x}"
        );
        match int(run("to_i64_raw", vec![(Ty::F64, *x)])) {
            Some(raw) => {
                assert!(fits, "FPToSI {x:#x} is defined only where it fits");
                assert_eq!(raw, stated, "FPToSI {x:#x}");
            }
            None => assert!(
                !fits,
                "FPToSI {x:#x} is undefined only where it does not fit"
            ),
        }
    }
}

/// The exact parts of the SSE transcription (OD-198's T1) and the default
/// MXCSR (T3), measured on this host's own hardware: `ucomisd`/`ucomiss`
/// write the ZF, PF and CF [`FloatRelation::ucomis_flags`] states, and
/// `cvttsd2si` returns the truncation where [`f64_fits_i64`] holds and the
/// integer indefinite elsewhere. Testing evidence for the trust, never credit.
#[cfg(target_arch = "x86_64")]
#[test]
fn the_sse_compare_and_truncation_rows_are_the_hosts() {
    use crate::smt::{EvalEnv, EvalResult};
    let mut mxcsr = 0u32;
    // SAFETY: `stmxcsr` writes the four bytes of `mxcsr`, which the pointer
    // names exclusively, and has no other effect.
    unsafe {
        core::arch::asm!("stmxcsr [{p}]", p = in(reg) &mut mxcsr, options(nostack));
    }
    assert_eq!(mxcsr & 0xffc0, 0x1f80, "MXCSR's control bits: {mxcsr:#x}");
    let patterns64: Vec<u64> = vec![
        0,
        1 << 63,
        1,
        0x3ff0_0000_0000_0000,
        0xbff0_0000_0000_0000,
        0x3ff8_0000_0000_0000,
        F64_TWO_POW_63,
        F64_TWO_POW_63 - 1,
        F64_MINUS_TWO_POW_63,
        F64_MINUS_TWO_POW_63 + 1,
        0x7ff0_0000_0000_0000,
        0xfff0_0000_0000_0000,
        0x7ff8_0000_0000_0000,
        0x7ff0_0000_0000_0001,
        0xc0c3_8800_0000_0000,
    ];
    for a in &patterns64 {
        for b in &patterns64 {
            let (zf, pf, cf): (u8, u8, u8);
            // SAFETY: register-only instructions; no memory, no stack.
            unsafe {
                core::arch::asm!(
                    "ucomisd {a}, {b}",
                    "setz {zf}",
                    "setp {pf}",
                    "setc {cf}",
                    a = in(xmm_reg) f64::from_bits(*a),
                    b = in(xmm_reg) f64::from_bits(*b),
                    zf = out(reg_byte) zf,
                    pf = out(reg_byte) pf,
                    cf = out(reg_byte) cf,
                    options(nomem, nostack),
                );
            }
            let flags =
                FloatRelation::of(Carrier::F64, &E::var("a", 64), &E::var("b", 64)).ucomis_flags();
            let mut env = EvalEnv::default();
            env.insert("a".into(), *a);
            env.insert("b".into(), *b);
            for (flag, stated) in [(zf, &flags.zf), (pf, &flags.pf), (cf, &flags.cf)] {
                assert_eq!(
                    stated.clone().expect("defined").eval(&env),
                    EvalResult::Bool(flag == 1),
                    "ucomisd {a:#x} {b:#x}"
                );
            }
        }
        let truncated: i64;
        // SAFETY: a register-only instruction.
        unsafe {
            core::arch::asm!(
                "cvttsd2si {r}, {x}",
                r = out(reg) truncated,
                x = in(xmm_reg) f64::from_bits(*a),
                options(nomem, nostack),
            );
        }
        let mut env = EvalEnv::default();
        env.insert("x".into(), *a);
        let expected = if f64_fits_i64(&E::var("x", 64)).eval(&env) == EvalResult::Bool(true) {
            f64::from_bits(*a) as i64
        } else {
            i64::MIN
        };
        assert_eq!(truncated, expected, "cvttsd2si {a:#x}");
    }
    for a in [
        0u32,
        0x8000_0000,
        0x3f80_0000,
        0xbf80_0000,
        0x7f80_0000,
        0x7fc0_0000,
    ] {
        for b in [0u32, 0x8000_0000, 0x3f80_0000, 0x7fc0_0001, 0xff80_0000] {
            let (zf, pf, cf): (u8, u8, u8);
            // SAFETY: register-only instructions; no memory, no stack.
            unsafe {
                core::arch::asm!(
                    "ucomiss {a}, {b}",
                    "setz {zf}",
                    "setp {pf}",
                    "setc {cf}",
                    a = in(xmm_reg) f32::from_bits(a),
                    b = in(xmm_reg) f32::from_bits(b),
                    zf = out(reg_byte) zf,
                    pf = out(reg_byte) pf,
                    cf = out(reg_byte) cf,
                    options(nomem, nostack),
                );
            }
            let flags =
                FloatRelation::of(Carrier::F32, &E::var("a", 32), &E::var("b", 32)).ucomis_flags();
            let mut env = EvalEnv::default();
            env.insert("a".into(), u64::from(a));
            env.insert("b".into(), u64::from(b));
            for (flag, stated) in [(zf, &flags.zf), (pf, &flags.pf), (cf, &flags.cf)] {
                assert_eq!(
                    stated.clone().expect("defined").eval(&env),
                    EvalResult::Bool(flag == 1),
                    "ucomiss {a:#x} {b:#x}"
                );
            }
        }
    }
}

/// Every slice-21 fixture's theorem as the replay renders it (`;;;; <shape>`).
pub(crate) fn slice_twenty_one_snapshots() -> String {
    let mut rendered = String::new();
    for shape in slice_twenty_one() {
        let (source, machine) = slice21_pair(shape);
        let owner = owner(&format!("{shape:?}"), &source, &machine);
        rendered.push_str(&format!(";;;; {shape:?}\n{}\n", text(owner.obligation())));
    }
    rendered
}

/// The reviewed digest of the slice-21 golden text.
const SLICE_TWENTY_ONE_SNAPSHOT_SHA256: &str =
    "2b613c0a7e73202462f2a18d630bb485c8defe123cb332ca833ea2d7e18d4da6";

/// The rendered theorems of every slice-21 fixture are the reviewed golden
/// text, pinned by digest, and independent of the function's name.
#[test]
fn slice_twenty_one_smt2_is_canonical_per_shape() {
    use sha2::{Digest, Sha256};
    const GOLDEN: &str =
        include_str!("../tests/fixtures/x86_source_bound_body/slice21_snapshots.smt2");
    let rendered = slice_twenty_one_snapshots();
    for shape in slice_twenty_one() {
        let (source, machine) = slice21_pair(shape);
        let (mut renamed_source, mut renamed_machine) = (source.clone(), machine.clone());
        renamed_source.name = "renamed_function".into();
        renamed_machine.name = "renamed_function".into();
        let original = owner("original", &source, &machine);
        let renamed = owner("renamed", &renamed_source, &renamed_machine);
        assert_eq!(
            text(renamed.obligation()),
            text(original.obligation()),
            "{shape:?}"
        );
    }
    if std::env::var_os("TCG_X86_BODY_SNAPSHOT_WRITE").is_some() {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures/x86_source_bound_body/slice21_snapshots.smt2");
        std::fs::write(&path, &rendered).unwrap();
        panic!(
            "rewrote {}; review its diff, set SLICE_TWENTY_ONE_SNAPSHOT_SHA256 to {:x} and \
             re-run without TCG_X86_BODY_SNAPSHOT_WRITE",
            path.display(),
            Sha256::digest(rendered.as_bytes())
        );
    }
    assert_eq!(
        format!("{:x}", Sha256::digest(GOLDEN.as_bytes())),
        SLICE_TWENTY_ONE_SNAPSHOT_SHA256,
        "the golden file changed without the reviewed digest pin"
    );
    assert_eq!(rendered, GOLDEN, "slice-21 snapshots drifted");
}

/// Rounding events inside a loop (slice 12's regions) and across slice 16's
/// cut points: `fn(x: f64, n: u64) -> f64 { let mut a = x; let mut i = 0;
/// while i < n { a = a * x; i += 1 } a }` and `fn(a: f64, b: f64) -> f64 { let
/// p = a * b; tick(); p / a }` (the second with a block of its own after the
/// product), each with its real selector output.
pub(crate) fn region_fixtures() -> Vec<(Function, X86ISelFunction)> {
    let mut builder = ModuleBuilder::new("x86_source_bound_body_slice21_regions");
    let tick = {
        let ty = builder.add_func_type(vec![], vec![]);
        builder.declare_function("tick", ty)
    };
    let signature = builder.add_func_type(vec![Ty::F64, Ty::U64], vec![Ty::F64]);
    let mut f = builder.function("s21_fmul_loop", signature);
    let entry = f.create_block();
    let x = f.add_block_param(entry, Ty::F64);
    let n = f.add_block_param(entry, Ty::U64);
    f.switch_to_block(entry);
    let (header, body, exit) = (f.create_block(), f.create_block(), f.create_block());
    let a = f.add_block_param(header, Ty::F64);
    let i = f.add_block_param(header, Ty::U64);
    let zero = f.iconst(Ty::U64, 0);
    f.br(header, vec![x, zero]);
    f.switch_to_block(header);
    let go = f.icmp(trust_ir::ICmpOp::Ult, Ty::U64, i, n);
    f.condbr(go, body, vec![], exit, vec![]);
    f.switch_to_block(body);
    let product = f.fmul(Ty::F64, a, x);
    let one = f.iconst(Ty::U64, 1);
    let next = f.binop(BinOp::Add, Ty::U64, i, one);
    f.br(header, vec![product, next]);
    f.switch_to_block(exit);
    f.ret(vec![a]);
    f.build();
    let signature = builder.add_func_type(vec![Ty::F64, Ty::F64], vec![Ty::F64]);
    let mut f = builder.function("s21_fmul_call_fdiv", signature);
    let entry = f.create_block();
    let a = f.add_block_param(entry, Ty::F64);
    let b = f.add_block_param(entry, Ty::F64);
    f.switch_to_block(entry);
    let p = f.fmul(Ty::F64, a, b);
    let after = f.create_block();
    f.br(after, vec![]);
    f.switch_to_block(after);
    f.call_void(tick, vec![]);
    let q = f.binop(BinOp::FDiv, Ty::F64, p, a);
    f.ret(vec![q]);
    f.build();
    let module = builder.build().expect("ModuleBuilder::build: test fixture");
    trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        &module,
        trust_cg_lower::GuardCarrierArch::X86_64,
        trust_cg_lower::TlsDialect::default(),
        &crate::license_test_support::permit_unlicensed(),
    )
    .expect("the region fixtures translate")
    .into_iter()
    .map(|(source, _)| {
        let machine = select(&source, X86CallAbi::SystemV);
        (source, machine)
    })
    .collect()
}

/// Each region fixture ([`region_fixtures`]), as the production owner states
/// it and cut at every block, either builds a theorem that holds on samples
/// and is FP-abstract, or is refused by name. Never a mismatch, never a
/// panic. (Measured: all four are stated.)
#[test]
fn rounding_events_in_a_loop_and_across_cuts_are_stated_or_refused_by_name() {
    use super::slice16::{cut_at, every_block, parts_hold};
    for (source, machine) in region_fixtures() {
        let name = source.name.clone();
        let judge =
            |outcome: Result<SourceBoundX86Body<'_>, X86BodyRefusal>, how: &str| match outcome {
                Ok(owner) => {
                    assert!(owner.is_fp_abstract(), "{name} ({how})");
                    if owner.is_stated_in_parts() {
                        parts_hold(&owner).unwrap_or_else(|why| panic!("{name} ({how}): {why}"));
                    } else {
                        assert!(
                            dag_holds_on_samples(owner.obligation()),
                            "{name} ({how}): refuted on samples\n{}",
                            text(owner.obligation())
                        );
                    }
                    eprintln!("SLICE21_REGIONS {name} ({how}): stated");
                }
                Err(X86BodyRefusal::Unsupported(reason)) => {
                    eprintln!("SLICE21_REGIONS {name} ({how}): refused: {reason}");
                }
                Err(X86BodyRefusal::Mismatch(mismatch)) => panic!(
                    "{name} ({how}): a correct lowering is a mismatch: {mismatch}\n{}{}",
                    describe_lir(&source),
                    describe(&machine)
                ),
            };
        judge(source_bound_x86_body(&source, &machine, SYSV), "production");
        judge(
            source_bound_x86_body_in_parts(&source, &machine, SYSV, &cut_at(every_block(&source))),
            "cut at every block",
        );
    }
}
