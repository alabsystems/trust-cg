// trust-cg-verify/src/fp_bv_lowering_tests.rs - tests for the FP -> BV lowering
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use super::*;
use crate::fp_bitmodel::{self, FpFmt};
use crate::smt::{EvalEnv, EvalResult, OutOfRangeMode};

/// Deterministic xorshift, so every run samples the same patterns.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }
}

/// Every class boundary of a `(eb, sb)` format, both signs, plus NaNs with
/// assorted payloads (quiet, signalling, all-ones, negative).
fn edge_patterns(eb: u32, sb: u32) -> Vec<u64> {
    let width = eb + sb;
    let sign = 1u64 << (width - 1);
    let exp = ((1u64 << eb) - 1) << (sb - 1);
    let man = (1u64 << (sb - 1)) - 1;
    let one = ((1u64 << (eb - 1)) - 1) << (sb - 1);
    let magnitudes = [
        0,
        1,
        2,
        man - 1,
        man,
        man + 1,
        one - 1,
        one,
        one + 1,
        exp - 1,
        exp,
        exp | 1,
        exp | (1 << (sb - 2)),
        exp | man,
        exp | (man >> 1),
    ];
    let mut out = Vec::new();
    for m in magnitudes {
        out.push(m);
        out.push(m | sign);
    }
    out
}

fn samples(eb: u32, sb: u32, rng: &mut Rng, random: usize) -> Vec<u64> {
    let width = eb + sb;
    let mask = if width == 64 {
        u64::MAX
    } else {
        (1u64 << width) - 1
    };
    let mut out = edge_patterns(eb, sb);
    out.extend((0..random).map(|_| rng.next() & mask));
    out
}

fn eval_bool(expr: &SmtExpr, env: &EvalEnv) -> bool {
    match expr.try_eval(env).expect("lowered term evaluates") {
        EvalResult::Bool(b) => b,
        other => panic!("expected Bool, got {other:?}"),
    }
}

fn eval_bits(expr: &SmtExpr, env: &EvalEnv) -> u64 {
    match expr.try_eval(env).expect("lowered term evaluates") {
        EvalResult::Bv(v) => v,
        other => panic!("expected a bit-vector, got {other:?}"),
    }
}

fn lowered(formula: &SmtExpr) -> FpBvLowering {
    lower_fp_to_bv(formula, &[], &[]).expect("formula lowers")
}

fn fp_of(name: &str, eb: u32, sb: u32) -> SmtExpr {
    SmtExpr::BvBitsToFP {
        operand: Arc::new(SmtExpr::var(name, eb + sb)),
        eb,
        sb,
    }
}

fn env2(a: u64, b: u64) -> EvalEnv {
    let mut env = EvalEnv::default();
    env.insert("a".into(), a);
    env.insert("b".into(), b);
    env
}

const FORMATS: [(u32, u32, FpFmt); 3] = [
    (5, 11, fp_bitmodel::F16),
    (8, 24, fp_bitmodel::F32),
    (11, 53, fp_bitmodel::F64),
];

/// Reference: the integer-only IEEE model [`fp_bitmodel`] (validated
/// bit-for-bit against Apple silicon by `tests/fp_bitmodel_bridge.rs`).
fn reference_lt(f: FpFmt, a: u64, b: u64) -> bool {
    fp_bitmodel::fcmp_n(f, a, b)
}
fn reference_eq(f: FpFmt, a: u64, b: u64) -> bool {
    fp_bitmodel::fcmp_z(f, a, b)
}

#[test]
fn predicates_agree_with_the_integer_ieee_model_in_every_format() {
    let mut rng = Rng(0x9e37_79b9_7f4a_7c15);
    for (eb, sb, f) in FORMATS {
        let pats = samples(eb, sb, &mut rng, 48);
        let (a, b) = (fp_of("a", eb, sb), fp_of("b", eb, sb));
        let bin = |node: fn(Arc<SmtExpr>, Arc<SmtExpr>) -> SmtExpr, x: &SmtExpr, y: &SmtExpr| {
            lowered(&node(Arc::new(x.clone()), Arc::new(y.clone()))).formula
        };
        let lt = bin(|l, r| SmtExpr::FPLt { lhs: l, rhs: r }, &a, &b);
        let le = bin(|l, r| SmtExpr::FPLe { lhs: l, rhs: r }, &a, &b);
        let gt = bin(|l, r| SmtExpr::FPGt { lhs: l, rhs: r }, &a, &b);
        let ge = bin(|l, r| SmtExpr::FPGe { lhs: l, rhs: r }, &a, &b);
        let feq = bin(|l, r| SmtExpr::FPEq { lhs: l, rhs: r }, &a, &b);
        let same = lowered(&a.clone().eq_expr(b.clone())).formula;
        let unary = |node: fn(Arc<SmtExpr>) -> SmtExpr| lowered(&node(Arc::new(a.clone()))).formula;
        let nan = unary(|x| SmtExpr::FPIsNaN { operand: x });
        let inf = unary(|x| SmtExpr::FPIsInf { operand: x });
        let zero = unary(|x| SmtExpr::FPIsZero { operand: x });
        let normal = unary(|x| SmtExpr::FPIsNormal { operand: x });
        for &x in &pats {
            let env = env2(x, 0);
            assert_eq!(
                eval_bool(&nan, &env),
                fp_bitmodel::is_nan(f, x),
                "isNaN {x:#x}"
            );
            assert_eq!(
                eval_bool(&inf, &env),
                fp_bitmodel::is_inf(f, x),
                "isInf {x:#x}"
            );
            assert_eq!(
                eval_bool(&zero, &env),
                fp_bitmodel::is_zero(f, x),
                "isZero {x:#x}"
            );
            assert_eq!(
                eval_bool(&normal, &env),
                fp_bitmodel::is_normal(f, x),
                "isNormal {x:#x}"
            );
            for &y in &pats {
                let env = env2(x, y);
                let ctx = format!("({eb},{sb}) a={x:#x} b={y:#x}");
                assert_eq!(eval_bool(&lt, &env), reference_lt(f, x, y), "lt {ctx}");
                assert_eq!(
                    eval_bool(&le, &env),
                    reference_lt(f, x, y) || reference_eq(f, x, y),
                    "leq {ctx}"
                );
                assert_eq!(eval_bool(&gt, &env), reference_lt(f, y, x), "gt {ctx}");
                assert_eq!(
                    eval_bool(&ge, &env),
                    reference_lt(f, y, x) || reference_eq(f, y, x),
                    "geq {ctx}"
                );
                assert_eq!(eval_bool(&feq, &env), reference_eq(f, x, y), "fp.eq {ctx}");
                // SMT-LIB `=`: identity of VALUES — one NaN, and +0 != -0.
                let identical = (fp_bitmodel::is_nan(f, x) && fp_bitmodel::is_nan(f, y)) || x == y;
                assert_eq!(eval_bool(&same, &env), identical, "= {ctx}");
            }
        }
    }
}

#[test]
fn predicates_agree_with_the_host_ieee_unit_for_binary32_and_binary64() {
    // A second, independent reference: the host FPU's own comparisons.
    let mut rng = Rng(0x2545_f491_4f6c_dd1d);
    let (a32, b32) = (fp_of("a", 8, 24), fp_of("b", 8, 24));
    let lt32 = lowered(&SmtExpr::FPLt {
        lhs: Arc::new(a32.clone()),
        rhs: Arc::new(b32.clone()),
    })
    .formula;
    let eq32 = lowered(&SmtExpr::FPEq {
        lhs: Arc::new(a32),
        rhs: Arc::new(b32),
    })
    .formula;
    let pats = samples(8, 24, &mut rng, 200);
    for &x in &pats {
        for &y in &pats {
            let (fx, fy) = (f32::from_bits(x as u32), f32::from_bits(y as u32));
            assert_eq!(eval_bool(&lt32, &env2(x, y)), fx < fy, "{fx:e} < {fy:e}");
            assert_eq!(eval_bool(&eq32, &env2(x, y)), fx == fy, "{fx:e} == {fy:e}");
        }
    }
    let (a64, b64) = (fp_of("a", 11, 53), fp_of("b", 11, 53));
    let le64 = lowered(&SmtExpr::FPLe {
        lhs: Arc::new(a64.clone()),
        rhs: Arc::new(b64.clone()),
    })
    .formula;
    let ge64 = lowered(&SmtExpr::FPGe {
        lhs: Arc::new(a64),
        rhs: Arc::new(b64),
    })
    .formula;
    let pats = samples(11, 53, &mut rng, 200);
    for &x in &pats {
        for &y in &pats {
            let (fx, fy) = (f64::from_bits(x), f64::from_bits(y));
            assert_eq!(eval_bool(&le64, &env2(x, y)), fx <= fy, "{fx:e} <= {fy:e}");
            assert_eq!(eval_bool(&ge64, &env2(x, y)), fx >= fy, "{fx:e} >= {fy:e}");
        }
    }
}

#[test]
fn binary16_unary_predicates_are_exhaustively_exact() {
    let x = fp_of("a", 5, 11);
    let nan = lowered(&SmtExpr::FPIsNaN {
        operand: Arc::new(x.clone()),
    })
    .formula;
    let normal = lowered(&SmtExpr::FPIsNormal {
        operand: Arc::new(x),
    })
    .formula;
    for bits in 0..=u64::from(u16::MAX) {
        let env = env2(bits, 0);
        assert_eq!(
            eval_bool(&nan, &env),
            fp_bitmodel::is_nan(fp_bitmodel::F16, bits)
        );
        assert_eq!(
            eval_bool(&normal, &env),
            fp_bitmodel::is_normal(fp_bitmodel::F16, bits)
        );
    }
}

#[test]
fn sign_operations_denote_the_negated_and_absolute_value() {
    let mut rng = Rng(0x1234_5678_9abc_def1);
    let a = fp_of("a", 8, 24);
    let mut probe = Lowerer {
        fp_vars: HashMap::new(),
        reserved: Vec::new(),
        applications: Vec::new(),
        index: HashMap::new(),
    };
    let neg = probe
        .lower(&SmtExpr::FPNeg {
            operand: Arc::new(a.clone()),
        })
        .unwrap();
    let abs = probe
        .lower(&SmtExpr::FPAbs {
            operand: Arc::new(a),
        })
        .unwrap();
    for x in samples(8, 24, &mut rng, 500) {
        let env = env2(x, 0);
        let v = f32::from_bits(x as u32);
        let same_value = |bits: u64, want: f32| {
            let got = f32::from_bits(bits as u32);
            (got.is_nan() && want.is_nan()) || got.to_bits() == want.to_bits()
        };
        assert!(same_value(eval_bits(&neg, &env), -v), "fp.neg {x:#x}");
        assert!(same_value(eval_bits(&abs, &env), v.abs()), "fp.abs {x:#x}");
    }
}

#[test]
fn equal_applications_share_one_variable_and_distinct_ones_are_constrained() {
    let (a, b) = (fp_of("a", 8, 24), fp_of("b", 8, 24));
    let div = |l: &SmtExpr, r: &SmtExpr| SmtExpr::FPDiv {
        rm: RoundingMode::RNE,
        lhs: Arc::new(l.clone()),
        rhs: Arc::new(r.clone()),
    };
    // X == X: one application, no constraint.
    let identity = lower_fp_to_bv(&div(&a, &b).eq_expr(div(&a, &b)).not_expr(), &[], &[]).unwrap();
    assert_eq!(identity.abstractions.len(), 1);
    assert_eq!(identity.declarations, vec![("tcg_fpbv_0".to_string(), 32)]);

    // Two applications of one operator: exactly one consistency constraint,
    // `(a = b) => (v0 = v1)` spelled `(or (not ...) ...)`.
    let swapped = lower_fp_to_bv(&div(&a, &b).eq_expr(div(&b, &a)).not_expr(), &[], &[]).unwrap();
    assert_eq!(swapped.abstractions.len(), 2);
    let text = swapped.formula.to_string();
    assert!(text.contains("(= tcg_fpbv_0 tcg_fpbv_1)"), "{text}");

    // Different rounding modes are different operators: no constraint.
    let rtz = SmtExpr::FPDiv {
        rm: RoundingMode::RTZ,
        lhs: Arc::new(a.clone()),
        rhs: Arc::new(b.clone()),
    };
    let modes = lower_fp_to_bv(&div(&a, &b).eq_expr(rtz).not_expr(), &[], &[]).unwrap();
    assert_eq!(modes.abstractions.len(), 2);
    assert!(
        !modes
            .formula
            .to_string()
            .contains("(= tcg_fpbv_0 tcg_fpbv_1)")
    );

    // Out-of-range modes of fp.to_sbv are different operators too.
    let conv = |mode| SmtExpr::FPToSBv {
        rm: RoundingMode::RTZ,
        operand: Arc::new(a.clone()),
        width: 32,
        mode,
    };
    let sat_vs_indef = lower_fp_to_bv(
        &conv(OutOfRangeMode::Saturate)
            .eq_expr(conv(OutOfRangeMode::IntegerIndefinite))
            .not_expr(),
        &[],
        &[],
    )
    .unwrap();
    assert_eq!(sat_vs_indef.abstractions.len(), 2);
}

#[test]
fn fresh_variables_avoid_reserved_names() {
    let a = fp_of("a", 8, 24);
    let sqrt = SmtExpr::FPSqrt {
        rm: RoundingMode::RNE,
        operand: Arc::new(a),
    };
    let out = lower_fp_to_bv(
        &sqrt.clone().eq_expr(sqrt).not_expr(),
        &[],
        &["tcg_fpbv_0".to_string()],
    )
    .unwrap();
    assert_eq!(out.abstractions[0].0, "tcg_fpbv_1");
}

#[test]
fn declines_what_it_cannot_lower() {
    assert_eq!(
        lower_fp_to_bv(
            &SmtExpr::var("x", 8).eq_expr(SmtExpr::bv_const(1, 8)),
            &[],
            &[]
        ),
        Err(FpBvDecline::NoFloatingPoint)
    );
    let fp_uf = SmtExpr::UF {
        name: "g".into(),
        args: vec![fp_of("a", 8, 24)],
        ret_sort: SmtSort::BitVec(8),
    };
    assert!(matches!(
        lower_fp_to_bv(&fp_uf.eq_expr(SmtExpr::bv_const(0, 8)), &[], &[]),
        Err(FpBvDecline::Unsupported(_))
    ));
    let quad = fp_of("a", 15, 113);
    assert!(matches!(
        lower_fp_to_bv(
            &SmtExpr::FPIsNaN {
                operand: Arc::new(quad)
            },
            &[],
            &[]
        ),
        Err(FpBvDecline::Unsupported(_))
    ));
}

/// The soundness argument, executed. For every FP obligation in the proof
/// database that lowers, and a spread of concrete inputs: evaluate the
/// original negated obligation with the crate's evaluator, give each
/// abstraction variable the pattern of the value its original term evaluates
/// to, and require the lowered formula to evaluate to the SAME truth value.
/// (Soundness needs only "original true => lowered true"; agreement both ways
/// also checks that the bit-level definitions are exact in context.)
#[test]
fn every_database_fp_obligation_lowers_to_an_exact_image_on_sampled_inputs() {
    let db = crate::proof_database::ProofDatabase::new();
    let mut rng = Rng(0x5851_f42d_4c95_7f2d);
    let (mut checked, mut lowered_count, mut skipped_points) = (0usize, 0usize, 0usize);
    for proof in db.all() {
        let ob = &proof.obligation;
        let formula = crate::ay_bridge::expand_bounded_quantifiers(&ob.negated_equivalence());
        let Ok(low) = lower_fp_to_bv(&formula, &ob.fp_inputs, &[]) else {
            continue;
        };
        lowered_count += 1;
        for point in 0..24 {
            let mut env = EvalEnv::default();
            for (name, width) in &ob.inputs {
                let mask = if *width >= 64 {
                    u64::MAX
                } else {
                    (1u64 << width) - 1
                };
                let edges = edge_patterns(
                    if *width == 64 { 11 } else { 8 },
                    if *width == 64 { 53 } else { 24 },
                );
                let value = if point < edges.len() && (*width == 32 || *width == 64) {
                    edges[(point + name.len()) % edges.len()]
                } else {
                    rng.next()
                };
                env.insert(name.clone(), value & mask);
            }
            // The original's truth under SMT-LIB semantics: every precondition
            // holds and the two sides are NOT the same value. (`try_eval`'s own
            // `Eq` compares floats with IEEE `==`, NaN != NaN; the query's `=` is
            // SMT-LIB identity, which `semantically_equal` implements.)
            let (Ok(source), Ok(machine)) = (
                ob.trust_ir_expr.try_eval(&env),
                ob.aarch64_expr.try_eval(&env),
            ) else {
                skipped_points += 1;
                continue;
            };
            if matches!(source, EvalResult::Poison) || matches!(machine, EvalResult::Poison) {
                skipped_points += 1;
                continue;
            }
            let mut original = !source.semantically_equal(&machine);
            for pre in &ob.preconditions {
                match pre.try_eval(&env) {
                    Ok(EvalResult::Bool(holds)) => original &= holds,
                    _ => {
                        skipped_points += 1;
                        continue;
                    }
                }
            }
            let mut lenv = env.clone();
            let mut complete = true;
            for (var, width, origin) in &low.abstractions {
                let bits = match origin.try_eval(&env) {
                    Ok(EvalResult::Bv(v)) => v,
                    Ok(EvalResult::Float(f)) => match width {
                        32 => u64::from((f as f32).to_bits()),
                        64 => f.to_bits(),
                        _ => {
                            complete = false;
                            break;
                        }
                    },
                    _ => {
                        complete = false;
                        break;
                    }
                };
                lenv.insert(var.clone(), bits);
            }
            if !complete {
                skipped_points += 1;
                continue;
            }
            let image = eval_bool(&low.formula, &lenv);
            assert_eq!(
                image, original,
                "{}: lowered formula disagrees with the original at {:?}",
                ob.name, env
            );
            if let Some(with_facts) = low.formula_with_conversion_facts() {
                assert_eq!(
                    eval_bool(&with_facts, &lenv),
                    original,
                    "{}: a conversion fact is false of the real conversion at {:?}",
                    ob.name,
                    env
                );
            }
            checked += 1;
        }
    }
    assert!(
        lowered_count > 200,
        "only {lowered_count} FP obligations lowered"
    );
    assert!(
        checked > lowered_count * 12,
        "only {checked} points checked over {lowered_count} obligations ({skipped_points} skipped)"
    );
}

fn width_mask(width: u32) -> u64 {
    if width >= 64 {
        u64::MAX
    } else {
        (1u64 << width) - 1
    }
}

/// `fact(arg := x, result := r)`.
fn fact_holds(fact: &SmtExpr, x: u64, r: u64) -> bool {
    let mut env = EvalEnv::default();
    env.insert("x".into(), x);
    env.insert("r".into(), r);
    eval_bool(fact, &env)
}

/// Check one conversion fact against a reference on `inputs`: it must hold
/// with the reference's answer, and whenever it pins the result at all it
/// must pin it to exactly that answer. Returns how many inputs it pinned.
fn check_fact(
    conversion: Conversion,
    arg_width: u32,
    result_width: u32,
    inputs: impl IntoIterator<Item = u64>,
    reference: impl Fn(u64) -> u64,
) -> usize {
    let fact = conversion_fact(
        conversion,
        &SmtExpr::var("x", arg_width),
        &SmtExpr::var("r", result_width),
    )
    .expect("a fact exists");
    let mut pinned = 0;
    for x in inputs {
        let want = reference(x) & width_mask(result_width);
        assert!(
            fact_holds(&fact, x, want),
            "{conversion:?} rejects the reference answer {want:#x} at {x:#x}"
        );
        let other = want ^ 1;
        if !fact_holds(&fact, x, other) {
            pinned += 1;
        }
    }
    pinned
}

#[test]
fn signed_to_fp_fact_is_the_exact_conversion_on_representable_integers() {
    // binary16 from 16/32/64-bit integers: every x with |x| <= 2^11 and a
    // margin past it, against the integer IEEE model's SCVTF.
    for width in [16u32, 32, 64] {
        let conversion = Conversion::FromSigned {
            width,
            eb: 5,
            sb: 11,
        };
        let inputs = (-2100i64..=2100).map(|x| (x as u64) & width_mask(width));
        let pinned = check_fact(conversion, width, 16, inputs, |x| {
            fp_bitmodel::scvtf(fp_bitmodel::F16, width, x)
        });
        assert_eq!(pinned, 2 * 2048 + 1, "binary16 from {width}-bit");
    }
    // binary32 / binary64: boundaries and a sample, against the host's own
    // integer-to-float conversion (exact on these inputs) and the model.
    let mut rng = Rng(0xd1b5_4a32_d192_ed03);
    let near = |bound: i64, rng: &mut Rng| -> Vec<i64> {
        let mut v: Vec<i64> = (-3..=3).flat_map(|d| [bound + d, -bound + d, d]).collect();
        v.extend((0..400).map(|_| (rng.next() as i64) % (bound + 1)));
        v
    };
    for x in near(1 << 24, &mut rng) {
        let bits = (x as u64) & width_mask(32);
        let conversion = Conversion::FromSigned {
            width: 32,
            eb: 8,
            sb: 24,
        };
        let fact =
            conversion_fact(conversion, &SmtExpr::var("x", 32), &SmtExpr::var("r", 32)).unwrap();
        let host = u64::from((x as i32 as f32).to_bits());
        assert!(fact_holds(&fact, bits, host), "binary32 {x}");
        assert_eq!(host, fp_bitmodel::scvtf(fp_bitmodel::F32, 32, bits), "{x}");
    }
    for x in near(1 << 53, &mut rng) {
        let conversion = Conversion::FromSigned {
            width: 64,
            eb: 11,
            sb: 53,
        };
        let fact =
            conversion_fact(conversion, &SmtExpr::var("x", 64), &SmtExpr::var("r", 64)).unwrap();
        let host = (x as f64).to_bits();
        assert!(fact_holds(&fact, x as u64, host), "binary64 {x}");
    }
}

#[test]
fn truncation_fact_is_fcvtz_wherever_it_pins_the_result() {
    // Every binary16 pattern, signed and unsigned, to 16/32/64 bits.
    for width in [16u32, 32, 64] {
        for signed in [true, false] {
            let conversion = Conversion::Truncate {
                eb: 5,
                sb: 11,
                width,
                signed,
            };
            let pinned = check_fact(conversion, 16, width, 0..=u64::from(u16::MAX), |p| {
                if signed {
                    fp_bitmodel::fcvtzs(fp_bitmodel::F16, width, p)
                } else {
                    fp_bitmodel::fcvtzu(fp_bitmodel::F16, width, p)
                }
            });
            // Every finite pattern whose truncation fits is pinned: all 63,488
            // finite binary16 patterns fit 32/64 bits signed; 16-bit signed
            // loses |v| >= 2^15; unsigned pins no negative |v| >= 1.
            assert!(
                pinned > 30_000,
                "binary16 -> {width}-bit signed={signed}: {pinned}"
            );
        }
    }
    // binary32 / binary64 against the host's truncating cast where in range.
    let mut rng = Rng(0x94d0_49bb_1331_11eb);
    let f32_pats = samples(8, 24, &mut rng, 3000);
    let conversion = Conversion::Truncate {
        eb: 8,
        sb: 24,
        width: 32,
        signed: true,
    };
    let fact = conversion_fact(conversion, &SmtExpr::var("x", 32), &SmtExpr::var("r", 32)).unwrap();
    for p in f32_pats {
        let v = f32::from_bits(p as u32);
        if v.is_finite() && v.trunc().abs() < 2f32.powi(31) {
            let host = u64::from(v as i32 as u32);
            assert!(fact_holds(&fact, p, host), "binary32 {v:e}");
            assert_eq!(host, fp_bitmodel::fcvtzs(fp_bitmodel::F32, 32, p));
        }
    }
    let f64_pats = samples(11, 53, &mut rng, 3000);
    let conversion = Conversion::Truncate {
        eb: 11,
        sb: 53,
        width: 64,
        signed: false,
    };
    let fact = conversion_fact(conversion, &SmtExpr::var("x", 64), &SmtExpr::var("r", 64)).unwrap();
    for p in f64_pats {
        let v = f64::from_bits(p);
        if v.is_finite() && v.trunc() >= 0.0 && v.trunc() < 2f64.powi(64) {
            let host = v as u64;
            assert!(fact_holds(&fact, p, host), "binary64 {v:e}");
        }
    }
}

#[test]
fn fp_presence_and_named_occurrence_handle_shared_dags() {
    let mut expr = SmtExpr::var("x", 64);
    for _ in 0..64 {
        let shared = std::sync::Arc::new(expr);
        expr = SmtExpr::BvAdd {
            lhs: shared.clone(),
            rhs: shared,
            width: 64,
        };
    }
    assert!(matches!(
        lower_fp_to_bv(&expr, &[], &[]),
        Err(FpBvDecline::NoFloatingPoint)
    ));
    assert!(mentions_var(&expr, "x"));
    assert!(!mentions_var(&expr, "absent"));
    let lowerer = Lowerer {
        fp_vars: HashMap::from([("x".into(), (11, 53))]),
        reserved: vec![],
        applications: vec![],
        index: HashMap::new(),
    };
    assert!(lowerer.mentions_fp(&expr));
}

#[test]
fn named_occurrence_scans_bound_uses_and_bounds_without_substitution() {
    let expr = SmtExpr::forall(
        "i",
        8,
        SmtExpr::var("lower", 8),
        SmtExpr::var("upper", 8),
        SmtExpr::var("i", 8).eq_expr(SmtExpr::bv_const(0, 8)),
    );
    for name in ["i", "lower", "upper"] {
        assert!(mentions_var(&expr, name));
    }
    assert!(!mentions_var(&expr, "absent"));
}
