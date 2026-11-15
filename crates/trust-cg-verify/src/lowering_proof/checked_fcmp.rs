//! Checked finite evaluation of stored scalar floating-point comparisons.
//!
//! This is an interpreter/testing boundary, not source provenance or formal
//! authority. Names can select fail-closed admission, but never the predicate
//! or operand wiring evaluated here.

use super::{ProofObligation, VerificationConfig, sample_lcg_step, sample_seed};
use crate::smt::{EvalEnv, EvalResult, SmtExpr, SmtSort};
use crate::verify::VerificationResult;
use std::collections::{HashMap, HashSet};

const MAX_DEPTH: usize = 128;

/// A routing hint only, not a type checker. Every annotated BV1/Bool root
/// containing FP must reach checked admission, even when its operator is not
/// supported there. Do not use `sort()` on untrusted recursively nested Ite
/// trees: depth ambiguity is a reason to validate/refuse, not to skip checks.
fn scalar_root(expr: &SmtExpr, depth: usize) -> bool {
    if depth > MAX_DEPTH {
        return true;
    }
    match expr {
        SmtExpr::Ite {
            then_expr,
            else_expr,
            ..
        } => scalar_root(then_expr, depth + 1) || scalar_root(else_expr, depth + 1),
        SmtExpr::Var { width, .. }
        | SmtExpr::BvConst { width, .. }
        | SmtExpr::BvAdd { width, .. }
        | SmtExpr::BvSub { width, .. }
        | SmtExpr::BvMul { width, .. }
        | SmtExpr::BvSDiv { width, .. }
        | SmtExpr::BvUDiv { width, .. }
        | SmtExpr::BvURem { width, .. }
        | SmtExpr::TrapIfZero { width, .. }
        | SmtExpr::BvNeg { width, .. }
        | SmtExpr::BvAnd { width, .. }
        | SmtExpr::BvOr { width, .. }
        | SmtExpr::BvXor { width, .. }
        | SmtExpr::BvShl { width, .. }
        | SmtExpr::BvLshr { width, .. }
        | SmtExpr::BvAshr { width, .. }
        | SmtExpr::Extract { width, .. }
        | SmtExpr::Concat { width, .. }
        | SmtExpr::ZeroExtend { width, .. }
        | SmtExpr::SignExtend { width, .. }
        | SmtExpr::FPToSBv { width, .. }
        | SmtExpr::FPToUBv { width, .. }
        | SmtExpr::MemLoad {
            result_width: width,
            ..
        } => *width == 1,
        SmtExpr::BoolConst(_)
        | SmtExpr::Eq { .. }
        | SmtExpr::Not { .. }
        | SmtExpr::And { .. }
        | SmtExpr::Or { .. }
        | SmtExpr::BvSlt { .. }
        | SmtExpr::BvSge { .. }
        | SmtExpr::BvSgt { .. }
        | SmtExpr::BvSle { .. }
        | SmtExpr::BvUlt { .. }
        | SmtExpr::BvUge { .. }
        | SmtExpr::BvUgt { .. }
        | SmtExpr::BvUle { .. }
        | SmtExpr::FPEq { .. }
        | SmtExpr::FPLt { .. }
        | SmtExpr::FPLe { .. }
        | SmtExpr::FPGt { .. }
        | SmtExpr::FPGe { .. }
        | SmtExpr::FPIsNaN { .. }
        | SmtExpr::FPIsInf { .. }
        | SmtExpr::FPIsZero { .. }
        | SmtExpr::FPIsNormal { .. }
        | SmtExpr::ForAll { .. }
        | SmtExpr::Exists { .. } => true,
        SmtExpr::UF { ret_sort, .. } | SmtExpr::UFDecl { ret_sort, .. } => {
            matches!(ret_sort, SmtSort::Bool | SmtSort::BitVec(1))
        }
        SmtExpr::Select { array, .. } => scalar_array_element(array, depth + 1),
        _ => false,
    }
}

fn scalar_array_element(array: &SmtExpr, depth: usize) -> bool {
    if depth > MAX_DEPTH {
        return true;
    }
    match array {
        SmtExpr::ConstArray { value, .. } => scalar_root(value, depth + 1),
        SmtExpr::Store { array, .. } => scalar_array_element(array, depth + 1),
        SmtExpr::Ite {
            then_expr,
            else_expr,
            ..
        } => {
            scalar_array_element(then_expr, depth + 1) || scalar_array_element(else_expr, depth + 1)
        }
        SmtExpr::UF {
            ret_sort: SmtSort::Array(_, element),
            ..
        }
        | SmtExpr::UFDecl {
            ret_sort: SmtSort::Array(_, element),
            ..
        } => {
            matches!(element.as_ref(), SmtSort::Bool | SmtSort::BitVec(1))
        }
        // In particular a nested Select may still yield a scalar element.
        // Array evaluation is not admitted by checked_sort; unresolved array
        // shapes must reach that refusal rather than an identity shortcut.
        _ => true,
    }
}

/// Recognize scalar Boolean materialization without trusting width annotations.
/// In particular, a malformed BV2 0/1 result must not escape checked admission.
/// Packed all-ones masks, concatenated lanes and FP-valued muxes are different
/// routes; finding an FP node anywhere inside them is not sufficient here.
fn scalar_boolean_result(expr: &SmtExpr, depth: usize) -> bool {
    if depth > MAX_DEPTH {
        // Ambiguous over-depth candidates must reach bounded validation, not
        // fall through to an identical-tree success.
        return true;
    }
    match expr {
        SmtExpr::BoolConst(_)
        | SmtExpr::Eq { .. }
        | SmtExpr::Not { .. }
        | SmtExpr::And { .. }
        | SmtExpr::Or { .. }
        | SmtExpr::FPEq { .. }
        | SmtExpr::FPLt { .. }
        | SmtExpr::FPLe { .. }
        | SmtExpr::FPGt { .. }
        | SmtExpr::FPGe { .. }
        | SmtExpr::FPIsNaN { .. }
        | SmtExpr::FPIsInf { .. }
        | SmtExpr::FPIsZero { .. }
        | SmtExpr::FPIsNormal { .. } => true,
        SmtExpr::BvConst { value, .. } => *value <= 1,
        SmtExpr::Ite {
            then_expr,
            else_expr,
            ..
        } => {
            scalar_boolean_result(then_expr, depth + 1)
                && scalar_boolean_result(else_expr, depth + 1)
        }
        SmtExpr::BvOr { lhs, rhs, .. }
        | SmtExpr::BvAnd { lhs, rhs, .. }
        | SmtExpr::BvXor { lhs, rhs, .. } => {
            scalar_boolean_result(lhs, depth + 1) && scalar_boolean_result(rhs, depth + 1)
        }
        // A widened scalar predicate is still a comparison candidate. The
        // validator below admits only the exact BV1 -> i32 carrier pair;
        // malformed extensions must not escape via an identity shortcut.
        SmtExpr::ZeroExtend { operand, .. } => {
            scalar_root(operand, depth + 1) || scalar_boolean_result(operand, depth + 1)
        }
        _ => false,
    }
}

fn contains_fp_comparison(expr: &SmtExpr, depth: usize) -> bool {
    if depth > MAX_DEPTH {
        // A scalar Boolean candidate too deep to inspect must reach the
        // validator's bounded refusal, not an identical-tree shortcut.
        return true;
    }
    if matches!(
        expr,
        SmtExpr::FPEq { .. }
            | SmtExpr::FPLt { .. }
            | SmtExpr::FPLe { .. }
            | SmtExpr::FPGt { .. }
            | SmtExpr::FPGe { .. }
            | SmtExpr::FPIsNaN { .. }
            | SmtExpr::FPIsInf { .. }
            | SmtExpr::FPIsZero { .. }
            | SmtExpr::FPIsNormal { .. }
            | SmtExpr::BvBitsToFP { .. }
    ) {
        return true;
    }
    let mut found = false;
    expr.for_each_child(&mut |child| found |= contains_fp_comparison(child, depth + 1));
    found
}

pub(super) fn applies(obligation: &ProofObligation) -> bool {
    // These are routing hints only. A renamed valid scalar comparison is
    // recognized structurally; a renamed completely collapsed FCMP with its
    // raw-input schema must also be checked, rather than accepted as X == X.
    // a_bits/b_bits is reserved here for the converted scalar comparison
    // builders. This is not generic admission for future FP-valued arithmetic
    // using that schema; such uses need their own validated route.
    let nominal = obligation.name.starts_with("Fcmp_") || obligation.name.starts_with("FCmp_");
    let raw_schema = obligation.inputs.len() == 2
        && obligation.inputs.iter().any(|(name, _)| name == "a_bits")
        && obligation.inputs.iter().any(|(name, _)| name == "b_bits");
    nominal
        || raw_schema
        // The scalar result and FP predicate must occur in the same tree.
        // A wrong constant-zero machine mask must not reroute a wide source
        // mask away from its operand-preserving reconstruction evaluator.
        || [&obligation.trust_ir_expr, &obligation.aarch64_expr]
            .into_iter()
            .any(|expr| {
                (scalar_root(expr, 0) || scalar_boolean_result(expr, 0))
                    && contains_fp_comparison(expr, 0)
            })
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Sort {
    Bool,
    Bv(u32),
    Fp(u32, u32),
}

fn fp_sort(eb: u32, sb: u32) -> Result<Sort, String> {
    match (eb, sb) {
        (8, 24) | (11, 53) => Ok(Sort::Fp(eb, sb)),
        _ => Err(format!("unsupported IEEE format ({eb}, {sb})")),
    }
}

fn expect(actual: Sort, expected: Sort) -> Result<(), String> {
    if actual == expected {
        Ok(())
    } else {
        Err(format!(
            "sort mismatch: expected {expected:?}, got {actual:?}"
        ))
    }
}

/// Compute sorts recursively instead of trusting the cached/root sort of a
/// publicly constructible expression. Unsupported nodes refuse the bounded
/// comparison grammar, including UFs, memory, arithmetic FP and quantifiers.
fn checked_sort(
    expr: &SmtExpr,
    declarations: &HashMap<&str, u32>,
    fp_bindings: &mut HashSet<String>,
    depth: usize,
) -> Result<Sort, String> {
    if depth > MAX_DEPTH {
        return Err("comparison expression exceeds the checked depth bound".into());
    }
    let mut child = |expr: &SmtExpr| checked_sort(expr, declarations, fp_bindings, depth + 1);
    match expr {
        SmtExpr::Var { name, width } => {
            if declarations.get(name.as_str()) != Some(width) {
                return Err(format!("undeclared or width-mismatched variable {name}"));
            }
            Ok(Sort::Bv(*width))
        }
        SmtExpr::BvConst { value, width } => {
            if !(1..=64).contains(width) || (*width < 64 && *value >= (1u64 << width)) {
                return Err("invalid bitvector constant width/value".into());
            }
            Ok(Sort::Bv(*width))
        }
        SmtExpr::BoolConst(_) => Ok(Sort::Bool),
        SmtExpr::FPConst { bits, eb, sb } => {
            let sort = fp_sort(*eb, *sb)?;
            if *eb == 8 && *bits > u32::MAX as u64 {
                return Err("F32 constant contains bits outside its format".into());
            }
            Ok(sort)
        }
        SmtExpr::BvBitsToFP { operand, eb, sb } => {
            let sort = fp_sort(*eb, *sb)?;
            let SmtExpr::Var { name, .. } = operand.as_ref() else {
                return Err("comparison input must reinterpret a declared raw variable".into());
            };
            expect(child(operand)?, Sort::Bv(eb + sb))?;
            fp_bindings.insert(name.clone());
            Ok(sort)
        }
        SmtExpr::FPEq { lhs, rhs }
        | SmtExpr::FPLt { lhs, rhs }
        | SmtExpr::FPLe { lhs, rhs }
        | SmtExpr::FPGt { lhs, rhs }
        | SmtExpr::FPGe { lhs, rhs } => {
            let left = child(lhs)?;
            let right = child(rhs)?;
            if !matches!(left, Sort::Fp(_, _)) {
                return Err("floating-point comparison has a non-FP operand".into());
            }
            expect(right, left)?;
            Ok(Sort::Bool)
        }
        SmtExpr::FPIsNaN { operand }
        | SmtExpr::FPIsInf { operand }
        | SmtExpr::FPIsZero { operand }
        | SmtExpr::FPIsNormal { operand } => {
            if !matches!(child(operand)?, Sort::Fp(_, _)) {
                return Err("floating-point predicate has a non-FP operand".into());
            }
            Ok(Sort::Bool)
        }
        SmtExpr::Not { operand } => {
            expect(child(operand)?, Sort::Bool)?;
            Ok(Sort::Bool)
        }
        SmtExpr::And { lhs, rhs } | SmtExpr::Or { lhs, rhs } => {
            expect(child(lhs)?, Sort::Bool)?;
            expect(child(rhs)?, Sort::Bool)?;
            Ok(Sort::Bool)
        }
        SmtExpr::Eq { lhs, rhs } => {
            let left = child(lhs)?;
            let right = child(rhs)?;
            if matches!(left, Sort::Fp(_, _)) {
                return Err("generic FP equality is outside the checked comparison grammar".into());
            }
            expect(right, left)?;
            Ok(Sort::Bool)
        }
        SmtExpr::Ite {
            cond,
            then_expr,
            else_expr,
        } => {
            expect(child(cond)?, Sort::Bool)?;
            let then_sort = child(then_expr)?;
            expect(child(else_expr)?, then_sort)?;
            Ok(then_sort)
        }
        SmtExpr::BvAnd { lhs, rhs, width }
        | SmtExpr::BvOr { lhs, rhs, width }
        | SmtExpr::BvXor { lhs, rhs, width }
        | SmtExpr::BvAdd { lhs, rhs, width }
        | SmtExpr::BvSub { lhs, rhs, width } => {
            if !(1..=64).contains(width) {
                return Err("unsupported bitvector width in comparison".into());
            }
            expect(child(lhs)?, Sort::Bv(*width))?;
            expect(child(rhs)?, Sort::Bv(*width))?;
            Ok(Sort::Bv(*width))
        }
        SmtExpr::BvSlt { lhs, rhs, width }
        | SmtExpr::BvSge { lhs, rhs, width }
        | SmtExpr::BvSgt { lhs, rhs, width }
        | SmtExpr::BvSle { lhs, rhs, width }
        | SmtExpr::BvUlt { lhs, rhs, width }
        | SmtExpr::BvUge { lhs, rhs, width }
        | SmtExpr::BvUgt { lhs, rhs, width }
        | SmtExpr::BvUle { lhs, rhs, width } => {
            if !(1..=64).contains(width) {
                return Err("unsupported precondition bitvector width".into());
            }
            expect(child(lhs)?, Sort::Bv(*width))?;
            expect(child(rhs)?, Sort::Bv(*width))?;
            Ok(Sort::Bool)
        }
        _ => Err("unsupported node in checked scalar FP comparison".into()),
    }
}

fn validate(obligation: &ProofObligation) -> Result<Sort, String> {
    if !obligation.fp_inputs.is_empty() || !(1..=2).contains(&obligation.inputs.len()) {
        return Err(
            "comparison requires one or two raw bitvector inputs, without FP declarations".into(),
        );
    }
    let width = obligation.inputs[0].1;
    if !matches!(width, 32 | 64) {
        return Err("comparison raw inputs must be F32/F64 width".into());
    }
    let mut declarations = HashMap::new();
    for (name, declared_width) in &obligation.inputs {
        let mut chars = name.chars();
        let safe_name = chars
            .next()
            .is_some_and(|c| c.is_ascii_alphabetic() || c == '_')
            && chars.all(|c| c.is_ascii_alphanumeric() || matches!(c, '_' | '.' | '-'));
        if !safe_name
            || *declared_width != width
            || declarations.insert(name.as_str(), width).is_some()
        {
            return Err("invalid, duplicate or inconsistent raw input declarations".into());
        }
    }
    let mut bindings = HashSet::new();
    let source = if let SmtExpr::ZeroExtend {
        operand,
        extra_bits: 31,
        width: 32,
    } = &obligation.trust_ir_expr
    {
        // WebAssembly materializes its scalar comparison as i32 0/1. Admit
        // this exact carrier without stripping either stored expression or
        // widening the general result grammar to arbitrary BV32 expressions.
        let SmtExpr::Ite {
            then_expr,
            else_expr,
            ..
        } = &obligation.aarch64_expr
        else {
            return Err("i32 comparison requires the checked Boolean materialization pair".into());
        };
        if !matches!(
            then_expr.as_ref(),
            SmtExpr::BvConst {
                value: 1,
                width: 32
            }
        ) || !matches!(
            else_expr.as_ref(),
            SmtExpr::BvConst {
                value: 0,
                width: 32
            }
        ) {
            return Err("i32 comparison machine arms must be exactly 1 and 0".into());
        }
        expect(
            checked_sort(operand, &declarations, &mut bindings, 0)?,
            Sort::Bv(1),
        )?;
        expect(
            checked_sort(&obligation.aarch64_expr, &declarations, &mut bindings, 0)?,
            Sort::Bv(32),
        )?;
        Sort::Bv(32)
    } else {
        let source = checked_sort(&obligation.trust_ir_expr, &declarations, &mut bindings, 0)?;
        let machine = checked_sort(&obligation.aarch64_expr, &declarations, &mut bindings, 0)?;
        expect(machine, source)?;
        // BV1 is one comparison; BV4 is exactly one packed N:Z:C:V flag value
        // (an FCMP's complete NZCV). No other width is a comparison result.
        if source != Sort::Bv(1) && source != Sort::Bv(4) {
            return Err(
                "scalar FP comparison must produce BV1, a packed BV4 NZCV value or the \
                        exact i32 carrier pair"
                    .into(),
            );
        }
        source
    };
    if declarations.keys().any(|name| !bindings.contains(*name)) {
        return Err("declared raw input is not bound to a stored FP operand".into());
    }
    // Preconditions may constrain existing operands, but cannot make missing
    // operands in two collapsed result trees look bound.
    for precondition in &obligation.preconditions {
        expect(
            checked_sort(precondition, &declarations, &mut HashSet::new(), 0)?,
            Sort::Bool,
        )?;
    }
    Ok(source)
}

#[derive(Default, Debug)]
struct Counts {
    edge_attempts: u64,
    applicable_edges: u64,
    random_attempts: u64,
    applicable_random: u64,
}

fn unknown(reason: impl Into<String>) -> VerificationResult {
    VerificationResult::Unknown {
        reason: format!("checked FCMP: {}", reason.into()),
    }
}

/// Preserve the former IEEE value battery, and add raw signed subnormals and
/// distinct quiet/signaling NaNs. Only comparison truth values are checked;
/// native FP exceptions and NaN payload propagation are not modeled here.
pub(super) fn edge_bits(width: u32) -> Vec<u64> {
    let values = [
        0.0,
        -0.0,
        1.0,
        -1.0,
        0.5,
        -0.5,
        2.0,
        -2.0,
        0.1,
        -0.1,
        1e10,
        -1e10,
        1e-10,
        -1e-10,
        f64::INFINITY,
        f64::NEG_INFINITY,
        f64::MIN_POSITIVE,
        -f64::MIN_POSITIVE,
        f64::MAX,
        f64::MIN,
        std::f64::consts::PI,
        -std::f64::consts::PI,
        1.0 / 3.0,
        -1.0 / 3.0,
        42.0,
        -42.0,
        100.0,
        -100.0,
        0.000001,
        -0.000001,
        f64::NAN,
    ];
    let mut bits: Vec<u64> = values
        .into_iter()
        .map(|v| {
            if width == 32 {
                (v as f32).to_bits() as u64
            } else {
                v.to_bits()
            }
        })
        .collect();
    let extra: &[u64] = if width == 32 {
        &[
            f32::MIN_POSITIVE.to_bits() as u64,
            (-f32::MIN_POSITIVE).to_bits() as u64,
            f32::MAX.to_bits() as u64,
            f32::MIN.to_bits() as u64,
            1,
            0x8000_0001,
            0x007f_ffff,
            0x807f_ffff,
            0x7fc1_2345,
            0xffc2_3456,
            0x7f81_2345,
            0xff81_2346,
        ]
    } else {
        &[
            1,
            0x8000_0000_0000_0001,
            0x000f_ffff_ffff_ffff,
            0x800f_ffff_ffff_ffff,
            0x7ff8_1234_5678_9abc,
            0xfff8_2345_6789_abcd,
            0x7ff0_1234_5678_9abc,
            0xfff0_1234_5678_9abd,
        ]
    };
    for &value in extra {
        if !bits.contains(&value) {
            bits.push(value);
        }
    }
    bits
}

fn check_point(
    obligation: &ProofObligation,
    env: &EvalEnv,
    applicable: &mut u64,
    max_value: u64,
) -> Result<(), VerificationResult> {
    for precondition in &obligation.preconditions {
        match precondition.try_eval(env) {
            Ok(EvalResult::Bool(true)) => {}
            Ok(EvalResult::Bool(false)) => return Ok(()),
            other => {
                return Err(unknown(format!(
                    "precondition evaluation failed: {other:?}"
                )));
            }
        }
    }
    *applicable += 1;
    match (
        obligation.trust_ir_expr.try_eval(env),
        obligation.aarch64_expr.try_eval(env),
    ) {
        (Ok(EvalResult::Bv(t)), Ok(EvalResult::Bv(m))) if t <= max_value && m <= max_value => {
            if t == m {
                Ok(())
            } else {
                Err(VerificationResult::Invalid {
                    counterexample: format!(
                        "inputs: {env:?}, stored source={t}, stored machine={m}"
                    ),
                })
            }
        }
        (Ok(EvalResult::Bool(t)), Ok(EvalResult::Bool(m))) => {
            if t == m {
                Ok(())
            } else {
                Err(VerificationResult::Invalid {
                    counterexample: format!(
                        "inputs: {env:?}, stored source={t}, stored machine={m}"
                    ),
                })
            }
        }
        other => Err(unknown(format!(
            "stored comparison evaluation failed: {other:?}"
        ))),
    }
}

fn evaluate(
    obligation: &ProofObligation,
    config: &VerificationConfig,
    counts: &mut Counts,
) -> VerificationResult {
    let max_value = match validate(obligation) {
        Ok(Sort::Bv(4)) => 0b1111,
        Ok(_) => 1,
        Err(reason) => return unknown(reason),
    };
    let width = obligation.inputs[0].1;
    let mut env = EvalEnv::default();
    for (name, _) in &obligation.inputs {
        env.insert(name.clone(), 0);
    }
    let edges = edge_bits(width);
    for &a in &edges {
        env.set_at(0, a);
        let second = if obligation.inputs.len() == 2 {
            edges.as_slice()
        } else {
            &[0]
        };
        for &b in second {
            if obligation.inputs.len() == 2 {
                env.set_at(1, b);
            }
            counts.edge_attempts += 1;
            if let Err(result) =
                check_point(obligation, &env, &mut counts.applicable_edges, max_value)
            {
                return result;
            }
        }
    }
    let mut state = sample_seed(&obligation.name);
    for _ in 0..config.sample_count {
        for i in 0..obligation.inputs.len() {
            state = sample_lcg_step(state);
            env.set_at(
                i,
                if width == 32 {
                    state as u32 as u64
                } else {
                    state
                },
            );
        }
        counts.random_attempts += 1;
        if let Err(result) = check_point(obligation, &env, &mut counts.applicable_random, max_value)
        {
            return result;
        }
    }
    if counts.applicable_edges == 0 && counts.applicable_random == 0 {
        return unknown("no sampled input satisfied the preconditions");
    }
    // A favorable result has executed every configured random attempt. Edge
    // observations and points excluded by preconditions are tracked separately.
    debug_assert_eq!(counts.random_attempts, config.sample_count);
    VerificationResult::Valid
}

pub(super) fn verify(
    obligation: &ProofObligation,
    config: &VerificationConfig,
) -> VerificationResult {
    evaluate(obligation, config, &mut Counts::default())
}

/// Reuse the bounded comparison grammar for scalar FP-value preconditions.
pub(super) fn validate_condition(
    expr: &SmtExpr,
    declarations: &HashMap<&str, u32>,
) -> Result<(), String> {
    expect(
        checked_sort(expr, declarations, &mut HashSet::new(), 0)?,
        Sort::Bool,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lowering_proof::{all_fp_lowering_proofs, proof_fcmp_lt_f64};

    #[test]
    fn checked_fcmp_default_executes_all_random_attempts_for_all_28_rows() {
        let config = VerificationConfig::default();
        assert_eq!(config.sample_count, 100_000);
        let rows: Vec<_> = all_fp_lowering_proofs()
            .into_iter()
            .filter(|ob| ob.name.starts_with("Fcmp_"))
            .collect();
        assert_eq!(rows.len(), 28);
        let mut random_attempts = 0;
        for ob in rows {
            let start = std::time::Instant::now();
            let mut counts = Counts::default();
            assert!(
                matches!(
                    evaluate(&ob, &config, &mut counts),
                    VerificationResult::Valid
                ),
                "{}",
                ob.name
            );
            assert_eq!(counts.random_attempts, 100_000, "{}", ob.name);
            assert_eq!(counts.applicable_random, counts.random_attempts);
            assert_eq!(counts.applicable_edges, counts.edge_attempts);
            assert!(counts.edge_attempts >= 29 * 29);
            random_attempts += counts.random_attempts;
            eprintln!("{}: {counts:?}, elapsed={:?}", ob.name, start.elapsed());
        }
        assert_eq!(random_attempts, 2_800_000);
    }

    #[test]
    fn checked_fcmp_last_random_attempt_has_actual_refutation_power() {
        let config = VerificationConfig::default();
        let mut ob = proof_fcmp_lt_f64();
        let mut state = sample_seed(&ob.name);
        let mut last_a = 0;
        let mut last_b = 0;
        for _ in 0..config.sample_count {
            last_a = sample_lcg_step(state);
            last_b = sample_lcg_step(last_a);
            state = last_b;
        }
        let edges = edge_bits(64);
        assert!(!edges.contains(&last_a) || !edges.contains(&last_b));
        let last_pair = SmtExpr::var("a_bits", 64)
            .eq_expr(SmtExpr::bv_const(last_a, 64))
            .and_expr(SmtExpr::var("b_bits", 64).eq_expr(SmtExpr::bv_const(last_b, 64)));
        let source = ob.trust_ir_expr.clone();
        ob.aarch64_expr = SmtExpr::ite(
            last_pair,
            SmtExpr::bv_const(1, 1).bvsub(source.clone()),
            source,
        );
        let mut counts = Counts::default();
        assert!(matches!(
            evaluate(&ob, &config, &mut counts),
            VerificationResult::Invalid { .. }
        ));
        assert_eq!(counts.random_attempts, 100_000);
        assert_eq!(counts.applicable_random, 100_000);
    }

    /// Exactly one wider carrier is admitted: a packed 4-bit N:Z:C:V value.
    /// It is evaluated over the same edge battery and random attempts, with
    /// results bounded by 15; BV2/BV3/BV5 comparison results stay refused.
    #[test]
    fn checked_fcmp_admits_only_the_packed_nzcv_carrier_beyond_bv1() {
        let a = SmtExpr::bv_bits_to_fp(SmtExpr::var("a_bits", 32), 8, 24);
        let b = SmtExpr::bv_bits_to_fp(SmtExpr::var("b_bits", 32), 8, 24);
        let packed = |width: u32, lt_value: u64| {
            SmtExpr::ite(
                a.clone().fp_is_nan().or_expr(b.clone().fp_is_nan()),
                SmtExpr::bv_const(0b0011, width),
                SmtExpr::ite(
                    a.clone().fp_eq(b.clone()),
                    SmtExpr::bv_const(0b0110, width),
                    SmtExpr::ite(
                        a.clone().fp_lt(b.clone()),
                        SmtExpr::bv_const(lt_value, width),
                        SmtExpr::bv_const(0b0010, width),
                    ),
                ),
            )
        };
        let obligation = |width: u32, lt_value: u64| ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: format!("packed carrier probe w{width}"),
            trust_ir_expr: packed(width, 0b1000 & crate::smt::mask(u64::MAX, width)),
            aarch64_expr: packed(width, lt_value),
            inputs: vec![("a_bits".into(), 32), ("b_bits".into(), 32)],
            preconditions: vec![],
            fp_inputs: vec![],
            category: None,
        };
        let config = VerificationConfig::with_sample_count(64);
        let valid = obligation(4, 0b1000);
        assert!(applies(&valid));
        assert!(matches!(verify(&valid, &config), VerificationResult::Valid));
        // A wrong less-than flag value is refuted, not accepted as "some BV4".
        assert!(matches!(
            verify(&obligation(4, 0b1001), &config),
            VerificationResult::Invalid { .. }
        ));
        for width in [2, 3, 5] {
            assert!(
                matches!(
                    verify(
                        &obligation(width, 0b1000 & crate::smt::mask(u64::MAX, width)),
                        &config
                    ),
                    VerificationResult::Unknown { .. }
                ),
                "BV{width} must stay outside the checked comparison grammar"
            );
        }
    }

    #[test]
    fn checked_fcmp_precondition_attempts_and_applicable_pairs_are_distinct() {
        let mut ob = proof_fcmp_lt_f64();
        ob.preconditions = vec![SmtExpr::var("a_bits", 64).eq_expr(SmtExpr::var("b_bits", 64))];
        let config = VerificationConfig::with_sample_count(31);
        let mut counts = Counts::default();
        assert!(matches!(
            evaluate(&ob, &config, &mut counts),
            VerificationResult::Valid
        ));
        assert_eq!(counts.random_attempts, 31);
        assert_eq!(counts.applicable_random, 0);
        assert!(counts.applicable_edges > 0);
        assert!(counts.applicable_edges < counts.edge_attempts);
        ob.preconditions = vec![SmtExpr::bool_const(false)];
        let mut empty = Counts::default();
        assert!(matches!(
            evaluate(&ob, &config, &mut empty),
            VerificationResult::Unknown { .. }
        ));
        assert_eq!(empty.random_attempts, 31);
        assert_eq!(empty.applicable_random + empty.applicable_edges, 0);
        let mut zero = Counts::default();
        ob.preconditions.clear();
        assert!(matches!(
            evaluate(&ob, &VerificationConfig::with_sample_count(0), &mut zero),
            VerificationResult::Valid
        ));
        assert_eq!(zero.random_attempts, 0);
        assert!(zero.applicable_edges > 0);
    }

    #[test]
    fn checked_fcmp_i32_reconstruction_carriers_execute_actual_trials() {
        use crate::wasm_function_verifier::{
            reconstruct_alu_obligation, representative_reconstructable_inst,
        };
        use trust_cg_ir::WasmOpcode;
        let config = VerificationConfig::with_sample_count(23);
        let opcodes = [
            WasmOpcode::F32Eq,
            WasmOpcode::F64Eq,
            WasmOpcode::F32Ne,
            WasmOpcode::F64Ne,
            WasmOpcode::F32Lt,
            WasmOpcode::F64Lt,
            WasmOpcode::F32Gt,
            WasmOpcode::F64Gt,
            WasmOpcode::F32Le,
            WasmOpcode::F64Le,
            WasmOpcode::F32Ge,
            WasmOpcode::F64Ge,
        ];
        let mut total = 0;
        for opcode in opcodes {
            let inst = representative_reconstructable_inst(opcode).unwrap();
            let mut obligation = reconstruct_alu_obligation(&inst).unwrap();
            obligation.name = format!("renamed i32 carrier {opcode:?}");
            assert!(applies(&obligation));
            assert_eq!(validate(&obligation), Ok(Sort::Bv(32)));
            let mut counts = Counts::default();
            assert!(matches!(
                evaluate(&obligation, &config, &mut counts),
                VerificationResult::Valid
            ));
            assert_eq!(counts.random_attempts, 23);
            assert_eq!(counts.applicable_random, 23);
            total += counts.random_attempts;
        }
        assert_eq!(total, 12 * 23);
    }

    #[test]
    fn checked_fcmp_routing_leaves_fp_values_and_packed_neon_separate() {
        use crate::lowering_proof::{proof_fadd_f32, proof_fsqrt_f64};
        use crate::x86_64_lowering_proofs::{
            proof_x86_cmpsd_unord_f64, proof_x86_maxsd_f64, proof_x86_minsd_f64,
        };
        for ob in [
            proof_fadd_f32(),
            proof_fsqrt_f64(),
            proof_x86_minsd_f64(),
            proof_x86_maxsd_f64(),
            proof_x86_cmpsd_unord_f64(),
        ] {
            assert!(!applies(&ob), "{}", ob.name);
        }
        let neon = crate::neon_lowering_proofs::all_neon_fp_lanewise_proofs();
        assert!(!neon.is_empty());
        for ob in neon {
            assert!(!applies(&ob), "{}", ob.name);
        }
    }

    #[test]
    fn checked_fcmp_wide_mask_with_wrong_constant_stays_on_mask_route() {
        use crate::x86_64_lowering_proofs::proof_x86_cmpsd_unord_f64;
        for source_is_constant in [false, true] {
            let mut ob = proof_x86_cmpsd_unord_f64();
            ob.name = "renamed wide mask".into();
            if source_is_constant {
                ob.trust_ir_expr = SmtExpr::bv_const(0, 64);
            } else {
                ob.aarch64_expr = SmtExpr::bv_const(0, 64);
            }
            assert!(!applies(&ob));
        }
    }

    #[test]
    fn checked_fcmp_collapsed_renamed_and_unused_input_identities_refuse() {
        use crate::lowering_proof::{
            memoized_verify_by_evaluation, verify_by_evaluation_with_config,
            verify_fp_by_evaluation,
        };
        let config = VerificationConfig::with_sample_count(3);
        let mut ob = proof_fcmp_lt_f64();
        ob.name = "renamed constant comparison".into();
        ob.trust_ir_expr = SmtExpr::bv_const(0, 1);
        ob.aarch64_expr = ob.trust_ir_expr.clone();
        assert!(applies(&ob));
        for result in [
            verify_by_evaluation_with_config(&ob, &config),
            memoized_verify_by_evaluation(&ob, &config),
            verify_fp_by_evaluation(&ob),
        ] {
            assert!(matches!(result, VerificationResult::Unknown { .. }));
        }
        // A precondition mentioning both operands cannot provide the missing
        // binding in the stored result trees.
        ob.preconditions = vec![SmtExpr::var("a_bits", 64).eq_expr(SmtExpr::var("b_bits", 64))];
        assert!(matches!(
            verify(&ob, &config),
            VerificationResult::Unknown { .. }
        ));
    }

    #[test]
    fn checked_fcmp_deep_renamed_identity_cannot_bypass_validation() {
        use crate::lowering_proof::{
            memoized_verify_by_evaluation, verify_by_evaluation_with_config,
            verify_fp_by_evaluation,
        };
        let mut ob = proof_fcmp_lt_f64();
        ob.name = "renamed deep comparison".into();
        ob.inputs = vec![("left_raw".into(), 64), ("right_raw".into(), 64)];
        let a = SmtExpr::bv_bits_to_fp(SmtExpr::var("left_raw", 64), 11, 53);
        let b = SmtExpr::bv_bits_to_fp(SmtExpr::var("right_raw", 64), 11, 53);
        let mut tree = SmtExpr::ite(a.fp_lt(b), SmtExpr::bv_const(1, 1), SmtExpr::bv_const(0, 1));
        for _ in 0..130 {
            tree = SmtExpr::ite(SmtExpr::bool_const(true), tree, SmtExpr::bv_const(0, 1));
        }
        ob.trust_ir_expr = tree.clone();
        ob.aarch64_expr = tree;
        assert!(applies(&ob));
        let config = VerificationConfig::with_sample_count(1);
        for result in [
            verify_by_evaluation_with_config(&ob, &config),
            memoized_verify_by_evaluation(&ob, &config),
            verify_fp_by_evaluation(&ob),
        ] {
            assert!(matches!(result, VerificationResult::Unknown { .. }));
        }
    }

    #[test]
    fn checked_fcmp_scalar_wrappers_route_before_all_identity_shortcuts() {
        use crate::lowering_proof::{
            memoized_verify_by_evaluation, verify_by_evaluation_with_config,
            verify_fp_by_evaluation,
        };
        let mut ob = proof_fcmp_lt_f64();
        ob.name = "renamed scalar wrapper".into();
        ob.inputs = vec![("left_raw".into(), 64), ("right_raw".into(), 64)];
        let tree = |width| {
            let a = SmtExpr::bv_bits_to_fp(SmtExpr::var("left_raw", width), 11, 53);
            let b = SmtExpr::bv_bits_to_fp(SmtExpr::var("right_raw", 64), 11, 53);
            SmtExpr::ite(a.fp_lt(b), SmtExpr::bv_const(1, 1), SmtExpr::bv_const(0, 1))
        };
        let config = VerificationConfig::with_sample_count(19);
        let valid = SmtExpr::bv_const(1, 1).bvsub(tree(64));
        ob.trust_ir_expr = valid.clone();
        ob.aarch64_expr = valid;
        assert!(applies(&ob));
        let mut counts = Counts::default();
        assert!(matches!(
            evaluate(&ob, &config, &mut counts),
            VerificationResult::Valid
        ));
        assert_eq!(counts.random_attempts, 19);
        assert_eq!(counts.applicable_random, 19);
        for bad in [
            SmtExpr::bv_const(1, 1).bvsub(tree(63)),
            SmtExpr::bv_const(0, 1).bvadd(tree(63)),
            SmtExpr::uf("unsupported", vec![tree(64)], SmtSort::BitVec(1)),
            tree(64).bvneg(),
            tree(64).extract(0, 0),
            tree(64).zero_ext(0),
            SmtExpr::select(
                SmtExpr::select(
                    SmtExpr::uf(
                        "nested_array",
                        vec![tree(64)],
                        SmtSort::Array(
                            Box::new(SmtSort::BitVec(64)),
                            Box::new(SmtSort::Array(
                                Box::new(SmtSort::BitVec(64)),
                                Box::new(SmtSort::BitVec(1)),
                            )),
                        ),
                    ),
                    SmtExpr::bv_const(0, 64),
                ),
                SmtExpr::bv_const(0, 64),
            ),
        ] {
            ob.trust_ir_expr = bad.clone();
            ob.aarch64_expr = bad;
            assert!(applies(&ob));
            for result in [
                verify_by_evaluation_with_config(&ob, &config),
                memoized_verify_by_evaluation(&ob, &config),
                verify_fp_by_evaluation(&ob),
            ] {
                assert!(matches!(result, VerificationResult::Unknown { .. }));
            }
        }
    }
}
