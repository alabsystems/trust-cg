//! Bounded statistical evaluation of stored scalar FP value expressions.
//!
//! Raw operands retain their names and wiring. This supplies neither formal
//! proof nor source/encoding provenance. NaNs are compared as SMT FP values;
//! payload propagation and floating-point exception state are outside this model.

use super::{ProofObligation, VerificationConfig, checked_fcmp, sample_lcg_step, sample_seed};
use crate::smt::{EvalEnv, EvalResult, RoundingMode, SmtExpr};
use crate::verify::VerificationResult;
use std::collections::{HashMap, HashSet};

pub(super) fn applies(obligation: &ProofObligation) -> bool {
    // The reserved schema is only a routing hint: malformed/collapsed or
    // renamed expressions must reach validation before an identity shortcut.
    obligation
        .inputs
        .iter()
        .any(|(name, _)| name == "fp_a_bits" || name == "fp_b_bits")
        || (obligation.fp_inputs.is_empty()
            && obligation.inputs.len() <= 2
            && [&obligation.trust_ir_expr, &obligation.aarch64_expr]
                .into_iter()
                .any(|expr| value_root(expr, 0)))
}

fn value_root(expr: &SmtExpr, depth: usize) -> bool {
    if depth > 128 {
        return true;
    }
    match expr {
        SmtExpr::FPAdd { .. }
        | SmtExpr::FPSub { .. }
        | SmtExpr::FPMul { .. }
        | SmtExpr::FPDiv { .. }
        | SmtExpr::FPSqrt { .. }
        | SmtExpr::FPNeg { .. }
        | SmtExpr::FPAbs { .. }
        | SmtExpr::FPRoundToIntegral { .. }
        | SmtExpr::BvBitsToFP { .. }
        | SmtExpr::FPConst { .. } => true,
        SmtExpr::Ite {
            then_expr,
            else_expr,
            ..
        } => value_root(then_expr, depth + 1) || value_root(else_expr, depth + 1),
        _ => false,
    }
}

fn unknown(reason: impl Into<String>) -> VerificationResult {
    VerificationResult::Unknown {
        reason: format!("checked scalar FP: {}", reason.into()),
    }
}

/// Charge conditions against the same work allowance as the value trees.
/// The shared comparison validator separately checks all operator sorts.
fn condition_work(expr: &SmtExpr, depth: usize, budget: &mut usize) -> Result<(), String> {
    if depth > 128 || *budget == 0 {
        return Err("condition exceeds the checked work bound".into());
    }
    *budget -= 1;
    let mut child = |expr: &SmtExpr| condition_work(expr, depth + 1, budget);
    match expr {
        SmtExpr::BoolConst(_)
        | SmtExpr::BvConst { .. }
        | SmtExpr::FPConst { .. }
        | SmtExpr::Var { .. } => Ok(()),
        SmtExpr::Not { operand }
        | SmtExpr::BvBitsToFP { operand, .. }
        | SmtExpr::FPIsNaN { operand }
        | SmtExpr::FPIsInf { operand }
        | SmtExpr::FPIsZero { operand }
        | SmtExpr::FPIsNormal { operand } => child(operand),
        SmtExpr::Eq { lhs, rhs }
        | SmtExpr::And { lhs, rhs }
        | SmtExpr::Or { lhs, rhs }
        | SmtExpr::BvAdd { lhs, rhs, .. }
        | SmtExpr::BvSub { lhs, rhs, .. }
        | SmtExpr::BvAnd { lhs, rhs, .. }
        | SmtExpr::BvOr { lhs, rhs, .. }
        | SmtExpr::BvXor { lhs, rhs, .. }
        | SmtExpr::BvSlt { lhs, rhs, .. }
        | SmtExpr::BvSle { lhs, rhs, .. }
        | SmtExpr::BvSgt { lhs, rhs, .. }
        | SmtExpr::BvSge { lhs, rhs, .. }
        | SmtExpr::BvUlt { lhs, rhs, .. }
        | SmtExpr::BvUle { lhs, rhs, .. }
        | SmtExpr::BvUgt { lhs, rhs, .. }
        | SmtExpr::BvUge { lhs, rhs, .. }
        | SmtExpr::FPEq { lhs, rhs }
        | SmtExpr::FPLt { lhs, rhs }
        | SmtExpr::FPLe { lhs, rhs }
        | SmtExpr::FPGt { lhs, rhs }
        | SmtExpr::FPGe { lhs, rhs } => {
            child(lhs)?;
            child(rhs)
        }
        SmtExpr::Ite {
            cond,
            then_expr,
            else_expr,
        } => {
            child(cond)?;
            child(then_expr)?;
            child(else_expr)
        }
        _ => Err("unsupported node in scalar FP condition".into()),
    }
}

fn value_format(
    expr: &SmtExpr,
    declarations: &HashMap<&str, u32>,
    bindings: &mut HashSet<String>,
    depth: usize,
    budget: &mut usize,
) -> Result<u32, String> {
    if depth > 128 || *budget == 0 {
        return Err("value expression exceeds the checked work bound".into());
    }
    *budget -= 1;
    let mut child = |expr: &SmtExpr| value_format(expr, declarations, bindings, depth + 1, budget);
    match expr {
        SmtExpr::FPConst { bits, eb, sb } => match (*eb, *sb) {
            (8, 24) if *bits <= u32::MAX as u64 => Ok(32),
            (11, 53) => Ok(64),
            _ => Err("unsupported or malformed FP constant".into()),
        },
        SmtExpr::BvBitsToFP { operand, eb, sb } => {
            let width = match (*eb, *sb) {
                (8, 24) => 32,
                (11, 53) => 64,
                _ => return Err("unsupported FP input format".into()),
            };
            let SmtExpr::Var {
                name,
                width: declared_width,
            } = operand.as_ref()
            else {
                return Err("FP input must reinterpret a declared raw variable".into());
            };
            if *declared_width != width || declarations.get(name.as_str()) != Some(&width) {
                return Err(format!("undeclared or width-mismatched FP input {name}"));
            }
            bindings.insert(name.clone());
            Ok(width)
        }
        SmtExpr::FPAdd { rm, lhs, rhs }
        | SmtExpr::FPSub { rm, lhs, rhs }
        | SmtExpr::FPMul { rm, lhs, rhs }
        | SmtExpr::FPDiv { rm, lhs, rhs } => {
            if *rm != RoundingMode::RNE {
                return Err("arithmetic evaluation supports only RNE".into());
            }
            let width = child(lhs)?;
            if child(rhs)? != width {
                return Err("binary FP operands have different formats".into());
            }
            Ok(width)
        }
        SmtExpr::FPSqrt { rm, operand } => {
            if *rm != RoundingMode::RNE {
                return Err("square-root evaluation supports only RNE".into());
            }
            child(operand)
        }
        SmtExpr::FPNeg { operand }
        | SmtExpr::FPAbs { operand }
        | SmtExpr::FPRoundToIntegral { operand, .. } => child(operand),
        SmtExpr::Ite {
            cond,
            then_expr,
            else_expr,
        } => {
            condition_work(cond, depth + 1, budget)?;
            checked_fcmp::validate_condition(cond, declarations)?;
            let width = value_format(then_expr, declarations, bindings, depth + 1, budget)?;
            if value_format(else_expr, declarations, bindings, depth + 1, budget)? != width {
                return Err("FP conditional arms have different formats".into());
            }
            Ok(width)
        }
        _ => Err("unsupported node in stored scalar FP value".into()),
    }
}

fn validate(obligation: &ProofObligation) -> Result<u32, String> {
    if !obligation.fp_inputs.is_empty() || !(1..=2).contains(&obligation.inputs.len()) {
        return Err("expected one or two raw inputs without FP declarations".into());
    }
    let width = obligation.inputs[0].1;
    let mut declarations = HashMap::new();
    for (name, declared_width) in &obligation.inputs {
        let mut chars = name.chars();
        let valid_name = chars
            .next()
            .is_some_and(|c| c.is_ascii_alphabetic() || c == '_')
            && chars.all(|c| c.is_ascii_alphanumeric() || matches!(c, '_' | '.' | '-'));
        if !matches!(width, 32 | 64)
            || *declared_width != width
            || !valid_name
            || declarations.insert(name.as_str(), width).is_some()
        {
            return Err("invalid, duplicate or inconsistent raw declarations".into());
        }
    }
    let mut bindings = HashSet::new();
    let mut budget = 8192;
    for expr in [&obligation.trust_ir_expr, &obligation.aarch64_expr] {
        if value_format(expr, &declarations, &mut bindings, 0, &mut budget)? != width {
            return Err("stored result format differs from the input format".into());
        }
    }
    if declarations.keys().any(|name| !bindings.contains(*name)) {
        return Err("declared FP operand is absent from the stored expressions".into());
    }
    if obligation.preconditions.len() > 8 {
        return Err("too many scalar FP preconditions".into());
    }
    for condition in &obligation.preconditions {
        condition_work(condition, 0, &mut budget)?;
        checked_fcmp::validate_condition(condition, &declarations)?;
    }
    Ok(width)
}

fn check_point(obligation: &ProofObligation, env: &EvalEnv) -> Result<bool, VerificationResult> {
    for condition in &obligation.preconditions {
        match condition.try_eval(env) {
            Ok(EvalResult::Bool(true)) => {}
            Ok(EvalResult::Bool(false)) => return Ok(false),
            other => {
                return Err(unknown(format!(
                    "precondition evaluation failed: {other:?}"
                )));
            }
        }
    }
    match (
        obligation.trust_ir_expr.try_eval(env),
        obligation.aarch64_expr.try_eval(env),
    ) {
        (Ok(EvalResult::Float(source)), Ok(EvalResult::Float(machine))) => {
            if (source.is_nan() && machine.is_nan()) || source.to_bits() == machine.to_bits() {
                Ok(true)
            } else {
                Err(VerificationResult::Invalid {
                    counterexample: format!(
                        "inputs: {env:?}, stored source={source:?}, stored machine={machine:?}"
                    ),
                })
            }
        }
        other => Err(unknown(format!("stored FP evaluation failed: {other:?}"))),
    }
}

pub(super) fn verify(
    obligation: &ProofObligation,
    config: &VerificationConfig,
) -> VerificationResult {
    let width = match validate(obligation) {
        Ok(width) => width,
        Err(reason) => return unknown(reason),
    };
    let mut env = EvalEnv::default();
    for (name, _) in &obligation.inputs {
        env.insert(name.clone(), 0);
    }
    let edges = checked_fcmp::edge_bits(width);
    let second = if obligation.inputs.len() == 2 {
        edges.as_slice()
    } else {
        &[0]
    };
    let mut applicable = 0u64;
    for &a in &edges {
        env.set_at(0, a);
        for &b in second {
            if obligation.inputs.len() == 2 {
                env.set_at(1, b);
            }
            match check_point(obligation, &env) {
                Ok(used) => applicable += u64::from(used),
                Err(result) => return result,
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
        match check_point(obligation, &env) {
            Ok(used) => applicable += u64::from(used),
            Err(result) => return result,
        }
    }
    if applicable == 0 {
        unknown("no sampled input satisfied the preconditions")
    } else {
        VerificationResult::Valid
    }
}

#[cfg(test)]
mod tests;
