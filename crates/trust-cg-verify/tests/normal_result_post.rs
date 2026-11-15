// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0
//! Actual ordinary Run applications for the shared normal-result rule.
//! Mathematical proof consumers only; no compiler or native admission.
use clean_kernel::{BinderInfo, Environment, Expr, Level, Name, TypeChecker};
use trust_ir_build::semantic_evaluation as eval;

fn z(name: &str, levels: usize, args: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string(name), vec![Level::zero(); levels]),
        args,
    )
}
fn boolean(value: bool) -> Expr {
    Expr::const_str(if value { "Bool.true" } else { "Bool.false" })
}
fn b() -> Expr {
    Expr::const_str("Bool")
}
fn n() -> Expr {
    Expr::const_str("Nat")
}
fn m() -> Expr {
    z("Option", 1, [b()])
}
fn some(value: bool) -> Expr {
    z("Option.some", 1, [b(), boolean(value)])
}
fn none() -> Expr {
    z("Option.none", 1, [b()])
}
fn status_type() -> Expr {
    z("Except", 2, [n(), b()])
}
fn raw_type() -> Expr {
    z("Prod", 2, [b(), status_type()])
}
fn pair(state: bool, status: Expr) -> Expr {
    z("Prod.mk", 2, [b(), status_type(), boolean(state), status])
}
fn ok(value: Expr) -> Expr {
    z("Except.ok", 2, [n(), b(), value])
}
fn error(code: u64) -> Expr {
    z("Except.error", 2, [n(), b(), Expr::nat_lit(code)])
}
fn eq(ty: Expr, left: Expr, right: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [ty, left, right],
    )
}
fn refl(ty: Expr, value: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [ty, value],
    )
}
fn measure() -> Expr {
    Expr::lam(
        BinderInfo::Default,
        b(),
        z("Option.some", 1, [b(), Expr::bvar(0)]),
    )
}
fn observer(expected: Expr, result: Expr) -> Expr {
    z(
        eval::NORMAL_OBSERVATION,
        1,
        [b(), n(), b(), m(), measure(), expected, result],
    )
}
fn post(expected: Expr, result: Expr) -> Expr {
    let predicate = Expr::lam(
        BinderInfo::Default,
        b(),
        Expr::lam(
            BinderInfo::Default,
            b(),
            eq(m(), Expr::app(measure(), Expr::bvar(1)), expected),
        ),
    );
    z(eval::NORMAL_POST, 1, [b(), n(), b(), predicate, result])
}
fn partial_rule(expected: Expr, result: Expr) -> Expr {
    z(
        eval::NORMAL_OBSERVATION_POST,
        1,
        [b(), n(), b(), m(), measure(), expected, result],
    )
}
fn rule(expected: Expr, result: Expr, premise: Expr) -> Expr {
    Expr::app(partial_rule(expected, result), premise)
}
fn environment() -> Environment {
    let mut env = eval::build_environment().unwrap();
    env.init_nat().unwrap();
    env.init_option().unwrap();
    eval::install_normal_post_into(&mut env).unwrap();
    let name = Name::from_string(eval::NORMAL_OBSERVATION_POST);
    assert!(env.axiom_deps(&name).is_some_and(|deps| deps.is_empty()));
    assert!(
        env.foundational_axiom_deps(&name)
            .is_some_and(|deps| deps.is_empty())
    );
    assert!(
        env.trust_marker_deps(&name)
            .is_some_and(|deps| deps.is_empty())
    );
    env
}
fn check(env: &Environment, proof: &Expr, goal: &Expr) -> Result<(), String> {
    let mut tc = TypeChecker::with_mode(env, env.mode());
    tc.set_heartbeat_limit(1_000_000);
    tc.set_max_cache_entries(eval::CACHE_ENTRY_LIMIT);
    tc.set_allow_unsafe(false);
    tc.set_allow_partial(false);
    tc.check_type(proof, goal)
        .map_err(|error| format!("{error:?}"))
}
fn accept(env: &Environment, proof: &Expr, goal: &Expr) {
    check(env, proof, goal).unwrap();
    assert!(env.audit_certification(goal, proof).issues.is_empty());
}
fn reject(env: &Environment, proof: &Expr, goal: &Expr) {
    let error = check(env, proof, goal).expect_err("changed or omitted premise must refuse");
    assert!(
        error.contains("TypeMismatch") && !error.contains("BudgetExhausted"),
        "{error}"
    );
}
fn run_type() -> Expr {
    z(eval::RUN, 1, [b(), n(), b()])
}
fn success_run() -> Expr {
    // Return a new state and retain the supplied initial state as the value.
    Expr::lam(BinderInfo::Default, b(), pair(true, ok(Expr::bvar(0))))
}
fn failed_run() -> Expr {
    Expr::lam(BinderInfo::Default, b(), pair(true, error(9)))
}

#[test]
fn actual_normal_run_post_reads_changed_returned_state_and_keeps_success_value() {
    let env = environment();
    let run = success_run();
    check(&env, &run, &run_type()).unwrap();
    let actual = Expr::app(run, boolean(false));
    let full_return = pair(true, ok(boolean(false)));
    let image = refl(raw_type(), full_return.clone());
    accept(&env, &image, &eq(raw_type(), actual.clone(), full_return));
    reject(
        &env,
        &image,
        &eq(raw_type(), actual.clone(), pair(false, ok(boolean(false)))),
    );
    reject(
        &env,
        &image,
        &eq(raw_type(), actual.clone(), pair(true, ok(boolean(true)))),
    );

    let expected = some(true);
    let premise = refl(m(), expected.clone());
    accept(
        &env,
        &premise,
        &eq(
            m(),
            observer(expected.clone(), actual.clone()),
            expected.clone(),
        ),
    );
    let proof = rule(expected.clone(), actual.clone(), premise.clone());
    accept(&env, &proof, &post(expected.clone(), actual.clone()));
    reject(&env, &proof, &post(some(false), actual.clone()));
    reject(
        &env,
        &partial_rule(expected.clone(), actual.clone()),
        &post(expected, actual.clone()),
    );
    reject(
        &env,
        &rule(some(false), actual.clone(), premise),
        &post(some(false), actual),
    );
}

#[test]
fn actual_error_run_keeps_changed_state_and_error_without_a_normal_invariant() {
    let env = environment();
    let run = failed_run();
    check(&env, &run, &run_type()).unwrap();
    let actual = Expr::app(run, boolean(false));
    let full_return = pair(true, error(9));
    let image = refl(raw_type(), full_return.clone());
    accept(&env, &image, &eq(raw_type(), actual.clone(), full_return));
    reject(
        &env,
        &image,
        &eq(raw_type(), actual.clone(), pair(false, error(9))),
    );
    reject(
        &env,
        &image,
        &eq(raw_type(), actual.clone(), pair(true, error(10))),
    );

    let expected = none();
    let premise = refl(m(), expected.clone());
    accept(
        &env,
        &premise,
        &eq(
            m(),
            observer(expected.clone(), actual.clone()),
            expected.clone(),
        ),
    );
    let proof = rule(expected.clone(), actual.clone(), premise.clone());
    accept(&env, &proof, &post(expected.clone(), actual.clone()));
    accept(
        &env,
        &Expr::const_str("True.intro"),
        &post(expected.clone(), actual),
    );
    // The fallback premise obtained on error does not establish a normal post.
    let normal = Expr::app(success_run(), boolean(false));
    reject(
        &env,
        &rule(expected.clone(), normal.clone(), premise),
        &post(expected, normal),
    );
}
