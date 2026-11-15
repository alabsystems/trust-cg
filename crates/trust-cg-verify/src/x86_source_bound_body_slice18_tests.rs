// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Slice 18: the value-numbered spelling is the canonical spelling of every
//! single-query x86-64 body theorem whose source side is `true` (OD-187),
//! its first step folding constants and the `bvsub`-zero identity (OD-188),
//! and every slice-16 part is spelled again as slice 17 spells a theorem
//! (OD-189).
//!
//! The spelling is trusted code (OD-182 and OD-183 trust it for parts and for
//! theorems with an in-bounds claim). These tests sweep it against direct
//! evaluation over every fixture of slices 1 to 17, `ArrayGep`, memory and
//! the `bool` sign extension, and over every wrong-lowering family: each
//! spelled theorem must give every sampled input the claim value the plain
//! spelling gives it, and every definition it keeps the value the plain
//! spelling's definition of that name has. The evaluator is this file's own
//! ([`exact_eval`]), written from the SMT-LIB semantics of each operator, not
//! the crate's sampler.

use super::slice22::fixture_owner;
use super::*;

// ---------------------------------------------------------------------------
// An exact evaluator (SMT-LIB semantics, widths to 128)
// ---------------------------------------------------------------------------

/// A value of [`exact_eval`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Val {
    Bool(bool),
    Bv(u128),
}

pub(crate) fn fit(value: u128, width: u32) -> u128 {
    assert!(
        (1..=128).contains(&width),
        "width {width} is outside the evaluator"
    );
    if width == 128 {
        value
    } else {
        value & ((1u128 << width) - 1)
    }
}

fn signed(value: u128, width: u32) -> i128 {
    let shift = 128 - width;
    ((value << shift) as i128) >> shift
}

/// `bvudiv` of SMT-LIB: a division by zero is all ones.
fn udiv(a: u128, b: u128, width: u32) -> u128 {
    a.checked_div(b).unwrap_or_else(|| fit(u128::MAX, width))
}

/// `bvsdiv` of SMT-LIB, through `bvudiv` of the magnitudes.
fn sdiv(a: u128, b: u128, width: u32) -> u128 {
    let negative = |v: u128| (v >> (width - 1)) & 1 == 1;
    let neg = |v: u128| fit(v.wrapping_neg(), width);
    match (negative(a), negative(b)) {
        (false, false) => udiv(a, b, width),
        (true, false) => neg(udiv(neg(a), b, width)),
        (false, true) => neg(udiv(a, neg(b), width)),
        (true, true) => udiv(neg(a), neg(b), width),
    }
}

pub(crate) fn bv(expr: &E, env: &HashMap<String, u128>, memo: &mut HashMap<*const E, Val>) -> u128 {
    match exact_eval(expr, env, memo) {
        Val::Bv(value) => value,
        Val::Bool(_) => panic!("{expr} is not a bit-vector"),
    }
}

pub(crate) fn boolean(
    expr: &E,
    env: &HashMap<String, u128>,
    memo: &mut HashMap<*const E, Val>,
) -> bool {
    match exact_eval(expr, env, memo) {
        Val::Bool(value) => value,
        Val::Bv(_) => panic!("{expr} is not Boolean"),
    }
}

/// `expr`'s value under `env` (every free name of `expr` bound), memoized by
/// node (the obligation being evaluated outlives `memo`). Panics on an
/// operator outside the body theorem's vocabulary, so a new one cannot pass
/// the sweep unevaluated.
pub(crate) fn exact_eval(
    expr: &E,
    env: &HashMap<String, u128>,
    memo: &mut HashMap<*const E, Val>,
) -> Val {
    let key = expr as *const E;
    if let Some(value) = memo.get(&key) {
        return *value;
    }
    let value = match expr {
        E::Var { name, width } => Val::Bv(fit(
            *env.get(name).unwrap_or_else(|| panic!("{name} is unbound")),
            *width,
        )),
        E::BvConst { value, width } => Val::Bv(fit(u128::from(*value), *width)),
        E::BoolConst(value) => Val::Bool(*value),
        E::BvAdd { lhs, rhs, width } => Val::Bv(fit(
            bv(lhs, env, memo).wrapping_add(bv(rhs, env, memo)),
            *width,
        )),
        E::BvSub { lhs, rhs, width } => Val::Bv(fit(
            bv(lhs, env, memo).wrapping_sub(bv(rhs, env, memo)),
            *width,
        )),
        E::BvMul { lhs, rhs, width } => Val::Bv(fit(
            bv(lhs, env, memo).wrapping_mul(bv(rhs, env, memo)),
            *width,
        )),
        E::BvUDiv { lhs, rhs, width } => {
            Val::Bv(udiv(bv(lhs, env, memo), bv(rhs, env, memo), *width))
        }
        E::BvURem { lhs, rhs, .. } => {
            let (a, b) = (bv(lhs, env, memo), bv(rhs, env, memo));
            Val::Bv(if b == 0 { a } else { a % b })
        }
        E::BvSDiv { lhs, rhs, width } => {
            Val::Bv(sdiv(bv(lhs, env, memo), bv(rhs, env, memo), *width))
        }
        E::BvNeg { operand, width } => Val::Bv(fit(bv(operand, env, memo).wrapping_neg(), *width)),
        E::BvAnd { lhs, rhs, .. } => Val::Bv(bv(lhs, env, memo) & bv(rhs, env, memo)),
        E::BvOr { lhs, rhs, .. } => Val::Bv(bv(lhs, env, memo) | bv(rhs, env, memo)),
        E::BvXor { lhs, rhs, .. } => Val::Bv(bv(lhs, env, memo) ^ bv(rhs, env, memo)),
        E::BvShl { lhs, rhs, width } => {
            let (a, b) = (bv(lhs, env, memo), bv(rhs, env, memo));
            Val::Bv(if b >= u128::from(*width) {
                0
            } else {
                fit(a << b, *width)
            })
        }
        E::BvLshr { lhs, rhs, width } => {
            let (a, b) = (bv(lhs, env, memo), bv(rhs, env, memo));
            Val::Bv(if b >= u128::from(*width) { 0 } else { a >> b })
        }
        E::BvAshr { lhs, rhs, width } => {
            let (a, b) = (signed(bv(lhs, env, memo), *width), bv(rhs, env, memo));
            let shift = b.min(u128::from(*width - 1)) as u32;
            Val::Bv(fit((a >> shift) as u128, *width))
        }
        E::Eq { lhs, rhs } => Val::Bool(exact_eval(lhs, env, memo) == exact_eval(rhs, env, memo)),
        E::Not { operand } => Val::Bool(!boolean(operand, env, memo)),
        E::And { lhs, rhs } => {
            let a = boolean(lhs, env, memo);
            let b = boolean(rhs, env, memo);
            Val::Bool(a && b)
        }
        E::Or { lhs, rhs } => {
            let a = boolean(lhs, env, memo);
            let b = boolean(rhs, env, memo);
            Val::Bool(a || b)
        }
        E::BvUlt { lhs, rhs, .. } => Val::Bool(bv(lhs, env, memo) < bv(rhs, env, memo)),
        E::BvUle { lhs, rhs, .. } => Val::Bool(bv(lhs, env, memo) <= bv(rhs, env, memo)),
        E::BvUgt { lhs, rhs, .. } => Val::Bool(bv(lhs, env, memo) > bv(rhs, env, memo)),
        E::BvUge { lhs, rhs, .. } => Val::Bool(bv(lhs, env, memo) >= bv(rhs, env, memo)),
        E::BvSlt { lhs, rhs, width } => {
            Val::Bool(signed(bv(lhs, env, memo), *width) < signed(bv(rhs, env, memo), *width))
        }
        E::BvSle { lhs, rhs, width } => {
            Val::Bool(signed(bv(lhs, env, memo), *width) <= signed(bv(rhs, env, memo), *width))
        }
        E::BvSgt { lhs, rhs, width } => {
            Val::Bool(signed(bv(lhs, env, memo), *width) > signed(bv(rhs, env, memo), *width))
        }
        E::BvSge { lhs, rhs, width } => {
            Val::Bool(signed(bv(lhs, env, memo), *width) >= signed(bv(rhs, env, memo), *width))
        }
        E::Ite {
            cond,
            then_expr,
            else_expr,
        } => {
            if boolean(cond, env, memo) {
                exact_eval(then_expr, env, memo)
            } else {
                exact_eval(else_expr, env, memo)
            }
        }
        E::Extract {
            high, low, operand, ..
        } => Val::Bv(fit(bv(operand, env, memo) >> low, high - low + 1)),
        E::Concat { hi, lo, width } => {
            let low_width = lo.bv_width();
            let (h, l) = (bv(hi, env, memo), bv(lo, env, memo));
            Val::Bv(fit((h << low_width) | l, *width))
        }
        E::ZeroExtend { operand, .. } => Val::Bv(bv(operand, env, memo)),
        E::SignExtend {
            operand,
            extra_bits,
            width,
        } => Val::Bv(fit(
            signed(bv(operand, env, memo), *width - *extra_bits) as u128,
            *width,
        )),
        other => panic!("the body theorem's vocabulary has no {other}"),
    };
    memo.insert(key, value);
    value
}

// ---------------------------------------------------------------------------
// The sweep
// ---------------------------------------------------------------------------

/// A built single-query theorem: the obligation, its free inputs, and its
/// spelling.
pub(crate) type Built = (ProofObligation, Vec<(String, u32)>, Spelling);

/// The obligation's definitions, in definition order.
pub(crate) fn definitions_of(obligation: &ProofObligation) -> Vec<(String, E)> {
    obligation
        .preconditions
        .iter()
        .rev()
        .map(|premise| match premise {
            E::Eq { lhs, rhs } => match lhs.as_ref() {
                E::Var { name, .. } => (name.clone(), rhs.as_ref().clone()),
                other => panic!("premise defines {other}"),
            },
            other => panic!("premise {other} is not a definition"),
        })
        .collect()
}

/// The claim value of `obligation` and every definition's value, for free
/// inputs `free`.
pub(crate) fn evaluate_theorem(
    obligation: &ProofObligation,
    free: &HashMap<String, u128>,
) -> (bool, HashMap<String, u128>) {
    let mut env = free.clone();
    let mut memo: HashMap<*const E, Val> = HashMap::new();
    for premise in obligation.preconditions.iter().rev() {
        let E::Eq { lhs, rhs } = premise else {
            panic!("premise {premise} is not a definition")
        };
        let E::Var { name, .. } = lhs.as_ref() else {
            panic!("premise {premise} defines no name")
        };
        let value = bv(rhs, &env, &mut memo);
        env.insert(name.clone(), value);
    }
    let holds = if obligation.trust_ir_expr == E::bool_const(true) {
        boolean(&obligation.aarch64_expr, &env, &mut memo)
    } else {
        exact_eval(&obligation.trust_ir_expr, &env, &mut memo)
            == exact_eval(&obligation.aarch64_expr, &env, &mut memo)
    };
    (holds, env)
}

/// A seeded value of a `width`-bit free input: 0, all ones, 1, a power of
/// two, the sign bit, or random bits.
pub(crate) fn sample(width: u32, state: &mut u64) -> u128 {
    let mut next = || {
        *state = state.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = *state;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    };
    let pick = next() % 10;
    let random = (u128::from(next()) << 64) | u128::from(next());
    fit(
        match pick {
            0 | 1 => 0,
            2 => u128::MAX,
            3 => 1,
            4 => 1u128 << (next() % u64::from(width)),
            5 => 1u128 << (width - 1),
            _ => random,
        },
        width,
    )
}

/// The number of samples [`sweep`] draws per theorem.
pub(crate) const SWEEP_SAMPLES: u64 = 256;

/// Sweep `spelled` against `plain` (the same pair, built without value
/// numbering): on [`SWEEP_SAMPLES`] seeded assignments of the plain
/// theorem's free inputs, the two claim values agree and every definition
/// the spelled theorem keeps has the value the plain theorem's definition of
/// that name has. Returns how many samples falsify the claims.
pub(crate) fn sweep(label: &str, plain: &Built, spelled: &Built) -> Result<usize, String> {
    let plain_free: HashMap<&str, u32> = plain.1.iter().map(|(n, w)| (n.as_str(), *w)).collect();
    for (name, width) in &spelled.1 {
        if plain_free.get(name.as_str()) != Some(width) {
            return Err(format!(
                "{label}: the spelled theorem declares {name} ({width} bits), which the plain \
                 one does not"
            ));
        }
    }
    let plain_names: HashSet<String> = definitions_of(&plain.0)
        .into_iter()
        .map(|(name, _)| name)
        .collect();
    let kept: Vec<String> = definitions_of(&spelled.0)
        .into_iter()
        .map(|(name, _)| name)
        .collect();
    if let Some(name) = kept.iter().find(|name| !plain_names.contains(*name)) {
        return Err(format!(
            "{label}: the spelled theorem defines {name}, which the plain one does not"
        ));
    }
    let mut falsified = 0;
    let mut state = label.bytes().fold(0xcbf2_9ce4_8422_2325u64, |h, b| {
        (h ^ u64::from(b)).wrapping_mul(0x0100_0000_01b3)
    });
    for round in 0..SWEEP_SAMPLES {
        let free: HashMap<String, u128> = plain
            .1
            .iter()
            .map(|(name, width)| (name.clone(), sample(*width, &mut state)))
            .collect();
        let (holds, values) = evaluate_theorem(&plain.0, &free);
        let (spelled_holds, spelled_values) = evaluate_theorem(&spelled.0, &free);
        if holds != spelled_holds {
            return Err(format!(
                "{label}: sample {round} gives the claims {holds} plainly and {spelled_holds} \
                 spelled ({free:?})"
            ));
        }
        for name in &kept {
            if values[name] != spelled_values[name] {
                return Err(format!(
                    "{label}: sample {round} gives {name} {:#x} plainly and {:#x} spelled",
                    values[name], spelled_values[name]
                ));
            }
        }
        falsified += usize::from(!holds);
    }
    Ok(falsified)
}

// ---------------------------------------------------------------------------
// The fixtures and the wrong-lowering families
// ---------------------------------------------------------------------------

/// Every correct fixture of slices 1 to 17, `ArrayGep`, the `bool` sign
/// extension and slice 20, with the machine variants the earlier slices
/// qualify: label,
/// LIR, machine stream.
pub(crate) fn every_fixture() -> Vec<(String, Function, X86ISelFunction)> {
    let mut fixtures = super::slice16::earlier_fixtures();
    for (label, source, machine) in super::machine_variants() {
        fixtures.push((format!("variant {label}"), source, machine));
    }
    for (label, source, machine) in super::commuted_variants() {
        fixtures.push((format!("commuted {label}"), source, machine));
    }
    for (label, source, machine) in super::slice5::slice_five_variants() {
        fixtures.push((format!("s5 variant {label}"), source, machine));
    }
    for (label, source, machine) in super::slice6::slice_six_variants() {
        fixtures.push((format!("s6 variant {label}"), source, machine));
    }
    for shape in super::slice16::SLICE_SIXTEEN {
        let (source, machine) = super::slice16::slice16_pair(shape);
        fixtures.push((format!("s16 {shape:?}"), source, machine));
    }
    for shape in super::slice17::SLICE_SEVENTEEN {
        let (source, machine) = super::slice17::slice17_pair(shape);
        fixtures.push((format!("s17 {shape:?}"), source, machine));
    }
    for (label, source, machine) in super::slice17::slice_seventeen_machine_variants() {
        fixtures.push((format!("s17 variant {label}"), source, machine));
    }
    for shape in super::arraygep::all_arraygep_shapes() {
        let (source, machine) = super::arraygep::arraygep_pair(shape);
        fixtures.push((format!("agep {shape:?}"), source, machine));
    }
    for shape in super::sext_bool::SEXT_BOOL {
        let (source, machine) = super::sext_bool::sext_bool_pair(shape);
        fixtures.push((format!("sext {shape:?}"), source, machine));
    }
    for shape in super::slice20::SLICE_TWENTY {
        let (source, machine) = super::slice20::slice20_pair(shape);
        fixtures.push((format!("s20 {shape:?}"), source, machine));
    }
    for variant in super::slice20::SLICE_TWENTY_VARIANTS {
        let (source, machine) = super::slice20::variant_pair(variant);
        fixtures.push((format!("s20 variant {variant:?}"), source, machine));
    }
    fixtures
}

/// Every wrong-lowering family: label, LIR, the mutated stream, and whether
/// its theorem is built without the slice-17 bound finder.
pub(crate) fn every_refutation() -> Vec<(String, Function, X86ISelFunction, bool)> {
    let mut cases: Vec<(String, Function, X86ISelFunction, bool)> = Vec::new();
    for (label, source, machine) in super::qualification_refutations() {
        cases.push((format!("s1 {label}"), source, machine, false));
    }
    for (label, source, machine) in super::memory::memory_refutations() {
        cases.push((format!("s4 {label}"), source, machine, false));
    }
    for (label, source, machine) in super::slice5::slice_five_refutations() {
        cases.push((format!("s5 {label}"), source, machine, false));
    }
    for (label, source, machine) in super::slice16::earlier_refutations() {
        cases.push((label, source, machine, false));
    }
    for (label, source, machine) in super::slice16::control_refutations() {
        cases.push((format!("s16 control {label}"), source, machine, false));
    }
    for (label, source, machine) in super::slice16::size_refutations() {
        cases.push((format!("s16 size {label}"), source, machine, false));
    }
    for (label, source, machine, unbounded) in super::slice17::slice_seventeen_refutations() {
        cases.push((format!("s17 {label}"), source, machine, unbounded));
    }
    for (label, source, machine) in super::arraygep::arraygep_refutations() {
        cases.push((format!("agep {label}"), source, machine, false));
    }
    for (label, source, machine) in super::sext_bool::sext_bool_refutations() {
        cases.push((format!("sext {label}"), source, machine, false));
    }
    // Slice 20's wrong lowerings the production owner builds (the others are
    // built in parts at every block or without the shift bound).
    for (label, source, machine, built) in super::slice20::slice_twenty_refutations() {
        if built == super::slice20::Built::Owner {
            cases.push((format!("s20 {label}"), source, machine, false));
        }
    }
    cases
}

/// The single-query theorem of a pair under `encoding` (`None` for a pair
/// stated in parts or refused), built without the affine refusal, as the
/// qualification builds a wrong lowering's theorem.
pub(crate) fn built(
    source: &Function,
    machine: &X86ISelFunction,
    encoding: PathEncoding,
    unbounded: bool,
) -> Option<Built> {
    single_theorem_with_encoding(source, machine, SYSV, encoding, unbounded)?.ok()
}

/// The plain spelling (no value numbering; slices 1 to 16, and slice 17's
/// theorems without an in-bounds claim).
pub(crate) const PLAIN: PathEncoding = PathEncoding {
    value_number: ValueNumbering::Off,
    ..PathEncoding::CANONICAL
};

/// Slice 18's cascade from its second step (OD-187: slice 17's spelling,
/// no folding) on every theorem whose source side is `true`.
pub(crate) const EVERY: PathEncoding = PathEncoding {
    value_number: ValueNumbering::Every,
    bit_moves: true,
    fold: false,
    normal: normal::Groups::NONE,
    ..PathEncoding::CANONICAL
};

/// The cascade from its second step: slice 16's part spelling (no bit
/// moves), else the plain one.
pub(crate) const EVERY_WITHOUT_BIT_MOVES: PathEncoding = PathEncoding {
    bit_moves: false,
    ..EVERY
};

// ---------------------------------------------------------------------------
// The sweep over every fixture and every wrong lowering
// ---------------------------------------------------------------------------

/// THE sweep of the canonical spelling (OD-187): every fixture's and every
/// wrong lowering's single-query theorem, in the canonical spelling and in
/// the cascade's second step (slice 16's part spelling), against the plain
/// spelling of the same pair: equal claim values and equal kept definitions
/// on every sampled input ([`sweep`]). Every spelled theorem is checked as a
/// part is, and a wrong lowering falsified on a sample stays falsified there
/// (the claim values are equal sample by sample).
#[test]
fn canonical_spelling_preserves_every_fixture_theorem() {
    let mut failures: Vec<String> = Vec::new();
    let mut counts: std::collections::BTreeMap<&str, usize> = std::collections::BTreeMap::new();
    let mut cases: Vec<(String, Function, X86ISelFunction, bool)> = every_fixture()
        .into_iter()
        .map(|(label, source, machine)| (label, source, machine, false))
        .collect();
    let fixtures = cases.len();
    cases.extend(every_refutation());
    for (k, (label, source, machine, unbounded)) in cases.iter().enumerate() {
        let wrong = k >= fixtures;
        let Some(plain) = built(source, machine, PLAIN, *unbounded) else {
            continue;
        };
        for (step, encoding) in [
            ("canonical", PathEncoding::CANONICAL),
            ("every, no folding", EVERY),
            ("every, no bit moves", EVERY_WITHOUT_BIT_MOVES),
        ] {
            if step != "canonical" && encoding == PathEncoding::CANONICAL {
                continue;
            }
            let Some(spelled) = built(source, machine, encoding, *unbounded) else {
                failures.push(format!("{label}: the {step} spelling refuses"));
                continue;
            };
            if spelled.2 == Spelling::Plain {
                *counts.entry("kept plain").or_default() += 1;
                if spelled.0 != plain.0 {
                    failures.push(format!("{label}: kept plain, yet not the plain theorem"));
                }
                continue;
            }
            if let Err(why) = check_definitional_part(&spelled.0, &spelled.1) {
                failures.push(format!("{label} ({step}): {why}"));
            }
            match sweep(&format!("{label} ({step})"), &plain, &spelled) {
                Ok(falsified) => {
                    *counts
                        .entry(if wrong { "wrong swept" } else { "swept" })
                        .or_default() += 1;
                    if falsified > 0 {
                        *counts.entry("falsified on a sample").or_default() += 1;
                    }
                }
                Err(why) => failures.push(why),
            }
        }
    }
    eprintln!("SLICE18_SWEEP {counts:?}");
    assert!(failures.is_empty(), "{}", failures.join("\n"));
    assert!(
        counts.get("swept").copied().unwrap_or(0) >= 300,
        "the sweep covers the fixtures: {counts:?}"
    );
    assert!(
        counts.get("wrong swept").copied().unwrap_or(0) >= 100,
        "the sweep covers the wrong lowerings: {counts:?}"
    );
}

// ---------------------------------------------------------------------------
// Historical custody of the goldens (as OD-134 kept the right spine's)
// ---------------------------------------------------------------------------

/// A golden snapshot file's pairs, in its order, labelled as its slice's
/// snapshot test labels them.
pub(crate) fn pairs<S: std::fmt::Debug + Copy>(
    shapes: &[S],
    pair: impl Fn(S) -> (Function, X86ISelFunction),
) -> Vec<(String, Function, X86ISelFunction)> {
    shapes
        .iter()
        .map(|&shape| {
            let (source, machine) = pair(shape);
            (format!("{shape:?}"), source, machine)
        })
        .collect()
}

/// A golden snapshot file rendered as its slice's snapshot test renders it:
/// each shape's owner, its replayed SMT2 under a `;;;; <shape>` header.
pub(crate) fn render(pairs: &[(String, Function, X86ISelFunction)]) -> String {
    let mut rendered = String::new();
    for (label, source, machine) in pairs {
        let owner =
            fixture_owner(source, machine).unwrap_or_else(|refusal| panic!("{label}: {refusal}"));
        let smt2 = generate_smt2_query_raw(owner.obligation(), &replay_config());
        rendered.push_str(&format!(";;;; {label}\n{smt2}\n"));
    }
    rendered
}

/// Every golden snapshot file: its name, its digest before slice 18 (slice
/// 17's spelling, main `190b3e53d`), and its pairs.
#[allow(clippy::type_complexity)]
pub(crate) fn golden_files() -> Vec<(
    &'static str,
    &'static str,
    Vec<(String, Function, X86ISelFunction)>,
)> {
    vec![
        (
            "snapshots.smt2",
            "f06ba2d67278e4dfc38f00479846d04213a1520654d9abdc7be0703df73f792c",
            pairs(&super::all_shapes(), super::pair),
        ),
        (
            "memory_snapshots.smt2",
            "594d8c1ed893aab8aebc2d51371422a3137e0fd992e619cf3588c32d809c3622",
            pairs(&super::memory::MEMORY_SHAPES, super::memory::memory_pair),
        ),
        (
            "slice5_snapshots.smt2",
            "2a5af3f931b56349a7cfb16d449f9785c2397060abe69854dc658fff55eca419",
            pairs(&super::slice5::SLICE_FIVE, super::slice5::slice5_pair),
        ),
        (
            "slice6_snapshots.smt2",
            "ac1853fe9522cf9597e4e57f353afb8933675fd1d57d1b2eeea75525e2d1cb88",
            pairs(&super::slice6::SLICE_SIX, super::slice6::slice6_pair),
        ),
        (
            "slice7_snapshots.smt2",
            "f5e4c539bebf4b094bef0f1d7f76497581804e35766d1047a7dbd28c618348ab",
            pairs(&super::slice7::SLICE_SEVEN, super::slice7::slice7_pair),
        ),
        (
            "slice8_snapshots.smt2",
            "ea1102610f9e752779b3a1823c7809b780e18221b71d4a326317a0236076bbfc",
            pairs(&super::slice8::SLICE_EIGHT, super::slice8::slice8_pair),
        ),
        (
            "slice9_snapshots.smt2",
            "394a3d17a4e793e05b7f569050e6851b5c030b8fc1545afd61ca80babd7e9dbc",
            pairs(&super::slice9::SLICE_NINE, super::slice9::slice9_pair),
        ),
        (
            "slice10_snapshots.smt2",
            "668d5f6b65cddd23f2fcd2bbfd9a9a9f57a5dad9ae9d7e932170841d78d7e791",
            pairs(&super::slice10::SLICE_TEN, super::slice10::slice10_pair),
        ),
        (
            "slice11_snapshots.smt2",
            "f4aa144e7903262f3935bcf9066d9b1d1c1b9cc6a94a478f7a8955380bd29e45",
            pairs(&super::slice11::SLICE_ELEVEN, super::slice11::slice11_pair),
        ),
        (
            "slice12_snapshots.smt2",
            "6ecce29f4268a80e31b0387ec4a9171bb647ab19bdd7912365fc53e2c9836276",
            pairs(&super::slice12::SLICE_TWELVE, super::slice12::slice12_pair),
        ),
        (
            "slice13_snapshots.smt2",
            "f8f924fe224267fccea7de3a75406a3b2c1c717d577e1179bdb3d53f323ab2b3",
            pairs(
                &super::slice13::SLICE_THIRTEEN,
                super::slice13::slice13_pair,
            ),
        ),
        (
            "slice14_snapshots.smt2",
            "6f1e3a64a1fa7d76e6a51a845f5ef8fb00faa02df6ae0fbd7b4e2b1626e892a7",
            pairs(
                &super::slice14::SLICE_FOURTEEN,
                super::slice14::slice14_pair,
            ),
        ),
        (
            "slice15_snapshots.smt2",
            "15d951964213b6c0ae9ba1901ee4992c06e290b8b3d8b8d033c80f83e0898b53",
            pairs(&super::slice15::SLICE_FIFTEEN, super::slice15::slice15_pair),
        ),
        (
            "arraygep_snapshots.smt2",
            "4616eedc1b3e15609a1e42a28799c5cef855d726488f99ee0ff62ca9a98a9bc7",
            pairs(&super::arraygep::ARRAY_GEP, super::arraygep::arraygep_pair),
        ),
    ]
}

/// Historical custody: the test-only legacy spelling (slice 17's: only a
/// theorem with an in-bounds claim value-numbered, no cascade, two claims at
/// least) re-renders every golden file as it was before slice 18, byte for
/// byte, so each old digest stays reproducible; and the canonical rendering
/// is the committed golden (each slice's own snapshot test pins its new
/// digest). Prints, per file, how many theorems the canonical spelling
/// changes.
#[test]
fn the_legacy_spelling_reproduces_every_golden_before_slice_eighteen() {
    use sha2::{Digest, Sha256};
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/x86_source_bound_body");
    // The slice-16 size shapes' parts (their golden, added by slice 18, at
    // its digest before OD-189 re-spelled them).
    // Every historical rendering selects as the selector did then, every
    // constant `I128` shift on the general path (OD-215 came later).
    let legacy = super::with_i128_const_shift_fold(false, || {
        with_legacy_spelling(super::slice16::slice_sixteen_parts_snapshots)
    });
    assert_eq!(
        format!("{:x}", Sha256::digest(legacy.as_bytes())),
        "acfc09b8d46eb3067ee50c5cb3bf39f0a531d12a138d7d9ed638418e5c1fdb8f",
        "slice16_parts_snapshots.smt2: the legacy spelling no longer renders slice 16's parts"
    );
    let canonical = super::slice16::slice_sixteen_parts_snapshots();
    let committed = std::fs::read_to_string(dir.join("slice16_parts_snapshots.smt2")).unwrap();
    assert_eq!(
        canonical, committed,
        "slice16_parts_snapshots.smt2: the canonical rendering drifted"
    );
    eprintln!(
        "SLICE18_CUSTODY file=slice16_parts_snapshots.smt2 parts_changed={} canonical_sha256={:x}",
        legacy != canonical,
        Sha256::digest(canonical.as_bytes())
    );
    let legacy_files = super::with_i128_const_shift_fold(false, golden_files);
    for ((file, legacy_digest, fixtures), (_, _, legacy_fixtures)) in
        golden_files().into_iter().zip(legacy_files)
    {
        // Before OD-224 a `mul` row's CF/OF were spelled from the product term.
        let legacy =
            with_mul_flag_of_the_term(|| with_legacy_spelling(|| render(&legacy_fixtures)));
        assert_eq!(
            format!("{:x}", Sha256::digest(legacy.as_bytes())),
            legacy_digest,
            "{file}: the legacy spelling no longer renders the golden before slice 18"
        );
        let canonical = render(&fixtures);
        let committed = std::fs::read_to_string(dir.join(file)).unwrap();
        assert_eq!(
            canonical, committed,
            "{file}: the canonical rendering drifted"
        );
        let old = super::snapshot_sections(&legacy);
        let new = super::snapshot_sections(&canonical);
        assert_eq!(old.len(), new.len(), "{file}");
        let changed = old.iter().zip(&new).filter(|(a, b)| a != b).count();
        // Each theorem's spelling: slice 17's, slice 16's part spelling (the
        // cascade's second step), or plain; a plain one is conjunctive (its
        // source side `true`) or one-path.
        let mut spellings: std::collections::BTreeMap<&str, usize> =
            std::collections::BTreeMap::new();
        for (label, source, machine) in &fixtures {
            let key = match single_theorem_with_encoding(
                source,
                machine,
                SYSV,
                PathEncoding::CANONICAL,
                false,
            ) {
                None => "in parts",
                Some(Err(refusal)) => panic!("{label}: {refusal}"),
                Some(Ok((obligation, _, spelling))) => match spelling {
                    Spelling::Normal => "normal",
                    Spelling::Folded => "folded",
                    Spelling::BitMoves => "bit moves",
                    Spelling::Numbered => "parts spelling",
                    Spelling::Plain if obligation.trust_ir_expr == E::bool_const(true) => {
                        "plain conjunctive"
                    }
                    Spelling::Plain => "one path",
                },
            };
            *spellings.entry(key).or_default() += 1;
        }
        eprintln!(
            "SLICE18_CUSTODY file={file} theorems={} changed={changed} spellings={spellings:?} \
             legacy_sha256={legacy_digest} canonical_sha256={:x}",
            old.len(),
            Sha256::digest(canonical.as_bytes())
        );
    }
}

// ---------------------------------------------------------------------------
// OD-188: constant folding and the `bvsub`-zero identity, against evaluation
// ---------------------------------------------------------------------------

/// Constants of `width` bits a [`E::BvConst`] holds: 0, 1, all ones, the
/// sign bit, and seeded random values (each below 2^64).
fn sample_constants(width: u32, state: &mut u64) -> Vec<u64> {
    let cap = if width >= 64 {
        u128::from(u64::MAX)
    } else {
        (1u128 << width) - 1
    };
    let mut values = vec![0, 1, cap as u64];
    if width <= 64 {
        values.push((1u128 << (width - 1)) as u64);
    }
    for _ in 0..6 {
        *state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1);
        values.push(((u128::from(*state ^ (*state >> 29))) & cap) as u64);
    }
    values.push(u64::from(width));
    values.push(u64::from(width).saturating_sub(1));
    values.sort_unstable();
    values.dedup();
    values
        .into_iter()
        .filter(|v| u128::from(*v) <= cap)
        .collect()
}

/// Every operator OD-188 folds, at every width it is stated at in the body
/// theorem (1 to 128 bits) and over sampled constants: the fold is either
/// refused (a value no [`E::BvConst`] holds) or the constant the exact
/// evaluator ([`exact_eval`]) gives the unfolded node; every operator folds
/// at least once; and an `ite`, a Boolean connective, an equation of two
/// equal constants and a node with a variable operand are never folded.
#[test]
fn every_constant_fold_is_the_value_of_its_operator() {
    use std::collections::BTreeMap;
    type Build = fn(E, E) -> E;
    let binary: &[(&str, Build)] = &[
        ("bvadd", |a, b| a.bvadd(b)),
        ("bvsub", |a, b| a.bvsub(b)),
        ("bvmul", |a, b| a.bvmul(b)),
        ("bvand", |a, b| a.bvand(b)),
        ("bvor", |a, b| a.bvor(b)),
        ("bvxor", |a, b| a.bvxor(b)),
        ("bvshl", |a, b| a.bvshl(b)),
        ("bvlshr", |a, b| a.bvlshr(b)),
        ("bvashr", |a, b| a.bvashr(b)),
        ("bvudiv", |a, b| a.bvudiv(b)),
        ("bvurem", |a, b| a.bvurem(b)),
        ("bvsdiv", |a, b| a.bvsdiv(b)),
        ("bvult", |a, b| a.bvult(b)),
        ("bvule", |a, b| a.bvule(b)),
        ("bvugt", |a, b| a.bvugt(b)),
        ("bvuge", |a, b| a.bvuge(b)),
        ("bvslt", |a, b| a.bvslt(b)),
        ("bvsle", |a, b| a.bvsle(b)),
        ("bvsgt", |a, b| a.bvsgt(b)),
        ("bvsge", |a, b| a.bvsge(b)),
        ("=", |a, b| a.eq_expr(b)),
        ("concat", |a, b| a.concat(b)),
    ];
    let mut folds: BTreeMap<String, usize> = BTreeMap::new();
    let mut state = 0x5851_f42d_4c95_7f2du64;
    let env: HashMap<String, u128> = HashMap::new();
    let check = |node: &E, label: &str, folds: &mut BTreeMap<String, usize>| {
        let Some(folded) = split::fold_constant(node) else {
            return;
        };
        let mut memo = HashMap::new();
        let want = exact_eval(node, &env, &mut memo);
        let mut memo = HashMap::new();
        let got = exact_eval(&folded, &env, &mut memo);
        assert!(
            matches!(folded, E::BvConst { .. } | E::BoolConst(_)),
            "{label}: {node} folds to {folded}, no constant"
        );
        assert_eq!(got, want, "{label}: {node} folds to {folded}");
        if !matches!(node, E::BvConst { .. } | E::BoolConst(_)) {
            *folds.entry(label.to_owned()).or_default() += 1;
        }
    };
    for width in [1u32, 7, 8, 16, 31, 32, 56, 63, 64, 65, 127, 128] {
        let values = sample_constants(width, &mut state);
        for (name, build) in binary {
            if *name == "concat" && width > 64 {
                continue;
            }
            for &a in &values {
                for &b in &values {
                    let node = build(E::bv_const(a, width), E::bv_const(b, width));
                    check(&node, name, &mut folds);
                }
            }
        }
        for &a in &values {
            let constant = E::bv_const(a, width);
            check(&constant.clone().bvneg(), "bvneg", &mut folds);
            if width <= 64 {
                check(&constant.clone().zero_ext(64), "zero_extend", &mut folds);
                check(&constant.clone().sign_ext(64), "sign_extend", &mut folds);
            }
            for (high, low) in [(width - 1, 0), (width / 2, 0), (width - 1, width / 2)] {
                check(&constant.clone().extract(high, low), "extract", &mut folds);
            }
        }
    }
    for (name, _) in binary {
        assert!(
            folds.get(*name).copied().unwrap_or(0) > 0,
            "{name} never folds: {folds:?}"
        );
    }
    for name in ["bvneg", "zero_extend", "sign_extend", "extract"] {
        assert!(
            folds.get(name).copied().unwrap_or(0) > 0,
            "{name} never folds: {folds:?}"
        );
    }
    let x = E::var("x", 64);
    let one = E::bv_const(1, 64);
    for unfolded in [
        E::ite(E::bool_const(true), one.clone(), one.clone()),
        E::bool_const(true).and_expr(E::bool_const(false)),
        E::bool_const(true).not_expr(),
        one.clone().eq_expr(one.clone()),
        x.clone().bvadd(one.clone()),
    ] {
        assert!(
            split::fold_constant(&unfolded).is_none(),
            "{unfolded} is folded"
        );
    }
}

/// The `bvsub`-zero identity holds on every sampled input, either way round
/// and at every width; a difference compared with zero through an extract
/// (only its low bits) is never rewritten to an equation of the operands
/// (wrong when they differ above the extract), nor one compared with another
/// constant; and the folded term is the unfolded one on every sample, for
/// terms where the identity and the folds nest.
#[test]
fn the_bvsub_zero_identity_is_exact() {
    let mut state = 0x2545_f491_4f6c_dd1du64;
    let mut terms: Vec<E> = Vec::new();
    for width in [1u32, 8, 32, 64, 128] {
        let (x, y) = if width == 128 {
            (E::var("x", 64).zero_ext(64), E::var("y", 64).sign_ext(64))
        } else {
            (
                E::var("x", 64).extract(width - 1, 0),
                E::var("y", 64).extract(width - 1, 0),
            )
        };
        let zero = E::bv_const(0, width);
        terms.push(x.clone().bvsub(y.clone()).eq_expr(zero.clone()));
        terms.push(zero.clone().eq_expr(x.clone().bvsub(y.clone())));
        // A difference compared with another constant is no equation of the
        // operands.
        terms.push(x.clone().bvsub(y.clone()).eq_expr(E::bv_const(1, width)));
        terms.push(
            x.clone()
                .bvsub(E::bv_const(3, width).bvadd(E::bv_const(4, width)))
                .eq_expr(zero.clone()),
        );
        terms.push(
            E::ite(
                x.clone().bvsub(y.clone()).eq_expr(zero.clone()),
                E::bv_const(1, 1),
                E::bv_const(0, 1),
            )
            .eq_expr(E::bv_const(1, 1)),
        );
    }
    let narrowed = E::var("x", 64)
        .bvsub(E::var("y", 64))
        .extract(7, 0)
        .eq_expr(E::bv_const(0, 8));
    terms.push(narrowed.clone());
    assert_ne!(
        split::folded(&narrowed),
        E::var("x", 64).eq_expr(E::var("y", 64)),
        "a difference compared through an extract is no equation of its operands"
    );
    let rewritten = split::folded(&terms[0]);
    assert!(
        matches!(&rewritten, E::Eq { lhs, .. } if !matches!(lhs.as_ref(), E::BvSub { .. })),
        "{} is rewritten: {rewritten}",
        terms[0]
    );
    for term in &terms {
        let folded = split::folded(term);
        for round in 0..512u64 {
            state = state
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1);
            let x = u128::from(state);
            let y = match round % 5 {
                0 => x,
                1 => x ^ 0x100,
                2 => x.wrapping_add(1) & u128::from(u64::MAX),
                3 => x.wrapping_sub(1) & u128::from(u64::MAX),
                _ => u128::from(state.rotate_left(13)),
            };
            let env: HashMap<String, u128> = [("x".to_owned(), x), ("y".to_owned(), y)]
                .into_iter()
                .collect();
            let (mut a, mut b) = (HashMap::new(), HashMap::new());
            assert_eq!(
                exact_eval(term, &env, &mut a),
                exact_eval(&folded, &env, &mut b),
                "{term} and {folded} differ at x {x:#x} y {y:#x}"
            );
        }
    }
}

// ---------------------------------------------------------------------------
// The normalizers on random terms, against evaluation
// ---------------------------------------------------------------------------

/// A seeded generator of the terms the body theorem's spelling rewrites.
struct Terms {
    state: u64,
}

impl Terms {
    fn next(&mut self) -> u64 {
        self.state = self.state.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.state;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }

    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }

    /// A constant of `width` bits (at most 64: a constant field's width).
    fn constant(&mut self, width: u32) -> E {
        let value = match self.below(4) {
            0 => 0,
            1 => 1,
            2 => u64::MAX,
            _ => self.next(),
        };
        E::bv_const(value, width)
    }

    /// A random `width`-bit term over `vars` (each `(name, width)`), at
    /// most `depth` operators deep: variables' bits, constants, extracts
    /// (of extracts, of extensions, of constants), extensions,
    /// concatenations (of adjacent extracts of one term, and of two terms),
    /// arithmetic, logic, an `ite` on an equation and a `bvsub` compared
    /// with zero.
    fn term(&mut self, width: u32, depth: u32, vars: &[(String, u32)]) -> E {
        if depth == 0 || self.below(5) == 0 {
            if width > 64 {
                // No leaf is this wide: two leaves side by side.
                let hi = self.term(width - 64, 0, vars);
                let lo = self.term(64, 0, vars);
                return hi.concat(lo);
            }
            let fitting: Vec<(String, u32)> =
                vars.iter().filter(|(_, w)| *w >= width).cloned().collect();
            if fitting.is_empty() || self.below(3) == 0 {
                return self.constant(width);
            }
            let (name, var_width) = fitting[self.below(fitting.len() as u64) as usize].clone();
            let var = E::var(name, var_width);
            if var_width == width {
                return var;
            }
            let low = self.below(u64::from(var_width - width + 1)) as u32;
            return var.extract(low + width - 1, low);
        }
        let narrower = |terms: &mut Self| 1 + terms.below(u64::from(width.max(2) - 1)) as u32;
        match self.below(11) {
            0 if width < 128 => {
                // An extract of a wider term (an extract, an extension or a
                // constant among them, as the bit moves write).
                let wider = width + 1 + self.below(u64::from((128 - width).min(64))) as u32;
                let low = self.below(u64::from(wider - width + 1)) as u32;
                self.term(wider, depth - 1, vars)
                    .extract(low + width - 1, low)
            }
            1 if width > 1 => {
                let inner = narrower(self);
                let operand = self.term(inner, depth - 1, vars);
                if self.below(2) == 0 {
                    operand.zero_ext(width - inner)
                } else {
                    operand.sign_ext(width - inner)
                }
            }
            2 if width > 1 => {
                // Adjacent extracts of one term, or of two terms of one width.
                let source_width = width + self.below(u64::from(129 - width)) as u32;
                let base = self.below(u64::from(source_width - width + 1)) as u32;
                let split = 1 + self.below(u64::from(width - 1)) as u32;
                let a = self.term(source_width, depth - 1, vars);
                let b = if self.below(2) == 0 {
                    a.clone()
                } else {
                    self.term(source_width, depth - 1, vars)
                };
                let hi = a.extract(base + width - 1, base + split);
                let lo = b.extract(base + split - 1, base);
                hi.concat(lo)
            }
            3 if width > 1 => {
                let high_width = narrower(self);
                let hi = self.term(high_width, depth - 1, vars);
                let lo = self.term(width - high_width, depth - 1, vars);
                hi.concat(lo)
            }
            4 => {
                let a = self.term(width, depth - 1, vars);
                let b = self.term(width, depth - 1, vars);
                a.bvadd(b)
            }
            5 => {
                let a = self.term(width, depth - 1, vars);
                let b = self.term(width, depth - 1, vars);
                a.bvsub(b)
            }
            6 => {
                let a = self.term(width, depth - 1, vars);
                let b = self.term(width, depth - 1, vars);
                if self.below(2) == 0 {
                    a.bvand(b)
                } else {
                    a.bvxor(b)
                }
            }
            7 => {
                let a = self.term(width, depth - 1, vars);
                let b = self.term(width, depth - 1, vars);
                a.bvmul(b)
            }
            8 => {
                let compared = narrower(self).min(64);
                let x = self.term(compared, depth - 1, vars);
                let y = self.term(compared, depth - 1, vars);
                let condition = if self.below(2) == 0 {
                    x.eq_expr(y)
                } else {
                    x.bvsub(y).eq_expr(E::bv_const(0, compared))
                };
                E::ite(
                    condition,
                    self.term(width, depth - 1, vars),
                    self.term(width, depth - 1, vars),
                )
            }
            9 => {
                let a = self.term(width, depth - 1, vars);
                let b = if width <= 64 {
                    self.constant(width)
                } else {
                    self.term(width, depth - 1, vars)
                };
                if self.below(2) == 0 {
                    a.bvlshr(b)
                } else {
                    a.bvshl(b)
                }
            }
            _ => self.term(width, depth - 1, vars),
        }
    }
}

/// Every normalizer the spelling applies is exact on random terms: on 4000
/// seeded terms of widths 1 to 128 over three variables, `bit_normalized`,
/// `bit_moves_normalized` and `folded` each give a term of the same width
/// whose value is the original's on 32 seeded inputs, and each rewrites a
/// share of them (so the sweep exercises its rules: adjacent extracts of one
/// term and of two terms, extracts of extracts, extensions and constants,
/// folds of constants, the `bvsub`-zero identity).
#[test]
fn the_normalizers_are_exact_on_random_terms() {
    type Normalizer = fn(&E) -> E;
    let normalizers: [(&str, Normalizer); 3] = [
        ("bit_normalized", split::bit_normalized),
        ("bit_moves_normalized", split::bit_moves_normalized),
        ("folded", split::folded),
    ];
    let vars = vec![
        ("x".to_owned(), 64),
        ("y".to_owned(), 64),
        ("z".to_owned(), 8),
    ];
    let mut terms = Terms {
        state: 0x6a09_e667_f3bc_c909,
    };
    let mut rewritten = [0usize; 3];
    let mut failures = Vec::new();
    for round in 0..4000u32 {
        let width = [1, 7, 8, 16, 31, 32, 56, 64, 65, 96, 128][(round % 11) as usize];
        let term = terms.term(width, 4, &vars);
        let inputs: Vec<HashMap<String, u128>> = (0..32)
            .map(|_| {
                vars.iter()
                    .map(|(name, width)| {
                        let value = match terms.below(5) {
                            0 => 0,
                            1 => u128::MAX,
                            _ => u128::from(terms.next()),
                        };
                        (name.clone(), fit(value, *width))
                    })
                    .collect()
            })
            .collect();
        for (k, (name, normalize)) in normalizers.iter().enumerate() {
            let normal = normalize(&term);
            if normal != term {
                rewritten[k] += 1;
            }
            if normal.bv_width() != term.bv_width() {
                failures.push(format!("{name} changes the width of {term}"));
                continue;
            }
            for env in &inputs {
                let (mut a, mut b) = (HashMap::new(), HashMap::new());
                if exact_eval(&term, env, &mut a) != exact_eval(&normal, env, &mut b) {
                    failures.push(format!("{name}: {term} and {normal} differ at {env:?}"));
                    break;
                }
            }
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
    for (k, (name, _)) in normalizers.iter().enumerate() {
        assert!(
            rewritten[k] >= 200,
            "{name} rewrites only {} terms",
            rewritten[k]
        );
    }
}

/// `folded` spells an unsigned division or remainder by a constant power of
/// two as its shift or mask, leaving no division node, and leaves one by any
/// other constant, by zero or by a variable a division: at widths 1 to 128,
/// with a dividend that is a variable or a compound term, the folded term's
/// value is the original's on seeded inputs (zero, all ones and random). A
/// divisor a substituted definition makes constant (OD-233) is the case the
/// rule is for: AY build 13556 bit-blasts `(bvudiv s (_ bv1 64))` as a
/// division circuit (the 2026-11-07 G-SEFRT measurement).
#[test]
fn the_fold_spells_a_division_by_a_power_of_two_as_its_shift_or_mask() {
    fn divides(expr: &E) -> bool {
        let mut stack = vec![expr];
        while let Some(node) = stack.pop() {
            if matches!(node, E::BvUDiv { .. } | E::BvURem { .. }) {
                return true;
            }
            node.for_each_child(&mut |child| stack.push(child));
        }
        false
    }
    let mut terms = Terms {
        state: 0x3c6e_f372_fe94_f82b,
    };
    let mut failures = Vec::new();
    let (mut spelled, mut kept) = (0usize, 0usize);
    for width in [1u32, 7, 8, 16, 32, 63, 64, 65, 96, 128] {
        let (x, y) = (format!("x{width}"), format!("y{width}"));
        let dividends = [
            E::var(&x, width),
            E::var(&x, width).bvxor(E::var(&y, width)),
        ];
        let top = width.min(64);
        let mut powers: Vec<u64> = vec![1];
        powers.extend((1..top).map(|k| 1u64 << k));
        let mut others: Vec<u64> = vec![0, 3, 6, 5 << (top.saturating_sub(4))];
        others.retain(|k| *k == 0 || crate::smt::mask(*k, top) == *k);
        others.retain(|k| !k.is_power_of_two());
        if top >= 2 {
            others.push(crate::smt::mask(u64::MAX, top));
        }
        let inputs: Vec<HashMap<String, u128>> = (0..24)
            .map(|round| {
                let pick = |terms: &mut Terms| match round % 4 {
                    0 => 0,
                    1 => u128::MAX,
                    _ => (u128::from(terms.next()) << 64) | u128::from(terms.next()),
                };
                let (a, b) = (pick(&mut terms), pick(&mut terms));
                HashMap::from([(x.clone(), fit(a, width)), (y.clone(), fit(b, width))])
            })
            .collect();
        for dividend in &dividends {
            for (divisor, power) in powers
                .iter()
                .map(|k| (*k, true))
                .chain(others.iter().map(|k| (*k, false)))
            {
                for remainder in [false, true] {
                    let d = E::bv_const(divisor, width);
                    let term = if remainder {
                        dividend.clone().bvurem(d)
                    } else {
                        dividend.clone().bvudiv(d)
                    };
                    let folded = split::folded(&term);
                    if folded.bv_width() != width {
                        failures.push(format!("{term} folds to {folded} of another width"));
                        continue;
                    }
                    if power == divides(&folded) {
                        failures.push(format!(
                            "{term} folds to {folded}: a division by {divisor} must {}",
                            if power { "be spelled away" } else { "stay" }
                        ));
                    }
                    if power {
                        spelled += 1;
                    } else {
                        kept += 1;
                    }
                    for env in &inputs {
                        let (mut a, mut b) = (HashMap::new(), HashMap::new());
                        if exact_eval(&term, env, &mut a) != exact_eval(&folded, env, &mut b) {
                            failures.push(format!("{term} and {folded} differ at {env:?}"));
                            break;
                        }
                    }
                }
            }
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
    assert!(
        spelled >= 1000 && kept >= 60,
        "spelled {spelled}, kept {kept}"
    );
}

/// The definition-level steps are exact on random definitions: random
/// definitions over three variables and the earlier names (renamings,
/// constants, repeated right-hand sides, bit moves and computations among
/// them) and random claims, spelled by `substitute_bit_moves`,
/// `unify_definitions` and (OD-188) `folded_spelling`, keep every claim's
/// value and every kept definition's value on 32 seeded inputs.
#[test]
fn the_definition_steps_are_exact_on_random_definitions() {
    let vars = vec![
        ("x".to_owned(), 64),
        ("y".to_owned(), 64),
        ("z".to_owned(), 8),
    ];
    let mut terms = Terms {
        state: 0xbb67_ae85_84ca_a73b,
    };
    let mut failures = Vec::new();
    let mut spelled = 0;
    for round in 0..600u32 {
        let mut scope = vars.clone();
        let mut definitions: Vec<(String, E)> = Vec::new();
        for k in 0..(4 + round % 9) {
            let width = [8u32, 16, 32, 64][terms.below(4) as usize];
            let expr = match terms.below(5) {
                // A renaming or a repeated right-hand side.
                0 if !definitions.is_empty() => {
                    let (name, earlier) =
                        definitions[terms.below(definitions.len() as u64) as usize].clone();
                    if terms.below(2) == 0 {
                        E::var(name, earlier.bv_width())
                    } else {
                        earlier
                    }
                }
                _ => terms.term(width, 3, &scope),
            };
            let name = format!("d{k}");
            scope.push((name.clone(), expr.bv_width()));
            definitions.push((name, expr));
        }
        let claim_terms: Vec<E> = (0..3)
            .map(|_| {
                let (name, width) = scope[terms.below(scope.len() as u64) as usize].clone();
                let other = terms.term(width, 2, &scope);
                E::var(name, width).eq_expr(other)
            })
            .collect();
        let claims = claim_terms
            .into_iter()
            .rev()
            .reduce(|tail, claim| claim.and_expr(tail))
            .expect("three claims");
        type Spelling = (Vec<(String, E)>, E);
        let mut spellings: Vec<(&str, Option<Spelling>)> = vec![
            (
                "substitute_bit_moves",
                Some(split::substitute_bit_moves(
                    definitions.clone(),
                    claims.clone(),
                )),
            ),
            (
                "unify_definitions",
                Some(split::unify_definitions(
                    definitions.clone(),
                    claims.clone(),
                )),
            ),
        ];
        spellings.push((
            "folded_spelling",
            split::folded_spelling(definitions.clone(), claims.clone()),
        ));
        let inputs: Vec<HashMap<String, u128>> = (0..32)
            .map(|_| {
                vars.iter()
                    .map(|(name, width)| (name.clone(), fit(u128::from(terms.next()), *width)))
                    .collect()
            })
            .collect();
        for (name, spelling) in spellings {
            let Some((kept, rewritten)) = spelling else {
                continue;
            };
            spelled += 1;
            for env in &inputs {
                let evaluate = |definitions: &[(String, E)], claims: &E| {
                    let mut values = env.clone();
                    let mut memo = HashMap::new();
                    for (name, expr) in definitions {
                        let value = bv(expr, &values, &mut memo);
                        values.insert(name.clone(), value);
                    }
                    (boolean(claims, &values, &mut memo), values)
                };
                let (holds, values) = evaluate(&definitions, &claims);
                let (spelled_holds, spelled_values) = evaluate(&kept, &rewritten);
                if holds != spelled_holds
                    || kept
                        .iter()
                        .any(|(defined, _)| values[defined] != spelled_values[defined])
                {
                    failures.push(format!("{name} changes round {round} at {env:?}"));
                    break;
                }
            }
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
    assert!(spelled >= 1500, "{spelled} spellings swept");
}

/// `folded_claims` keeps the value of every claim it is given, guarded ones
/// included: on random right-nested conjunctions of guarded claims `(or (not
/// G) X)` and plain ones, whose guard literals fold to `true`, fold to
/// `false` or read a variable, and whose bodies hold one or more equations
/// (identities among them), the folded claims are `None` only where the
/// claims hold on every sampled input and otherwise have the claims' value
/// on every sampled input (each `true` literal dropped from its guard, each
/// item under a `false` literal dropped, an item left unguarded split into
/// its conjuncts, all exactly).
#[test]
fn folded_claims_keep_every_claims_value() {
    let x = E::var("x", 8);
    let y = E::var("y", 8);
    let literals = [
        // Folds to `true`.
        E::bv_const(1, 8).bvult(E::bv_const(2, 8)),
        // Folds to `false`.
        E::bv_const(3, 8).bvult(E::bv_const(2, 8)),
        // A variable literal.
        x.clone().eq_expr(E::bv_const(0, 8)),
        y.clone().bvult(x.clone()),
    ];
    let equations = [
        x.clone().eq_expr(y.clone()),
        x.clone().bvadd(E::bv_const(0, 8)).eq_expr(x.clone()),
        y.clone().eq_expr(y.clone()),
        x.clone().bvsub(y.clone()).eq_expr(E::bv_const(0, 8)),
        E::bv_const(5, 8)
            .bvadd(E::bv_const(1, 8))
            .eq_expr(x.clone()),
    ];
    let mut state = 0x3c6e_f372_fe94_f82bu64;
    let mut pick = |n: usize| {
        state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1);
        ((state >> 33) % n as u64) as usize
    };
    let mut kept = 0;
    for _ in 0..3000 {
        let mut items: Vec<E> = Vec::new();
        for _ in 0..1 + pick(3) {
            let body = (0..1 + pick(3))
                .map(|_| equations[pick(equations.len())].clone())
                .rev()
                .reduce(|tail, term| term.and_expr(tail))
                .expect("a body");
            if pick(3) == 0 {
                items.push(body);
                continue;
            }
            let guard = (0..1 + pick(3))
                .map(|_| literals[pick(literals.len())].clone())
                .rev()
                .reduce(|tail, term| term.and_expr(tail))
                .expect("a guard");
            items.push(guard.not_expr().or_expr(body));
        }
        let claims = items
            .into_iter()
            .rev()
            .reduce(|tail, term| term.and_expr(tail))
            .expect("claims");
        let folded = split::folded_claims(&claims);
        for a in [0u128, 1, 2, 5, 6, 0xff] {
            for b in [0u128, 1, 6, 0xfe] {
                let env: HashMap<String, u128> = [("x".to_owned(), a), ("y".to_owned(), b)]
                    .into_iter()
                    .collect();
                let holds = boolean(&claims, &env, &mut HashMap::new());
                match &folded {
                    None => assert!(holds, "{claims} folds away, yet fails at x {a} y {b}"),
                    Some(folded) => assert_eq!(
                        boolean(folded, &env, &mut HashMap::new()),
                        holds,
                        "{claims} and {folded} differ at x {a} y {b}"
                    ),
                }
            }
        }
        kept += usize::from(folded.is_some());
    }
    assert!(kept > 1000, "{kept} claims kept");
}

// ---------------------------------------------------------------------------
// OD-189: each slice-16 part spelled again
// ---------------------------------------------------------------------------

/// A part's definitions (in order), as `(name, right-hand side)`.
pub(crate) fn part_definitions(part: &ProofObligation) -> Vec<(String, E)> {
    definitions_of(part)
}

/// The free inputs of a part (its declared inputs that are not definitions).
pub(crate) fn part_free(part: &ProofObligation) -> Vec<(String, u32)> {
    let defined: HashSet<String> = definitions_of(part)
        .into_iter()
        .map(|(name, _)| name)
        .collect();
    part.inputs
        .iter()
        .filter(|(name, _)| !defined.contains(name))
        .cloned()
        .collect()
}

/// THE parts sweep of OD-189: every earlier fixture cut at every block start
/// (slice 16's test policy), every slice-16 size shape (the production
/// planner) and every slice-16 control, stated in parts in the legacy
/// spelling (slice 16's parts, [`with_legacy_spelling`]) and canonically:
///
/// * the canonical parts are exactly the legacy parts, each spelled again by
///   `respelled_part` (its second spelling when that passes the part check,
///   else the legacy part), a part whose second spelling empties dropped, in
///   order, unless every part empties (then every region is stated plainly,
///   as before);
/// * each second spelling keeps the legacy part's claim value and every
///   definition it keeps on every sampled input ([`sweep`]), and a part that
///   empties holds on every sampled input (its claims are identities);
/// * every canonical part passes the part check and the inventory check.
#[test]
fn every_part_spelled_again_is_its_slice_sixteen_part() {
    type PartCase = (
        String,
        Function,
        X86ISelFunction,
        Option<Vec<(Block, usize)>>,
    );
    let mut cases: Vec<PartCase> = Vec::new();
    for (label, source, machine) in super::slice16::earlier_fixtures() {
        let points = super::slice16::every_block(&source);
        cases.push((label, source, machine, Some(points)));
    }
    for shape in super::slice16::SLICE_SIXTEEN {
        let (source, machine) = super::slice16::slice16_pair(shape);
        cases.push((format!("s16 {shape:?}"), source, machine, None));
    }
    let mut failures: Vec<String> = Vec::new();
    let (mut parts, mut respelled, mut emptied, mut changed) = (0usize, 0usize, 0usize, 0usize);
    for (label, source, machine, points) in &cases {
        let build = || match points {
            Some(points) => super::slice16::in_parts(source, machine, points.clone()),
            None => fixture_owner(source, machine),
        };
        // OD-189's second spelling alone: slice 18's spelling (slice 19's
        // third spelling of each part is `slice19`'s sweep).
        let (Ok(canonical), Ok(legacy)) = (
            with_normal_groups(normal::Groups::NONE, build),
            with_legacy_spelling(build),
        ) else {
            continue;
        };
        if !canonical.is_stated_in_parts() {
            continue;
        }
        if let Err(why) = with_normal_groups(normal::Groups::NONE, || canonical.check_parts()) {
            failures.push(format!("{label}: the inventory does not check: {why}"));
        }
        let mut expected: Vec<ProofObligation> = Vec::new();
        for (k, part) in legacy.parts().iter().enumerate() {
            parts += 1;
            let definitions = part_definitions(part);
            let free = part_free(part);
            let plain: Built = (part.clone(), free.clone(), Spelling::Plain);
            match split::respelled_part(definitions, part.aarch64_expr.clone()) {
                None => {
                    emptied += 1;
                    let mut state = 0x1234_5678u64 ^ k as u64;
                    for _ in 0..64 {
                        let inputs: HashMap<String, u128> = free
                            .iter()
                            .map(|(name, width)| (name.clone(), sample(*width, &mut state)))
                            .collect();
                        if !evaluate_theorem(part, &inputs).0 {
                            failures.push(format!(
                                "{label} part {}: its second spelling empties, yet it fails a sample",
                                k + 1
                            ));
                            break;
                        }
                    }
                }
                Some((kept, claims)) => {
                    let candidate = split::part_obligation(part, &free, kept, claims);
                    let candidate_free = part_free(&candidate);
                    if check_definitional_part(&candidate, &candidate_free).is_ok() {
                        respelled += 1;
                        let spelled: Built =
                            (candidate.clone(), candidate_free, Spelling::BitMoves);
                        if let Err(why) =
                            sweep(&format!("{label} part {}", k + 1), &plain, &spelled)
                        {
                            failures.push(why);
                        }
                        expected.push(candidate);
                    } else {
                        expected.push(part.clone());
                    }
                }
            }
        }
        if expected.is_empty() {
            // Every part emptied: every region is stated plainly.
            continue;
        }
        let names = |list: &[ProofObligation]| -> Vec<ProofObligation> {
            list.iter()
                .map(|part| ProofObligation {
                    name: String::new(),
                    ..part.clone()
                })
                .collect()
        };
        // Every region empty in slice 16's spelling: both state every region
        // plainly, the same parts.
        let unchanged = names(legacy.parts()) == names(canonical.parts());
        changed += usize::from(!unchanged);
        if names(&expected) != names(canonical.parts()) && !unchanged {
            failures.push(format!(
                "{label}: the canonical parts are not the legacy parts spelled again ({} expected, {} stated)",
                expected.len(),
                canonical.parts().len()
            ));
        }
    }
    eprintln!(
        "SLICE18_PARTS parts={parts} respelled={respelled} emptied={emptied} \
         functions_changed={changed}"
    );
    assert!(failures.is_empty(), "{}", failures.join("\n"));
    assert!(respelled >= 200, "{respelled} parts spelled again");
    assert!(
        changed >= 50,
        "the second spelling changes {changed} functions' parts"
    );
}

/// A part's second spelling (OD-189) substitutes the bit moves before it
/// numbers: the source's `p1 := x[31:0]` and the machine's `m0 :=
/// zero_extend(x[31:0])` read one stored byte through two names, which slice
/// 16's first spelling keeps apart (it numbers only repeated terms) and the
/// second makes one term, so the part's byte claim is an identity and the
/// part empties; a part that also computes keeps the computation's
/// definition and drops the bit moves' names. Each spelling keeps the
/// claims' value on every input tried.
#[test]
fn the_second_spelling_substitutes_the_bit_moves() {
    let x = E::var("x", 64);
    let definitions = vec![
        ("p1".to_owned(), x.clone().extract(31, 0)),
        ("m0".to_owned(), x.clone().extract(31, 0).zero_ext(32)),
        ("s3".to_owned(), E::var("p1", 32).bvadd(E::bv_const(7, 32))),
    ];
    let byte = E::var("p1", 32)
        .extract(7, 0)
        .eq_expr(E::var("m0", 64).extract(7, 0));
    assert!(
        split::respelled_part(definitions.clone(), byte.clone()).is_none(),
        "the byte claim is an identity once the bit moves are substituted"
    );
    let sum = E::var("s3", 32).eq_expr(E::var("m0", 64).extract(31, 0).bvadd(E::bv_const(7, 32)));
    let claims = byte.and_expr(
        sum.clone()
            .and_expr(E::var("s3", 32).eq_expr(E::var("x", 64).extract(31, 0))),
    );
    let (kept, rewritten) =
        split::respelled_part(definitions.clone(), claims.clone()).expect("a claim is left");
    assert!(
        kept.iter().all(|(name, _)| name != "p1" && name != "m0"),
        "the bit moves are substituted: {kept:?}"
    );
    for round in 0..512u64 {
        let value = round.wrapping_mul(0x9e37_79b9_7f4a_7c15) ^ (round << 40);
        let env: HashMap<String, u128> =
            [("x".to_owned(), u128::from(value))].into_iter().collect();
        let evaluate = |definitions: &[(String, E)], claims: &E| {
            let mut values = env.clone();
            let mut memo = HashMap::new();
            for (name, expr) in definitions {
                let v = bv(expr, &values, &mut memo);
                values.insert(name.clone(), v);
            }
            boolean(claims, &values, &mut memo)
        };
        assert_eq!(
            evaluate(&definitions, &claims),
            evaluate(&kept, &rewritten),
            "x {value:#x}"
        );
    }
}
