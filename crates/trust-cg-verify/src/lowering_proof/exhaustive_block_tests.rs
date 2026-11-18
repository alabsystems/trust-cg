// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The lane-blocked exhaustive sweep (`verify_exhaustive_blocked`) checks the
//! same tuples against the same values with the same failure behaviour as the
//! per-tuple loop it replaced (`verify_exhaustive_scalar`).
//!
//! The x86-64 signed-multiply-overflow canary
//! (OD-X86-OVERFLOW-CANARY-UNCONDITIONAL-20261112) is the reason this sweep
//! was made faster, so most tests here run that exact validator, or mutants
//! of its obligation, through the production path.

use super::*;
use crate::pass_validators::{
    CheckedOp, OverflowExpansion, OverflowExpansionValidator, PassValidation, PassValidator,
    TargetArch,
};

/// The validator `trust-cg-codegen`'s `validate_x86_overflow_expansion_canary`
/// runs, verbatim.
fn canary() -> OverflowExpansionValidator {
    OverflowExpansionValidator::signed_mul(
        "x86-overflow-expand",
        8,
        OverflowExpansion::DivisionFreeWideMul,
        TargetArch::X86_64,
    )
}

/// A validator whose obligation is given directly: the canary's obligation
/// with a mutated expansion side.
struct Mutant(ProofObligation);

impl PassValidator for Mutant {
    fn pass_name(&self) -> &str {
        "x86-overflow-expand"
    }
    fn obligation(&self) -> ProofObligation {
        self.0.clone()
    }
    fn target_arch(&self) -> TargetArch {
        TargetArch::X86_64
    }
}

/// The canary's obligation with its expansion side wrong at exactly one input
/// tuple `(a, b)`: the packed result's low bit is flipped there.
fn wrong_only_at(a: u64, b: u64) -> ProofObligation {
    let mut ob = canary().obligation();
    let at = SmtExpr::var("a", 8)
        .eq_expr(SmtExpr::bv_const(a, 8))
        .and_expr(SmtExpr::var("b", 8).eq_expr(SmtExpr::bv_const(b, 8)));
    let flipped = ob.aarch64_expr.clone().bvxor(SmtExpr::bv_const(1, 9));
    ob.aarch64_expr = SmtExpr::ite(at, flipped, ob.aarch64_expr.clone());
    ob
}

fn env_of(inputs: &[(String, u32)], values: &[u64]) -> EvalEnv {
    let mut env = EvalEnv::default();
    for ((name, _), value) in inputs.iter().zip(values) {
        env.insert(name.clone(), *value);
    }
    env
}

/// Every tuple of `inputs`' domain in the scalar loop's order (last input
/// fastest), computed independently of either sweep.
fn all_tuples(inputs: &[(String, u32)]) -> Vec<Vec<u64>> {
    let mut tuples = vec![Vec::new()];
    for (_, width) in inputs {
        let mut next = Vec::new();
        for prefix in &tuples {
            for value in 0..(1u64 << *width) {
                let mut t = prefix.clone();
                t.push(value);
                next.push(t);
            }
        }
        tuples = next;
    }
    tuples
}

/// Both sweeps on the same compiled obligation, and the interpreter-only
/// scalar sweep, rendered for exact comparison.
fn three_verdicts(ob: &ProofObligation) -> [String; 3] {
    let count = exhaustive_input_count(ob, &VerificationConfig::default())
        .expect("test obligations are inside the exhaustive budget");
    let co = CompiledObligation::try_new(ob).expect("test obligations compile");
    [
        format!("{:?}", verify_exhaustive(ob, Some(&co), count)),
        format!("{:?}", verify_exhaustive_scalar(ob, Some(&co), count)),
        format!("{:?}", verify_exhaustive_scalar(ob, None, count)),
    ]
}

fn overflow_family() -> Vec<ProofObligation> {
    let mut family = Vec::new();
    for arch in [TargetArch::X86_64, TargetArch::Aarch64] {
        for (op, expansion) in [
            (CheckedOp::SignedMul, OverflowExpansion::DivisionFreeWideMul),
            (CheckedOp::SignedMul, OverflowExpansion::SdivIdentity),
            (CheckedOp::SignedMul, OverflowExpansion::SignBitCheck),
            (CheckedOp::SignedAdd, OverflowExpansion::SignBitCheck),
            (CheckedOp::SignedSub, OverflowExpansion::SignBitCheck),
            (CheckedOp::SignedAdd, OverflowExpansion::DivisionFreeWideMul),
        ] {
            family.push(
                OverflowExpansionValidator {
                    pass_name: "x86-overflow-expand".to_string(),
                    width: 8,
                    op,
                    expansion,
                    arch,
                }
                .obligation(),
            );
        }
    }
    family
}

/// (a) The tuple set. The canary, run through the production validator,
/// decides every one of the 2^16 `(a, b)` tuples exactly once, in the scalar
/// loop's order, and nothing else.
#[test]
fn canary_sweep_visits_every_tuple_exactly_once() {
    exhaustive_visit_probe::start();
    let verdict = canary().validate();
    let visits = exhaustive_visit_probe::take();
    assert!(
        matches!(verdict, PassValidation::Verified { .. }),
        "the canary must verify: {verdict:?}"
    );
    let expected = all_tuples(&canary().obligation().inputs);
    assert_eq!(expected.len(), 1 << 16);
    assert_eq!(
        visits.len(),
        1 << 16,
        "the canary must decide 65,536 tuples"
    );
    let mut seen = vec![0u32; 1 << 16];
    for tuple in &visits {
        assert_eq!(tuple.len(), 2, "two inputs per tuple");
        assert!(
            tuple[0] < 256 && tuple[1] < 256,
            "tuple {tuple:?} outside i8 x i8"
        );
        seen[((tuple[0] << 8) | tuple[1]) as usize] += 1;
    }
    assert!(
        seen.iter().all(|&n| n == 1),
        "every (a, b) exactly once; first miss or repeat at index {:?}",
        seen.iter().position(|&n| n != 1)
    );
    assert_eq!(visits, expected, "tuples decided in mixed-radix order");
}

/// (b) The oracle. At every one of the 2^16 tuples, both sides of every
/// overflow-family obligation (the canary's own, the trapping SDIV identity,
/// add/sub, and the mismatched-pairing sentinel, on both architectures) take
/// the same value in the lane evaluator, the scalar tape evaluator and the
/// tree interpreter `SmtExpr::try_eval`, which this change does not touch.
/// Every node, not only the root, is stored without loss, so none of these
/// tapes falls back.
#[test]
fn lane_values_equal_interpreter_at_every_tuple() {
    const B: usize = EXHAUSTIVE_BLOCK;
    for ob in overflow_family() {
        let tuples = all_tuples(&ob.inputs);
        for (expr, side) in [
            (&ob.trust_ir_expr, "source"),
            (&ob.aarch64_expr, "expansion"),
        ] {
            let tape = FlatProg::compile(expr, &ob.inputs).expect("overflow tapes compile");
            let kinds = tape
                .lane_kinds(&env_of(&ob.inputs, &tuples[0]))
                .expect("overflow tapes hold only Bv and Bool values");
            let root_kind = kinds[tape.root_index()];
            let mut cols = Vec::new();
            let mut scratch = Vec::new();
            for block in tuples.chunks(B) {
                let mut vars = vec![0u64; ob.inputs.len() * B];
                for (lane, tuple) in block.iter().enumerate() {
                    for (slot, value) in tuple.iter().enumerate() {
                        vars[slot * B + lane] = *value;
                    }
                }
                let root = tape
                    .eval_lanes(&kinds, &vars, B, block.len(), &mut cols)
                    .expect("no overflow-family value changes variant")
                    .to_vec();
                for (lane, tuple) in block.iter().enumerate() {
                    let env = env_of(&ob.inputs, tuple);
                    let interpreted = expr.try_eval(&env).expect("overflow terms evaluate");
                    let scalar = tape.eval(&env, &mut scratch);
                    for (node, value) in scratch.iter().enumerate() {
                        assert_eq!(
                            kinds[node].decode(cols[node * B + lane]),
                            *value,
                            "{} {side} node {node} at {tuple:?}",
                            ob.name
                        );
                    }
                    let lanes = root_kind.decode(root[lane]).to_eval();
                    assert_eq!(
                        lanes, interpreted,
                        "{} {side} at {tuple:?}: lanes vs interpreter",
                        ob.name
                    );
                    assert_eq!(scalar, interpreted, "{} {side} at {tuple:?}", ob.name);
                }
            }
        }
    }
}

/// A tape whose values the lanes cannot hold losslessly is refused by the
/// lane evaluator and swept per tuple from its first tuple: a trapping
/// division (`Poison` at some tuples only, so the refusal comes mid-sweep), a
/// trap at the first tuple, and a 72-bit intermediate (`Bv128`). The verdict
/// is the per-tuple verdict and the decided tuples are the whole domain once.
#[test]
fn unencodable_tapes_fall_back_to_the_per_tuple_sweep() {
    let x = SmtExpr::var("x", 8);
    let y = SmtExpr::var("y", 8);
    let base = |name: &str, source: SmtExpr, target: SmtExpr, pre: Vec<SmtExpr>| ProofObligation {
        name: name.to_string(),
        trust_ir_expr: source,
        aarch64_expr: target,
        inputs: vec![("x".to_string(), 8), ("y".to_string(), 8)],
        preconditions: pre,
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::InstructionLowering),
        machine_side_provenance: MachineSideProvenance::StaticDb,
    };
    let nonzero_y = y.clone().eq_expr(SmtExpr::bv_const(0, 8)).not_expr();
    let guarded_div = x.clone().bvudiv(y.clone()).trap_if_zero(y.clone());
    let cases = [
        // Poison at the first tuple (y == 0); the precondition excludes
        // every y == 0 tuple: valid.
        base(
            "trap_guarded",
            x.clone().bvudiv(y.clone()),
            guarded_div.clone(),
            vec![nonzero_y.clone()],
        ),
        // The guard is y + 1, zero only at y == 255: Poison appears
        // mid-sweep, after the lanes accepted tuple 0, and refutes.
        base(
            "trap_mid_sweep",
            x.clone().bvudiv(y.clone()),
            x.clone()
                .bvudiv(y.clone())
                .trap_if_zero(y.clone().bvadd(SmtExpr::bv_const(1, 8))),
            vec![],
        ),
        // 72-bit intermediate, valid.
        base(
            "wide_intermediate",
            x.clone().bvadd(y.clone()),
            x.clone()
                .zero_ext(64)
                .bvadd(y.clone().zero_ext(64))
                .extract(7, 0),
            vec![],
        ),
    ];
    let expect_valid = [true, false, true];
    for (ob, valid) in cases.iter().zip(expect_valid) {
        let count = exhaustive_input_count(ob, &VerificationConfig::default()).unwrap();
        let co = CompiledObligation::try_new(ob).expect("test obligations compile");
        exhaustive_visit_probe::start();
        let blocked = format!("{:?}", verify_exhaustive(ob, Some(&co), count));
        let visits = exhaustive_visit_probe::take();
        let per_tuple = format!("{:?}", verify_exhaustive_scalar(ob, Some(&co), count));
        assert_eq!(blocked, per_tuple, "{}", ob.name);
        assert_eq!(blocked == "Valid", valid, "{}: {blocked}", ob.name);
        if valid {
            assert_eq!(visits, all_tuples(&ob.inputs), "{}", ob.name);
        }
    }
}

/// The verdict, counterexample text included, is identical across the
/// blocked sweep, the per-tuple sweep on the same tapes and the per-tuple
/// interpreter sweep, for the canary, its family and its single-tuple
/// mutants.
#[test]
fn blocked_verdict_equals_per_tuple_verdict() {
    let mut obligations = overflow_family();
    for (a, b) in [(0, 0), (0, 63), (0, 64), (3, 255), (255, 254), (255, 255)] {
        obligations.push(wrong_only_at(a, b));
    }
    for ob in &obligations {
        let [blocked, per_tuple, interpreted] = three_verdicts(ob);
        assert_eq!(blocked, per_tuple, "{}", ob.name);
        assert_eq!(blocked, interpreted, "{}", ob.name);
    }
}

/// (c) Fail-closed. An expansion wrong at a single tuple is refused, wherever
/// that tuple is: the first and last of the domain, both sides of every
/// block boundary the first two and last two blocks have, the first and last
/// tuple of an `a` row, and one interior tuple. The refusal names that tuple.
/// Dropping the first or last tuple, the last block, or the first or last
/// lane of a block from the sweep makes one of these pass, so each guards an
/// off-by-one bound.
#[test]
fn canary_refuses_an_expansion_wrong_at_any_single_tuple() {
    let block = EXHAUSTIVE_BLOCK as u64;
    let last = (1u64 << 16) - 1;
    let indices = [
        0,
        1,
        block - 1,
        block,
        2 * block - 1,
        2 * block,
        255,
        256,
        0x7f80,
        last + 1 - 2 * block,
        last - block,
        last + 1 - block,
        last - 1,
        last,
    ];
    let edges = indices.map(|t| (t >> 8, t & 0xff));
    for (a, bv) in edges {
        match Mutant(wrong_only_at(a, bv)).validate() {
            PassValidation::Rejected { reason, .. } => {
                let tuple = format!("[(\"a\", {a}), (\"b\", {bv})]");
                assert!(
                    reason.starts_with("counterexample: ") && reason.contains(&tuple),
                    "the refusal must name ({a}, {bv}): {reason}"
                );
            }
            other => panic!("an expansion wrong at ({a}, {bv}) was not refused: {other:?}"),
        }
    }
}

/// (c) Fail-closed. Whole-expansion regressions are refused with the same
/// refusal as before: the AArch64-only SDIV identity (the #67 miscompile) on
/// x86-64, a wrapping add in place of the multiply, and an overflow flag taken
/// from the wrong half of the wide product.
#[test]
fn canary_refuses_wrong_expansions() {
    let base = canary().obligation();
    let mut sdiv = OverflowExpansionValidator::signed_mul(
        "x86-overflow-expand",
        8,
        OverflowExpansion::SdivIdentity,
        TargetArch::X86_64,
    )
    .obligation();
    sdiv.name = base.name.clone();
    let mut add_not_mul = base.clone();
    let a = SmtExpr::var("a", 8);
    let b = SmtExpr::var("b", 8);
    let wide = a.clone().sign_ext(8).bvmul(b.clone().sign_ext(8));
    let roundtrip = wide.clone().extract(7, 0).sign_ext(8);
    let overflow = SmtExpr::ite(
        wide.clone().eq_expr(roundtrip).not_expr(),
        SmtExpr::bv_const(1, 1),
        SmtExpr::bv_const(0, 1),
    );
    add_not_mul.aarch64_expr = overflow.clone().concat(a.clone().bvadd(b.clone()));
    let mut wrong_half = base.clone();
    let low_sign = wide.clone().extract(7, 0).sign_ext(8);
    let wrong_flag = SmtExpr::ite(
        wide.extract(15, 8).sign_ext(8).eq_expr(low_sign).not_expr(),
        SmtExpr::bv_const(1, 1),
        SmtExpr::bv_const(0, 1),
    );
    wrong_half.aarch64_expr = wrong_flag.concat(a.bvmul(b));
    for (label, ob) in [
        ("sdiv identity", sdiv),
        ("add for mul", add_not_mul),
        ("wrong product half", wrong_half),
    ] {
        let [blocked, per_tuple, _] = three_verdicts(&ob);
        assert_eq!(blocked, per_tuple, "{label}");
        match Mutant(ob).validate() {
            PassValidation::Rejected { reason, .. } => {
                assert!(reason.starts_with("counterexample: "), "{label}: {reason}")
            }
            other => panic!("{label}: a wrong expansion was not refused: {other:?}"),
        }
    }
}

/// Preconditions, partial blocks and more than two inputs: the blocked sweep
/// agrees with the per-tuple sweep, including the vacuous-precondition
/// `Unknown`, and decides exactly the domain's tuples.
#[test]
fn blocked_sweep_matches_per_tuple_on_preconditions_and_partial_blocks() {
    let mk = |widths: &[u32], pre: Vec<SmtExpr>, target: SmtExpr| {
        let inputs: Vec<(String, u32)> = widths
            .iter()
            .enumerate()
            .map(|(i, w)| (format!("x{i}"), *w))
            .collect();
        let sum = inputs
            .iter()
            .map(|(n, w)| SmtExpr::var(n.clone(), *w).zero_ext(8 - *w))
            .reduce(SmtExpr::bvadd)
            .unwrap();
        ProofObligation {
            name: format!("blocked_{widths:?}"),
            trust_ir_expr: sum,
            aarch64_expr: target,
            inputs,
            preconditions: pre,
            fp_inputs: vec![],
            category: Some(TransvalCheckKind::InstructionLowering),
            machine_side_provenance: MachineSideProvenance::StaticDb,
        }
    };
    let x = |i: usize, w: u32| SmtExpr::var(format!("x{i}"), w);
    let sum3 = x(0, 3)
        .zero_ext(5)
        .bvadd(x(1, 2).zero_ext(6))
        .bvadd(x(2, 2).zero_ext(6));
    let cases = [
        // 32 tuples: one partial block, valid.
        mk(&[5], vec![], x(0, 5).zero_ext(3)),
        // 128 tuples over three inputs, valid.
        mk(&[3, 2, 2], vec![], sum3.clone()),
        // 128 tuples, wrong only where x2 == 3 and x1 == 3, x0 == 7 (last tuple).
        mk(
            &[3, 2, 2],
            vec![],
            SmtExpr::ite(
                x(0, 3).eq_expr(SmtExpr::bv_const(7, 3)).and_expr(
                    x(1, 2)
                        .eq_expr(SmtExpr::bv_const(3, 2))
                        .and_expr(x(2, 2).eq_expr(SmtExpr::bv_const(3, 2))),
                ),
                SmtExpr::bv_const(0, 8),
                sum3.clone(),
            ),
        ),
        // Wrong where x0 == 0, but the precondition excludes x0 == 0: valid.
        mk(
            &[5],
            vec![x(0, 5).eq_expr(SmtExpr::bv_const(0, 5)).not_expr()],
            SmtExpr::ite(
                x(0, 5).eq_expr(SmtExpr::bv_const(0, 5)),
                SmtExpr::bv_const(99, 8),
                x(0, 5).zero_ext(3),
            ),
        ),
        // Unsatisfiable precondition: vacuous, Unknown.
        mk(
            &[5],
            vec![SmtExpr::bv_const(0, 1).eq_expr(SmtExpr::bv_const(1, 1))],
            SmtExpr::bv_const(77, 8),
        ),
        // Two preconditions, the second excluding the only wrong tuple: valid.
        mk(
            &[3, 2, 2],
            vec![
                x(1, 2).eq_expr(SmtExpr::bv_const(1, 2)).not_expr(),
                x(0, 3).eq_expr(SmtExpr::bv_const(2, 3)).not_expr(),
            ],
            SmtExpr::ite(
                x(0, 3).eq_expr(SmtExpr::bv_const(2, 3)),
                SmtExpr::bv_const(0, 8),
                sum3,
            ),
        ),
    ];
    let expect_valid = [true, true, false, true, false, true];
    for (ob, valid) in cases.iter().zip(expect_valid) {
        let count = exhaustive_input_count(ob, &VerificationConfig::default()).unwrap();
        let co = CompiledObligation::try_new(ob).expect("test obligations compile");
        exhaustive_visit_probe::start();
        let _ = verify_exhaustive(ob, Some(&co), count);
        let visits = exhaustive_visit_probe::take();
        let [blocked, per_tuple, interpreted] = three_verdicts(ob);
        assert_eq!(blocked, per_tuple, "{}", ob.name);
        assert_eq!(blocked, interpreted, "{}", ob.name);
        assert_eq!(blocked == "Valid", valid, "{}: {blocked}", ob.name);
        if valid {
            assert_eq!(visits, all_tuples(&ob.inputs), "{}", ob.name);
        }
    }
}

/// (c) Fail-closed, preconditions across blocks. The per-lane precondition
/// mask is reset for every block: a precondition unmet at lane 7 of block 0
/// (tuple (0, 7)) must not leave lane 7 unmet in block 3, where the expansion
/// is wrong at (3, 7). Without the reset the sweep skips (3, 7) and accepts
/// the wrong expansion. (The canary itself has no precondition; this guards
/// the shared sweep it calls.)
#[test]
fn precondition_mask_resets_per_block() {
    let mut ob = wrong_only_at(3, 7);
    ob.preconditions = vec![
        SmtExpr::var("a", 8)
            .eq_expr(SmtExpr::bv_const(0, 8))
            .and_expr(SmtExpr::var("b", 8).eq_expr(SmtExpr::bv_const(7, 8)))
            .not_expr(),
    ];
    let [blocked, per_tuple, interpreted] = three_verdicts(&ob);
    assert_eq!(blocked, per_tuple);
    assert_eq!(blocked, interpreted);
    match Mutant(ob).validate() {
        PassValidation::Rejected { reason, .. } => assert!(
            reason.contains("[(\"a\", 3), (\"b\", 7)]"),
            "the refusal must name (3, 7): {reason}"
        ),
        other => panic!("an expansion wrong at (3, 7) was not refused: {other:?}"),
    }
}

/// (c) Fail-closed, evaluator disagreement. If the blocked sweep ever finds a
/// lane unequal that the per-tuple decision does not confirm (its `Equal` or
/// its `PreconditionUnmet`), the sweep must stop with `Unknown`, which the
/// validator refuses; it must never continue to a `Valid`. The shared node
/// semantics make this unreachable in a real sweep, so a test-only fault
/// (`exhaustive_visit_probe::inject_fault`) forces each half of it.
#[test]
fn evaluator_disagreement_is_unknown_and_refused() {
    use super::exhaustive_visit_probe::{Fault, clear_fault, inject_fault};
    let tuple = |a: u64, b: u64| (a << 8) | b;
    // Precondition excludes (5, 9) and the expansion is wrong only there:
    // valid unless the sweep is forced to treat (5, 9) as met.
    let mut excluded = wrong_only_at(5, 9);
    excluded.preconditions = vec![
        SmtExpr::var("a", 8)
            .eq_expr(SmtExpr::bv_const(5, 8))
            .and_expr(SmtExpr::var("b", 8).eq_expr(SmtExpr::bv_const(9, 8)))
            .not_expr(),
    ];
    let cases = [
        (
            "expansion payload flipped",
            canary().obligation(),
            Fault::FlipTarget,
            tuple(3, 7),
        ),
        (
            "precondition forced met",
            excluded,
            Fault::ForceMet,
            tuple(5, 9),
        ),
    ];
    for (label, ob, fault, at) in cases {
        let count = exhaustive_input_count(&ob, &VerificationConfig::default()).unwrap();
        let co = CompiledObligation::try_new(&ob).expect("test obligations compile");
        // Control: without the fault the obligation is valid.
        assert_eq!(
            format!("{:?}", verify_exhaustive(&ob, Some(&co), count)),
            "Valid",
            "{label}: control"
        );
        inject_fault(fault, at);
        let direct = verify_exhaustive(&ob, Some(&co), count);
        let validated = Mutant(ob.clone()).validate();
        clear_fault();
        match direct {
            VerificationResult::Unknown { reason } => assert!(
                reason.contains("blocked and per-tuple evaluators disagree"),
                "{label}: {reason}"
            ),
            other => panic!("{label}: a disagreement must be Unknown, got {other:?}"),
        }
        assert!(
            matches!(validated, PassValidation::Rejected { .. }),
            "{label}: the validator must refuse a disagreement: {validated:?}"
        );
    }
}

/// Seeded xorshift for the random differential below.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}

const RW: u32 = 8;

fn random_input(r: &mut Rng, inputs: &[(String, u32)]) -> SmtExpr {
    let (n, w) = &inputs[r.below(inputs.len() as u64) as usize];
    let v = SmtExpr::var(n.clone(), *w);
    if *w == RW {
        v
    } else if r.below(2) == 0 {
        v.zero_ext(RW - *w)
    } else {
        v.sign_ext(RW - *w)
    }
}

fn random_bv(r: &mut Rng, inputs: &[(String, u32)], depth: u32) -> SmtExpr {
    if depth == 0 || r.below(5) == 0 {
        return if r.below(3) == 0 {
            let c = [0u64, 1, 0x7f, 0x80, 0xff, 7][r.below(6) as usize];
            SmtExpr::bv_const(if r.below(2) == 0 { c } else { r.below(256) }, RW)
        } else {
            random_input(r, inputs)
        };
    }
    let a = random_bv(r, inputs, depth - 1);
    let b = random_bv(r, inputs, depth - 1);
    match r.below(19) {
        0 => a.bvadd(b),
        1 => a.bvsub(b),
        2 => a.bvmul(b),
        3 => a.bvand(b),
        4 => a.bvor(b),
        5 => a.bvxor(b),
        6 => a.bvshl(b),
        7 => a.bvlshr(b),
        8 => a.bvashr(b),
        9 => a.bvudiv(b),
        10 => a.bvurem(b),
        11 => a.bvsdiv(b),
        12 => a.bvneg(),
        13 => SmtExpr::ite(random_bool(r, inputs, depth - 1), a, b),
        14 => a.trap_if_zero(b),
        // Wide intermediates (`Bv128` lanes): the per-tuple fallback.
        15 => a.zero_ext(64).bvadd(b.zero_ext(64)).extract(7, 0),
        16 => a.sign_ext(8).bvmul(b.sign_ext(8)).extract(15, 8),
        17 => a.extract(3, 0).concat(b.extract(7, 4)),
        _ => a.bvudiv(b).trap_if_zero(random_bv(r, inputs, depth - 1)),
    }
}

fn random_bool(r: &mut Rng, inputs: &[(String, u32)], depth: u32) -> SmtExpr {
    if depth == 0 {
        return random_bv(r, inputs, 0).eq_expr(random_bv(r, inputs, 0));
    }
    let a = random_bv(r, inputs, depth - 1);
    let b = random_bv(r, inputs, depth - 1);
    match r.below(10) {
        0 => a.eq_expr(b),
        1 => a.bvslt(b),
        2 => a.bvult(b),
        3 => a.bvsge(b),
        4 => a.bvugt(b),
        5 => random_bool(r, inputs, depth - 1).not_expr(),
        6 => random_bool(r, inputs, depth - 1).and_expr(random_bool(r, inputs, depth - 1)),
        7 => random_bool(r, inputs, depth - 1).or_expr(random_bool(r, inputs, depth - 1)),
        8 => random_bool(r, inputs, depth - 1).eq_expr(random_bool(r, inputs, depth - 1)),
        _ => SmtExpr::ite(
            random_bool(r, inputs, depth - 1),
            random_bool(r, inputs, depth - 1),
            SmtExpr::bool_const(r.below(2) == 0),
        ),
    }
}

/// The conjunction `inputs == some random tuple`.
fn random_point(r: &mut Rng, inputs: &[(String, u32)]) -> SmtExpr {
    inputs
        .iter()
        .map(|(n, w)| SmtExpr::var(n.clone(), *w).eq_expr(SmtExpr::bv_const(r.below(1 << *w), *w)))
        .reduce(SmtExpr::and_expr)
        .expect("at least one input")
}

/// Random differential over the whole shared sweep, not only the canary:
/// 3000 seeded obligations with one to three inputs of mixed widths (up to
/// 2^14 tuples, so many span several blocks), `Bv` and `Bool` roots, traps
/// (`Poison`), 128-bit intermediates, `Ite`, single-tuple mutants and
/// zero to two preconditions. The blocked sweep's verdict text and decided
/// tuples equal the per-tuple sweep's on the same tapes, and its verdict
/// equals the tree interpreter's. Without the per-block precondition-mask
/// reset this test fails as well.
#[test]
fn random_obligations_blocked_equals_per_tuple() {
    let mut r = Rng(0x9e37_79b9_7f4a_7c15);
    let (mut n, mut valid, mut invalid) = (0, 0, 0);
    for case in 0..3000u32 {
        let k = 1 + r.below(3) as usize;
        let mut inputs = Vec::new();
        let mut bits = 0;
        for i in 0..k {
            let w = 1 + r.below(8) as u32;
            if bits + w > 14 {
                break;
            }
            bits += w;
            inputs.push((format!("v{i}"), w));
        }
        let bool_root = r.below(5) == 0;
        let depth = 1 + r.below(4) as u32;
        let source = if bool_root {
            random_bool(&mut r, &inputs, depth)
        } else {
            random_bv(&mut r, &inputs, depth)
        };
        let target = match r.below(5) {
            0 | 1 => source.clone(),
            2 | 3 => {
                let other = if bool_root {
                    source.clone().not_expr()
                } else {
                    source
                        .clone()
                        .bvxor(SmtExpr::bv_const(1 + r.below(255), RW))
                };
                SmtExpr::ite(random_point(&mut r, &inputs), other, source.clone())
            }
            _ => {
                if bool_root {
                    random_bool(&mut r, &inputs, depth)
                } else {
                    random_bv(&mut r, &inputs, depth)
                }
            }
        };
        let preconditions: Vec<SmtExpr> = (0..r.below(3))
            .map(|_| {
                if r.below(2) == 0 {
                    random_point(&mut r, &inputs).not_expr()
                } else {
                    random_bool(&mut r, &inputs, 1)
                }
            })
            .collect();
        let ob = ProofObligation {
            name: format!("random_{case}"),
            trust_ir_expr: source,
            aarch64_expr: target,
            inputs,
            preconditions,
            fp_inputs: vec![],
            category: Some(TransvalCheckKind::InstructionLowering),
            machine_side_provenance: MachineSideProvenance::StaticDb,
        };
        let Some(count) = exhaustive_input_count(&ob, &VerificationConfig::default()) else {
            continue;
        };
        let Some(co) = CompiledObligation::try_new(&ob) else {
            continue;
        };
        exhaustive_visit_probe::start();
        let blocked = format!("{:?}", verify_exhaustive(&ob, Some(&co), count));
        let blocked_visits = exhaustive_visit_probe::take();
        exhaustive_visit_probe::start();
        let per_tuple = format!("{:?}", verify_exhaustive_scalar(&ob, Some(&co), count));
        let per_tuple_visits = exhaustive_visit_probe::take();
        let interpreted = format!("{:?}", verify_exhaustive_scalar(&ob, None, count));
        assert_eq!(blocked, per_tuple, "case {case}: {ob:?}");
        assert_eq!(
            blocked_visits, per_tuple_visits,
            "case {case}: decided tuples"
        );
        assert_eq!(blocked, interpreted, "case {case}: interpreter");
        n += 1;
        if blocked == "Valid" {
            valid += 1;
        } else if blocked.starts_with("Invalid") {
            invalid += 1;
        }
    }
    // The generator must exercise both outcomes, not only one.
    assert!(
        n > 2500 && valid > 100 && invalid > 100,
        "{n} {valid} {invalid}"
    );
}
