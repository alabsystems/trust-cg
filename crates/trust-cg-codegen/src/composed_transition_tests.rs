// trust-cg-codegen/composed_transition_tests.rs - composed transition wiring tests
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use super::*;
use crate::license_test_support::permit_unlicensed;
use crate::pipeline::{OptLevel, Pipeline, PipelineConfig};
use std::sync::{Arc, Mutex};
use trust_cg_verify::composed_transition::{Representation, bytes_interface};

const DARWIN: &str = "aarch64-apple-darwin";
const LINUX: &str = "aarch64-unknown-linux-gnu";
const LEVELS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];

fn module(triple: &str, functy: &str, body: &str, name: &str) -> trust_ir::Module {
    let text = format!(
        "; TrustIr text format v1\nmodule \"ct\"\ntarget \"{triple}\" 8 little abi=\"aapcs64\"\n\
         functy.0 = {functy}\nfn @{name}(functy.0) {{\n{body}}}\n"
    );
    trust_ir::parser::parse_module(&text).unwrap_or_else(|error| panic!("{error:?}\n{text}"))
}

/// `(a + 5 - b) + a`: in the affine domain, and rewritten by DCE at O1+.
fn affine(triple: &str) -> (trust_ir::Module, trust_cg_lower::Function) {
    let module = module(
        triple,
        "(i64, i64) -> (i64)",
        "bb0(%0: i64, %1: i64):\n    %2 = const i64 5\n    %3 = add i64 %0, %2\n    \
         %4 = sub i64 %3, %1\n    %5 = add i64 %4, %0\n    ret %5\n",
        "affine",
    );
    let (lir, _) = trust_cg_lower::translate_function_with_license(
        &module.functions[0],
        &module,
        &permit_unlicensed(),
    )
    .expect("adapter");
    (module, lir)
}

/// `a * b`: outside the affine domain.
fn product(triple: &str) -> (trust_ir::Module, trust_cg_lower::Function) {
    let module = module(
        triple,
        "(i64, i64) -> (i64)",
        "bb0(%0: i64, %1: i64):\n    %2 = mul i64 %0, %1\n    ret %2\n",
        "product",
    );
    let (lir, _) = trust_cg_lower::translate_function_with_license(
        &module.functions[0],
        &module,
        &permit_unlicensed(),
    )
    .expect("adapter");
    (module, lir)
}

fn pipeline(triple: &str, level: OptLevel) -> Pipeline {
    Pipeline::new(PipelineConfig {
        opt_level: level,
        target_triple: triple.into(),
        ..PipelineConfig::default()
    })
}

fn prepare(
    pipeline: &Pipeline,
    module: &trust_ir::Module,
    lir: &trust_cg_lower::Function,
) -> (MachFunction, crate::pipeline::PreparationMetrics) {
    pipeline
        .prepare_function_with_metrics_and_trust_ir_module(lir, None, module, &module.functions[0])
        .expect("preparation")
}

#[test]
fn policy_spellings_round_trip_and_order() {
    for policy in [
        ComposedTransitionPolicy::Off,
        ComposedTransitionPolicy::Record,
        ComposedTransitionPolicy::Require,
    ] {
        assert_eq!(
            ComposedTransitionPolicy::parse(policy.as_str()),
            Some(policy)
        );
    }
    assert_eq!(ComposedTransitionPolicy::parse("everything"), None);
    assert_eq!(
        ComposedTransitionPolicy::Off.strongest(ComposedTransitionPolicy::Require),
        ComposedTransitionPolicy::Require
    );
    assert_eq!(
        ComposedTransitionPolicy::Require.strongest(ComposedTransitionPolicy::Record),
        ComposedTransitionPolicy::Require
    );
}

#[test]
fn proof_grade_preparation_requires_records_and_cannot_lower_it() {
    crate::env_lock::with_env_overrides_removed(&["TRUST_CG_COMPOSED_TRANSITION"], || {
        policies_resolve_against_the_proof_grade_floor()
    });
}

fn policies_resolve_against_the_proof_grade_floor() {
    let plain = pipeline(DARWIN, OptLevel::O2);
    assert_eq!(
        plain.composed_transition_policy(),
        ComposedTransitionPolicy::Off
    );
    assert_eq!(
        pipeline(DARWIN, OptLevel::O2)
            .with_composed_transitions(ComposedTransitionPolicy::Record)
            .composed_transition_policy(),
        ComposedTransitionPolicy::Record
    );
    assert_eq!(
        pipeline(DARWIN, OptLevel::O2)
            .with_proof_grade_aarch64_publication()
            .with_composed_transitions(ComposedTransitionPolicy::Off)
            .composed_transition_policy(),
        ComposedTransitionPolicy::Require
    );
    // Off: no record at all, and the default path is unchanged.
    let (module, lir) = affine(DARWIN);
    let (_, metrics) = prepare(&plain, &module, &lir);
    assert!(metrics.composed_transition.is_none());
}

#[test]
fn an_affine_function_composes_through_real_preparation_at_every_level() {
    for triple in [DARWIN, LINUX] {
        let (module, lir) = affine(triple);
        let origin = trust_cg_verify::composed_transition::trust_ir_function_interface(&module, 0)
            .expect("module-owned");
        let mut pass_runs = 0;
        for level in LEVELS {
            let proof = pipeline(triple, level).with_proof_grade_aarch64_publication();
            let (func, metrics) = prepare(&proof, &module, &lir);
            let record = metrics.composed_transition.expect("a proof-grade record");
            let composed = record
                .compose()
                .unwrap_or_else(|refusal| panic!("{triple} {level:?}: {refusal}\n{record:#?}"));
            composed
                .check_origin(&origin)
                .expect("starts at the source");
            assert_eq!(composed.strength, EvidenceStrength::ExactlyDecided);
            let stages: Vec<LinkStage> = record.links.iter().map(|link| link.stage).collect();
            assert_eq!(stages[..2], [LinkStage::Legalization, LinkStage::Selection]);
            assert_eq!(
                stages[stages.len() - 2..],
                [LinkStage::PostAllocation, LinkStage::Encoding]
            );
            pass_runs += composed.pass_runs;
            // The terminal is the proof-grade encoding of the final function.
            let (code, fixups, _) =
                crate::pipeline::encode_function_with_fixups_and_sites(&func).expect("encodes");
            assert!(fixups.is_empty());
            assert_eq!(composed.terminal, bytes_interface(&code));
            assert_eq!(composed.terminal_len, Some(code.len() as u64));
            assert_eq!(
                require_published(&func.name, Some(&record), &code, 0)
                    .expect("published")
                    .expect("required"),
                composed
            );
            // Every link names its relation, check and model.
            for link in &record.links {
                assert!(!link.relation.is_empty() && !link.check.is_empty());
                assert!(!link.model.is_empty(), "{}", link.name);
            }
        }
        assert!(pass_runs > 0, "{triple}: O1-O3 rewrite this function");
    }
}

#[test]
fn functions_outside_the_legalization_domain_say_why_and_are_not_required() {
    let (module, lir) = product(DARWIN);
    let proof = pipeline(DARWIN, OptLevel::O2).with_proof_grade_aarch64_publication();
    let (func, metrics) = prepare(&proof, &module, &lir);
    let record = metrics.composed_transition.expect("a record");
    assert!(!record.in_legalization_domain());
    assert!(record.links.is_empty(), "no link is paid for");
    let refusal = record.compose().expect_err("not composed");
    assert!(
        refusal.to_string().contains("unsupported affine TrustIR"),
        "{refusal}"
    );
    assert_eq!(
        require_composition(&func.name, Some(&record)),
        Ok(None),
        "no TrustIR-to-bytes claim to require"
    );

    // Without a TrustIR source there is nothing to start from.
    let (_, lir) = affine(DARWIN);
    let (_, metrics) = proof
        .prepare_function_with_metrics(&lir, None)
        .expect("preparation");
    let record = metrics.composed_transition.expect("a record");
    assert!(!record.in_legalization_domain());
    assert!(
        record
            .not_composed
            .as_ref()
            .is_some_and(|why| why.reason.contains("no TrustIR source"))
    );
    // A route that requires records refuses a function that has none.
    assert!(require_composition("f", None).is_err());
}

#[test]
fn corruption_an_unvalidated_instrumentation_step_breaks_the_chain() {
    // AOT profile instrumentation rewrites the function between the
    // optimizer and register allocation, and no validator covers it.
    let (module, lir) = affine(DARWIN);
    let sink = Arc::new(Mutex::new(trust_cg_opt::pgo::CounterMap::new()));
    let proof = pipeline(DARWIN, OptLevel::O0)
        .with_proof_grade_aarch64_publication()
        .with_profile_generate_sink(sink);
    let (func, metrics) = prepare(&proof, &module, &lir);
    let record = metrics.composed_transition.expect("a record");
    let refusal = record.compose().expect_err("an unvalidated step refuses");
    assert!(
        matches!(
            &refusal,
            CompositionRefusal::InterfaceMismatch { left_name, right_name, .. }
                if left_name == rel::SELECTION_NAME && right_name == "post-ra-value-flow"
        ),
        "{refusal}"
    );
    assert!(require_composition(&func.name, Some(&record)).is_err());
}

#[test]
fn corruption_published_bytes_and_fixups_must_match_the_terminal() {
    let (module, lir) = affine(DARWIN);
    let proof = pipeline(DARWIN, OptLevel::O2).with_proof_grade_aarch64_publication();
    let (func, metrics) = prepare(&proof, &module, &lir);
    let record = metrics.composed_transition.expect("a record");
    let (code, _, _) = crate::pipeline::encode_function_with_fixups_and_sites(&func).unwrap();
    for index in 0..code.len() {
        let mut mutated = code.clone();
        mutated[index] ^= 0x10;
        let refusal = require_published(&func.name, Some(&record), &mutated, 0)
            .expect_err("a mutated byte refuses");
        assert_eq!(refusal.class(), "published-bytes-mismatch");
    }
    let refusal = require_published(&func.name, Some(&record), &code, 1)
        .expect_err("a fixup the chain did not bind refuses");
    assert_eq!(refusal.stage(), Some(LinkStage::Encoding));
}

#[test]
fn session_records_refusals_as_unestablished_links() {
    let (module, lir) = affine(DARWIN);
    let raw = pipeline(DARWIN, OptLevel::O0)
        .select_ir_function(&lir)
        .expect("selection");

    // A rejected legalization establishes neither relation.
    let mut session = Session::begin(ComposedTransitionPolicy::Require, &lir.name);
    session.legalization(
        Legalization::Rejected {
            module: &module,
            ordinal: 0,
            reason: "LIR and AArch64 return different affine values".into(),
        },
        &lir,
        &raw,
    );
    assert!(!session.recording());
    assert!(session.transition_digest().is_none());
    let record = session.finish().unwrap();
    assert!(
        record.in_legalization_domain(),
        "a rejection is in the domain"
    );
    assert!(matches!(
        record.compose(),
        Err(CompositionRefusal::LinkNotEstablished {
            index: 0,
            stage: LinkStage::Legalization,
            ..
        })
    ));

    // Fixups at encoding, and a comparison that did not run.
    let mut session = Session::begin(ComposedTransitionPolicy::Record, &lir.name);
    session.legalization(
        Legalization::Checked {
            module: &module,
            ordinal: 0,
        },
        &lir,
        &raw,
    );
    assert!(session.recording());
    assert!(session.transition_digest().is_some());
    session.pre_allocation(&raw);
    session.post_allocation("post-ra-value-flow", &raw, None);
    assert!(
        !session.recording(),
        "a link that did not hold stops the chain"
    );
    let record = session.finish().unwrap();
    assert!(matches!(
        record.compose(),
        Err(CompositionRefusal::LinkNotEstablished { stage: LinkStage::PostAllocation, outcome, .. })
            if outcome == "not-run"
    ));

    let mut session = Session::begin(ComposedTransitionPolicy::Record, &lir.name);
    session.legalization(
        Legalization::Checked {
            module: &module,
            ordinal: 0,
        },
        &lir,
        &raw,
    );
    session.pre_allocation(&raw);
    session.post_allocation(
        "post-ra-value-flow",
        &raw,
        Some(&trust_cg_opt::ValidationVerdict::Validated),
    );
    session.encoding(&raw, Ok((&[0xc0, 0x03, 0x5f, 0xd6], 2)));
    let record = session.finish().unwrap();
    assert!(matches!(
        record.compose(),
        Err(CompositionRefusal::LinkNotEstablished { stage: LinkStage::Encoding, outcome, .. })
            if outcome == "fixups"
    ));
    assert_eq!(
        record.links.last().map(|link| link.to.representation),
        Some(Representation::Bytes)
    );

    // Off records nothing.
    let mut off = Session::begin(ComposedTransitionPolicy::Off, &lir.name);
    off.legalization(Legalization::NotCovered("x".into()), &lir, &raw);
    assert!(off.finish().is_none());
}

#[test]
fn object_publication_reads_each_functions_bytes_back() {
    for triple in [DARWIN, LINUX] {
        let (module, lir) = affine(triple);
        let proof = pipeline(triple, OptLevel::O2).with_proof_grade_aarch64_publication();
        let (func, metrics) = prepare(&proof, &module, &lir);
        let record = metrics.composed_transition.expect("a record");
        let object = proof
            .compile_module_with_globals(std::slice::from_ref(&func), &[])
            .expect("object");
        let records = [(func.name.as_str(), Some(&record))];
        assert_eq!(
            require_object_publication(&object, &records),
            Ok(1),
            "{triple}"
        );
        // Flip a bit of the function's code in the object.
        let (code, _, _) = crate::pipeline::encode_function_with_fixups_and_sites(&func).unwrap();
        let position = object
            .windows(code.len())
            .position(|window| window == code.as_slice())
            .expect("the object carries the code");
        let mut corrupted = object.clone();
        corrupted[position + 1] ^= 0x01;
        let refusal = require_object_publication(&corrupted, &records)
            .expect_err("a changed byte after the last link refuses");
        assert_eq!(refusal.class(), "published-bytes-mismatch", "{triple}");
        // A function the object does not define is refused too.
        let missing = [("absent", Some(&record))];
        assert!(require_object_publication(&object, &missing).is_err());
    }
}

fn transition(name: &str, n: u8, verdict: ValidationVerdict) -> PassTransition {
    PassTransition {
        pass_name: name.to_string(),
        reported_change: true,
        before: [n; 32],
        after: [n + 1; 32],
        validator: (verdict != ValidationVerdict::Uncovered)
            .then_some(trust_cg_opt::ValidatorKind::SymbolicRegionEquivalence),
        verdict,
    }
}

/// The production mapping from an optimizer transition to a link: only a
/// validated run establishes its link; an uncovered, refuted or unproved run
/// keeps its own outcome and reason.
#[test]
fn pass_run_links_establish_only_validated_runs() {
    let cases = [
        (ValidationVerdict::Validated, None),
        (ValidationVerdict::Uncovered, Some("uncovered")),
        (
            ValidationVerdict::Refuted("reported no change".into()),
            Some("refuted"),
        ),
        (
            ValidationVerdict::Unproved("terms differ".into()),
            Some("unproved"),
        ),
    ];
    for (index, (verdict, outcome)) in cases.into_iter().enumerate() {
        let link = pass_run_link(transition("p", index as u8 * 2, verdict.clone()));
        assert_eq!(link.stage, LinkStage::PassRun);
        assert_eq!(link.name, "p");
        assert_eq!(link.from.digest, [index as u8 * 2; 32]);
        assert_eq!(link.to.digest, [index as u8 * 2 + 1; 32]);
        assert_eq!(link.from.representation, Representation::MachIr);
        assert_eq!(link.strength, EvidenceStrength::ExactlyDecided);
        match (outcome, &link.verdict) {
            (None, LinkVerdict::Established) => {}
            (Some(expected), LinkVerdict::NotEstablished { outcome, reason }) => {
                assert_eq!(outcome, expected, "{verdict:?}");
                if let Some(detail) = verdict.reason() {
                    assert_eq!(reason, detail);
                }
            }
            (expected, found) => panic!("{verdict:?}: expected {expected:?}, found {found:?}"),
        }
        assert_eq!(
            link.check,
            if verdict == ValidationVerdict::Uncovered {
                "none"
            } else {
                "symbolic-region-equivalence"
            }
        );
    }
}

/// [`Session::pass_runs`] maps every transition through [`pass_run_link`]:
/// a non-validated run in the middle of a validated sequence refuses the
/// chain by that run's name and outcome, and stops the recording.
#[test]
fn session_pass_runs_refuse_the_first_unvalidated_run_by_name() {
    let (module, lir) = affine(DARWIN);
    let raw = pipeline(DARWIN, OptLevel::O0)
        .select_ir_function(&lir)
        .expect("selection");
    let start = ct::mach_function_interface(&raw).digest;
    for (verdict, outcome) in [
        (ValidationVerdict::Uncovered, "uncovered"),
        (ValidationVerdict::Refuted("r".into()), "refuted"),
        (ValidationVerdict::Unproved("u".into()), "unproved"),
    ] {
        let mut session = Session::begin(ComposedTransitionPolicy::Require, &lir.name);
        session.legalization(
            Legalization::Checked {
                module: &module,
                ordinal: 0,
            },
            &lir,
            &raw,
        );
        let mut first = transition("gvn", 0, ValidationVerdict::Validated);
        first.before = start;
        let mut second = transition("evil", 7, verdict);
        second.before = first.after;
        let mut third = transition("dce", 9, ValidationVerdict::Validated);
        third.before = second.after;
        session.pass_runs(vec![first, second, third]);
        assert!(!session.recording(), "{outcome}: the chain stops");
        let record = session.finish().expect("a record");
        assert_eq!(record.links.len(), 5, "every run is recorded");
        match record.compose() {
            Err(CompositionRefusal::LinkNotEstablished {
                index: 3,
                name,
                stage: LinkStage::PassRun,
                outcome: found,
                ..
            }) => {
                assert_eq!(name, "evil");
                assert_eq!(found, outcome);
            }
            other => panic!("{outcome}: {other:?}"),
        }
    }
}

/// An optimizer run that is not validated, inside a real preparation: the
/// run goes through the optimizer driver's own validation and transition
/// recording (`test_hooks::optimizer_step`), and the chain refuses it by
/// name under the proof-grade policy and under `record`. A reported rewrite
/// no dedicated validator owns gets the generic region check's verdict for
/// the record only (the proof-grade `enforce` policy does not refuse it), so
/// this link is what refuses it.
#[test]
fn an_unvalidated_optimizer_run_in_a_real_preparation_is_refused_by_name() {
    use super::test_hooks::{OptimizerStep, with_optimizer_step};
    let (module, lir) = affine(DARWIN);
    for level in LEVELS {
        for policy in [
            ComposedTransitionPolicy::Require,
            ComposedTransitionPolicy::Record,
        ] {
            for step in [
                OptimizerStep::ReportedRewrite,
                OptimizerStep::SilentRewrite,
                OptimizerStep::UncoveredStep,
            ] {
                let pipeline = if policy == ComposedTransitionPolicy::Require {
                    pipeline(DARWIN, level).with_proof_grade_aarch64_publication()
                } else {
                    pipeline(DARWIN, level).with_composed_transitions(policy)
                };
                let (_, metrics) = with_optimizer_step(step, || prepare(&pipeline, &module, &lir));
                let record = metrics.composed_transition.expect("a record");
                let expected = match step {
                    OptimizerStep::ReportedRewrite => "unproved",
                    OptimizerStep::SilentRewrite => "refuted",
                    OptimizerStep::UncoveredStep => "uncovered",
                };
                match record.compose() {
                    Err(CompositionRefusal::LinkNotEstablished {
                        name,
                        stage: LinkStage::PassRun,
                        outcome,
                        ..
                    }) => {
                        assert_eq!(name, step.name(), "{level:?} {policy:?}");
                        assert_eq!(outcome, expected, "{level:?} {policy:?} {step:?}");
                    }
                    other => panic!("{level:?} {policy:?} {step:?}: {other:?}\n{record:#?}"),
                }
                assert!(require_composition(&lir.name, Some(&record)).is_err());
            }
        }
    }
}

/// An accepted check whose source has no interface stays in the domain and
/// refuses: it never turns into a function no chain is required for.
#[test]
fn a_checked_source_without_an_interface_refuses_instead_of_leaving_the_domain() {
    let (module, lir) = affine(DARWIN);
    let raw = pipeline(DARWIN, OptLevel::O0)
        .select_ir_function(&lir)
        .expect("selection");
    for outcome in [
        Legalization::Checked {
            module: &module,
            ordinal: 7,
        },
        Legalization::Rejected {
            module: &module,
            ordinal: 7,
            reason: "function ordinal is outside the module".into(),
        },
    ] {
        let mut session = Session::begin(ComposedTransitionPolicy::Require, &lir.name);
        session.legalization(outcome, &lir, &raw);
        assert!(!session.recording());
        let record = session.finish().expect("a record");
        assert!(record.in_legalization_domain());
        assert!(matches!(
            require_composition(&lir.name, Some(&record)),
            Err(CompositionRefusal::LinkNotEstablished {
                stage: LinkStage::Legalization,
                ..
            })
        ));
    }
}

/// The object binding reads the function's whole symbol extent and refuses
/// a relocation inside it: a prefix of the function (ELF `st_size`, or the
/// Mach-O extent past it holding code, not `NOP` padding) and a function
/// whose bytes a relocation patches are refused, on both object formats.
#[test]
fn object_bytes_are_the_whole_symbol_extent_with_no_relocation_inside() {
    for triple in [DARWIN, LINUX] {
        let (module, lir) = affine(triple);
        let plain = pipeline(triple, OptLevel::O2);
        let (func, _) = prepare(&plain, &module, &lir);
        let object = plain
            .compile_module_with_globals(std::slice::from_ref(&func), &[])
            .expect("object");
        let (code, _, _) = crate::pipeline::encode_function_with_fixups_and_sites(&func).unwrap();
        let len = code.len() as u64;
        assert_eq!(
            object_function_bytes(&object, &func.name, len).expect("the whole extent"),
            code
        );
        let prefix = object_function_bytes(&object, &func.name, len - 4)
            .expect_err("a prefix of the function is not its extent");
        assert!(
            prefix.contains("symbol size") || prefix.contains("not NOP padding"),
            "{triple}: {prefix}"
        );

        // A call: its BL word is patched by a relocation.
        let text = format!(
            "; TrustIr text format v1\nmodule \"ct\"\ntarget \"{triple}\" 8 little \
             abi=\"aapcs64\"\nfuncty.0 = (i64) -> (i64)\nexternal fn @ct_ext(functy.0) {{\n}}\n\
             fn @ct_caller(functy.0) {{\nbb0(%0: i64):\n    %1 = call @func.0(%0)\n    \
             ret %1\n}}\n"
        );
        let module = trust_ir::parser::parse_module(&text).expect("parse");
        let caller = module
            .functions
            .iter()
            .find(|function| function.name == "ct_caller")
            .expect("the caller");
        let (lir, _) =
            trust_cg_lower::translate_function_with_license(caller, &module, &permit_unlicensed())
                .expect("adapter");
        let (func, _) = plain
            .prepare_function_with_metrics_and_trust_ir_module(&lir, None, &module, caller)
            .expect("preparation");
        let object = plain
            .compile_module_with_globals(std::slice::from_ref(&func), &[])
            .expect("object");
        let (code, fixups, _) =
            crate::pipeline::encode_function_with_fixups_and_sites(&func).unwrap();
        assert!(!fixups.is_empty(), "{triple}: the call carries a fixup");
        let refusal = object_function_bytes(&object, &func.name, code.len() as u64)
            .expect_err("a relocation inside the bytes");
        assert!(refusal.contains("relocation"), "{triple}: {refusal}");
    }
}
