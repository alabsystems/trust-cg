// trust-cg-lower/tests/box_deref_admission.rs - the shared Box deref acceptance check
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! `trust_cg_lower::admit_box_derefs`, the one acceptance check every target
//! calls for trust-ir v74 `Inst::BoxDeref`, and the adapter's lowering of an
//! admitted one.
//!
//! * the floor: the default refuses every premise; `NamedPremise` admits a
//!   named root and refuses an assumed one; no value weaker than
//!   `NamedPremise` exists;
//! * the manifest: one row per instruction, naming the root and the tier;
//! * rule findings come before floor findings, and each mutation of a fact is
//!   refused under the rule trust-ir names;
//! * the license policy carries the floor, defaults to refusal, and a
//!   non-default floor changes its canonical identity;
//! * no licence: the LIR of a function with an admitted `BoxDeref` is the LIR
//!   of the same function without it plus exactly one `Copy`. Nothing is
//!   removed and no memory access is added or moved.
//!
//! Test rung. Nothing here is proof evidence.

use trust_cg_lower::adapter::AdapterError;
use trust_cg_lower::box_deref::{BoxDerefRefusal, module_has_box_deref};
use trust_cg_lower::instructions::Opcode;
use trust_cg_lower::{
    BoxDerefDisclosure, BoxValidityFloor, CodegenLicensePolicy, Function, UnlicensedBodyPolicy,
    admit_box_derefs, translate_function_with_license,
};
use trust_ir::box_validity::{
    BoxDerefSite, BoxFactSession, BoxValidityFact, BoxValidityTier, PremiseRoot, ValidityConjunct,
    ValidityEvidence,
};
use trust_ir::inst::ICmpOp;
use trust_ir::{Endianness, Module, StructPassingPolicy, TargetInfo, Ty};
use trust_ir_build::ModuleBuilder;

fn target() -> TargetInfo {
    TargetInfo {
        triple: "x86_64-unknown-linux-gnu".to_owned(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: StructPassingPolicy::NativeC,
    }
}

fn fact(root: PremiseRoot, ordinal: u32) -> BoxValidityFact {
    BoxValidityFact::premise(
        BoxDerefSite {
            item: [0x5a; 16],
            ordinal,
        },
        BoxFactSession::PROOF_SNAPSHOT,
        root,
    )
}

/// `f(p: ptr) -> i64`: optionally the deref of `p`, then a null check of the
/// pointer read through, returning -1 on null and the load otherwise. With
/// `fact` absent the body is the same with the parameter used directly: the
/// control the no-licence comparison is made against.
fn module(fact: Option<&BoxValidityFact>) -> Module {
    let mut mb = ModuleBuilder::new_with_target_info("box_deref_admission", target());
    let ft = mb.add_func_type(vec![Ty::Ptr], vec![Ty::I64]);
    let mut fb = mb.function("f", ft);
    let entry = fb.create_block();
    let is_null = fb.create_block();
    let not_null = fb.create_block();
    let pointer = fb.add_block_param(entry, Ty::Ptr);
    fb.switch_to_block(entry);
    let boxed = match fact {
        Some(fact) => fb.box_deref(Ty::I64, pointer, fact.clone()),
        None => pointer,
    };
    let null = fb.null_ptr();
    let cond = fb.icmp(ICmpOp::Eq, Ty::Ptr, boxed, null);
    fb.condbr(cond, is_null, vec![], not_null, vec![]);
    fb.switch_to_block(is_null);
    let minus_one = fb.iconst(Ty::I64, -1);
    fb.ret(vec![minus_one]);
    fb.switch_to_block(not_null);
    let read = fb.load(Ty::I64, boxed);
    fb.ret(vec![read]);
    fb.build();
    mb.build().expect("the module builds")
}

fn reason(result: Result<impl std::fmt::Debug, AdapterError>) -> BoxDerefRefusal {
    match result {
        Ok(value) => panic!("admitted: {value:?}"),
        Err(AdapterError::BoxDerefNotAdmitted { reason, .. }) => reason,
        Err(other) => panic!("refused, but not as a BoxDeref: {other}"),
    }
}

#[test]
fn the_floor_has_two_values_and_the_default_refuses() {
    assert_eq!(BoxValidityFloor::default(), BoxValidityFloor::Refuse);
    assert_eq!(
        BoxValidityFloor::MOST_PERMISSIVE,
        BoxValidityFloor::NamedPremise
    );
    assert_eq!(
        BoxValidityFloor::Refuse.tier(),
        BoxValidityTier::ConsumerRederived
    );
    assert_eq!(
        BoxValidityFloor::NamedPremise.tier(),
        BoxValidityTier::NamedPremise
    );
    // The floor is never below trust-ir's named-premise tier.
    for floor in [BoxValidityFloor::Refuse, BoxValidityFloor::NamedPremise] {
        assert!(floor.tier() >= BoxValidityTier::NamedPremise);
    }
}

/// The exact verdict of each premise root over the parameter-only fixture,
/// at each floor. The fixture has a by-value parameter and no allocation or
/// call, so only `param_by_value` and `reference_arg_box_valid` are decided
/// by the FLOOR here; the other three roots are refused by trust-ir's rule 9
/// (`BoxDerefPremiseContradicted`) at both floors, before any floor is read.
/// This test therefore does NOT show `alloc_postcondition` or
/// `returned_box_discharged` admitted, nor the floor refusing
/// `returned_box_assumed`: no fixture in this backend does yet.
#[test]
fn each_root_of_the_parameter_only_fixture_gets_its_exact_verdict_at_each_floor() {
    #[derive(Debug, PartialEq, Eq)]
    enum Verdict {
        Admitted,
        BelowFloor {
            tier: &'static str,
            floor: &'static str,
        },
        Rule(&'static str),
    }
    let verdict = |root, floor| -> Verdict {
        match admit_box_derefs(&module(Some(&fact(root, 0))), floor) {
            Ok(manifest) => {
                assert_eq!(manifest.rows.len(), 1, "{root:?}");
                assert_eq!(manifest.rows[0].root, root);
                Verdict::Admitted
            }
            Err(error) => match reason(Err::<(), _>(error)) {
                BoxDerefRefusal::EvidenceBelowFloor { tier, floor, .. } => {
                    Verdict::BelowFloor { tier, floor }
                }
                BoxDerefRefusal::FactRefused { rule, .. } => Verdict::Rule(rule),
                other => panic!("{root:?} at {floor:?}: {other:?}"),
            },
        }
    };
    let contradicted = Verdict::Rule("BoxDerefPremiseContradicted");
    let mut seen = 0;
    for root in PremiseRoot::ALL {
        let (at_refuse, at_named) = match root {
            PremiseRoot::ParamByValue => (
                Verdict::BelowFloor {
                    tier: "named_premise",
                    floor: "consumer_rederived",
                },
                Verdict::Admitted,
            ),
            PremiseRoot::ReferenceArgBoxValid => (
                Verdict::BelowFloor {
                    tier: "assumed_root_premise",
                    floor: "consumer_rederived",
                },
                Verdict::BelowFloor {
                    tier: "assumed_root_premise",
                    floor: "named_premise",
                },
            ),
            PremiseRoot::AllocPostcondition
            | PremiseRoot::ReturnedBoxDischarged
            | PremiseRoot::ReturnedBoxAssumed => (
                Verdict::Rule("BoxDerefPremiseContradicted"),
                Verdict::Rule("BoxDerefPremiseContradicted"),
            ),
        };
        assert_eq!(
            verdict(root, BoxValidityFloor::Refuse),
            at_refuse,
            "{root:?}"
        );
        assert_eq!(
            verdict(root, BoxValidityFloor::NamedPremise),
            at_named,
            "{root:?}"
        );
        // No root is admitted at the default floor.
        assert_ne!(at_refuse, Verdict::Admitted);
        seen += usize::from(at_named != contradicted);
    }
    assert_eq!(seen, 2, "exactly two roots are decided by the floor here");
    // The named root this body satisfies is admitted at the opt-in floor.
    let admitted = module(Some(&fact(PremiseRoot::ParamByValue, 0)));
    let manifest = admit_box_derefs(&admitted, BoxValidityFloor::NamedPremise).expect("admitted");
    assert_eq!(manifest.floor, BoxValidityFloor::NamedPremise);
    assert_eq!(manifest.rows.len(), 1);
    assert_eq!(manifest.rows[0].function, "f");
    assert_eq!(manifest.rows[0].root, PremiseRoot::ParamByValue);
    assert_eq!(manifest.rows[0].tier, BoxValidityTier::NamedPremise);
    assert_eq!(manifest.rows[0].site.ordinal, 0);
    assert!(manifest.disclosure().is_some(), "an admission is disclosed");
}

#[test]
fn a_module_without_a_box_deref_has_an_empty_manifest_at_every_floor() {
    let plain = module(None);
    assert!(!module_has_box_deref(&plain));
    for floor in [BoxValidityFloor::Refuse, BoxValidityFloor::NamedPremise] {
        let manifest = admit_box_derefs(&plain, floor).expect("nothing to refuse");
        assert!(manifest.rows.is_empty());
        assert!(manifest.disclosure().is_none());
    }
}

/// Each mutation of an admitted fact is refused at the opt-in floor, under
/// the trust-ir rule named. The unmutated fact is the control: it is admitted
/// in the test above, so every refusal here is the mutation's.
#[test]
fn a_mutated_fact_is_refused_under_the_rule_trust_ir_names() {
    type Mutation = (&'static str, fn(&mut BoxValidityFact), &'static str);
    let mutations: [Mutation; 4] = [
        (
            "a conjunct's evidence replaced by a reserved kind",
            |fact| fact.evidence[0].evidence = ValidityEvidence::DominatingCheck { align: None },
            "BoxDerefDominatingCheckInvalid",
        ),
        (
            "a conjunct stripped",
            |fact| {
                fact.evidence
                    .retain(|entry| entry.conjunct != ValidityConjunct::Dereferenceable);
            },
            "BoxDerefConjunctCover",
        ),
        (
            "a non-claim dropped",
            |fact| {
                fact.not_claimed.pop();
            },
            "BoxDerefNonClaimsNotPinned",
        ),
        (
            "every non-claim dropped",
            |fact| fact.not_claimed.clear(),
            "BoxDerefNonClaimsNotPinned",
        ),
    ];
    for (name, mutate, rule) in mutations {
        let mut mutated = fact(PremiseRoot::ParamByValue, 0);
        mutate(&mut mutated);
        let module = module(Some(&mutated));
        // A rule finding is reported at both floors: it comes before the
        // floor's own finding, so the default does not mask it.
        for floor in [BoxValidityFloor::NamedPremise, BoxValidityFloor::Refuse] {
            match reason(admit_box_derefs(&module, floor)) {
                BoxDerefRefusal::FactRefused { rule: found, .. } => {
                    assert_eq!(found, rule, "{name} at {floor:?}");
                }
                other => panic!("{name} at {floor:?}: {other:?}"),
            }
        }
    }
}

#[test]
fn the_license_policy_carries_the_floor_and_defaults_to_refusal() {
    let default = CodegenLicensePolicy::default().with_unlicensed(UnlicensedBodyPolicy::Permit);
    assert_eq!(default.box_validity_floor(), BoxValidityFloor::Refuse);
    let disclosure = BoxDerefDisclosure::new();
    let opted = default.clone().with_named_premise_box_floor(&disclosure);
    assert_eq!(opted, opted.clone(), "a policy equals its clone");
    assert_ne!(
        opted,
        default
            .clone()
            .with_named_premise_box_floor(&BoxDerefDisclosure::new()),
        "policies reporting to different places are different policies"
    );
    assert_eq!(opted.box_validity_floor(), BoxValidityFloor::NamedPremise);
    // A cache keyed by the policy identity never serves an opt-in compile's
    // artifact to a default compile.
    assert_ne!(default.canonical_identity(), opted.canonical_identity());
    assert!(
        !default.canonical_identity().contains("box_validity_floor"),
        "the default identity is the pre-v67 identity"
    );

    let module = module(Some(&fact(PremiseRoot::ParamByValue, 0)));
    assert!(matches!(
        reason(default.admit_box_derefs(&module)),
        BoxDerefRefusal::EvidenceBelowFloor { .. }
    ));
    assert!(matches!(
        reason(default.enforce_module(&module)),
        BoxDerefRefusal::EvidenceBelowFloor { .. }
    ));
    let id = module.functions[0].id;
    assert!(matches!(
        reason(default.verdict(&module, id)),
        BoxDerefRefusal::EvidenceBelowFloor { .. }
    ));
    // A refusal reports nothing: nothing was compiled under an assumption.
    assert!(disclosure.is_empty());
    // Each license verdict that admits reports before it returns; a repeat
    // of the same verdict is one record.
    let entries: [(&str, Verdict); 4] = [
        ("enforce_module", |policy, module, _| {
            policy.enforce_module(module)
        }),
        ("verdict", |policy, module, id| policy.verdict(module, id)),
        ("census_module", |policy, module, _| {
            policy.census_module(module).map(|refusals| {
                assert!(refusals.is_empty(), "{refusals:?}");
            })
        }),
        ("admit_box_derefs", |policy, module, _| {
            policy.admit_box_derefs(module).map(|manifest| {
                assert_eq!(manifest.rows.len(), 1);
            })
        }),
    ];
    for (entry, run) in entries {
        let disclosure = BoxDerefDisclosure::new();
        let opted = default.clone().with_named_premise_box_floor(&disclosure);
        assert_eq!(
            opted.box_deref_disclosure(),
            Some(&disclosure),
            "the policy names its report"
        );
        run(&opted, &module, id).unwrap_or_else(|error| panic!("{entry}: {error}"));
        run(&opted, &module, id).unwrap_or_else(|error| panic!("{entry}: {error}"));
        let records = disclosure.records();
        assert_eq!(records.len(), 1, "{entry}: {records:?}");
        assert_eq!(records[0].module, module.name, "{entry}");
        assert_eq!(records[0].manifest.floor, BoxValidityFloor::NamedPremise);
        assert_eq!(records[0].manifest.rows.len(), 1, "{entry}");
        assert_eq!(records[0].manifest.rows[0].root, PremiseRoot::ParamByValue);
        let lines = disclosure.lines();
        assert!(
            lines.len() == 1
                && lines[0].contains("admitted for compilation under named assumptions")
                && lines[0].contains("assumed for admission, not established"),
            "{entry}: {lines:?}"
        );
    }
    // A module holding no `BoxDeref` assumed nothing and reports nothing.
    let disclosure = BoxDerefDisclosure::new();
    let opted = default.clone().with_named_premise_box_floor(&disclosure);
    opted
        .enforce_module(&crate::module(None))
        .expect("nothing to refuse");
    assert!(disclosure.is_empty());
}

/// One license verdict over a module and a function id.
type Verdict = fn(
    &CodegenLicensePolicy,
    &trust_ir::Module,
    trust_ir::FuncId,
) -> Result<(), trust_cg_lower::adapter::AdapterError>;

/// The LIR opcodes of `function`, by variant name, sorted.
fn opcode_names(function: &Function) -> Vec<String> {
    let mut names: Vec<String> = function
        .blocks
        .values()
        .flat_map(|block| &block.instructions)
        .map(|inst| {
            let debug = format!("{:?}", inst.opcode);
            debug
                .split(|c: char| !c.is_alphanumeric() && c != '_')
                .next()
                .unwrap_or_default()
                .to_owned()
        })
        .collect();
    names.sort();
    names
}

/// The no-licence clause, structurally: lowering an admitted `BoxDeref` adds
/// one `Copy` to the LIR of the same function without it and changes nothing
/// else. The null check after the deref and the load are both still there.
#[test]
fn an_admitted_box_deref_lowers_to_one_copy_and_takes_no_licence() {
    let license = CodegenLicensePolicy::default()
        .with_unlicensed(UnlicensedBodyPolicy::Permit)
        .with_named_premise_box_floor(&BoxDerefDisclosure::new());
    let with = module(Some(&fact(PremiseRoot::ParamByValue, 0)));
    let without = module(None);
    let (lowered_with, _) =
        translate_function_with_license(&with.functions[0], &with, &license).expect("admitted");
    let (lowered_without, _) =
        translate_function_with_license(&without.functions[0], &without, &license)
            .expect("the control lowers");

    let with_names = opcode_names(&lowered_with);
    let mut expected = opcode_names(&lowered_without);
    expected.push("Copy".to_owned());
    expected.sort();
    assert_eq!(
        with_names, expected,
        "the BoxDeref must add exactly one Copy and nothing else"
    );
    assert_eq!(
        lowered_with.blocks.len(),
        lowered_without.blocks.len(),
        "no block is removed or added"
    );
    // The copy reads the parameter, and nothing in the function reads memory
    // that the control does not.
    let copies: Vec<_> = lowered_with
        .blocks
        .values()
        .flat_map(|block| &block.instructions)
        .filter(|inst| matches!(inst.opcode, Opcode::Copy))
        .collect();
    let control_copies = lowered_without
        .blocks
        .values()
        .flat_map(|block| &block.instructions)
        .filter(|inst| matches!(inst.opcode, Opcode::Copy))
        .count();
    assert_eq!(copies.len(), control_copies + 1);
}

/// The single-function entry refuses under the default license with the same
/// typed error the module entries return.
#[test]
fn the_function_entry_refuses_under_the_default_license() {
    let license = CodegenLicensePolicy::default().with_unlicensed(UnlicensedBodyPolicy::Permit);
    let module = module(Some(&fact(PremiseRoot::ParamByValue, 0)));
    let error = translate_function_with_license(&module.functions[0], &module, &license)
        .map(|_| ())
        .expect_err("refused");
    let text = error.to_string();
    assert!(
        matches!(
            error,
            AdapterError::BoxDerefNotAdmitted {
                reason: BoxDerefRefusal::EvidenceBelowFloor { .. },
                ..
            }
        ),
        "{text}"
    );
    assert!(text.contains("function `f` bb0#0"), "{text}");
    assert!(text.contains("named_premise"), "{text}");
    assert!(text.contains("consumer_rederived"), "{text}");
}
