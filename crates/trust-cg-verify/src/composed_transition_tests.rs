// trust-cg-verify/composed_transition_tests.rs - composed transition chain tests
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use super::*;

const CODE: [u8; 8] = [0x00, 0x00, 0x01, 0x8b, 0xc0, 0x03, 0x5f, 0xd6];

fn iface(representation: Representation, n: u8) -> Interface {
    Interface {
        representation,
        digest: [n; 32],
    }
}

fn link(stage: LinkStage, name: &str, from: Interface, to: Interface) -> TransitionLink {
    TransitionLink {
        stage,
        name: name.to_string(),
        relation: format!("{} relation", stage.as_str()),
        check: "test".to_string(),
        model: "test model".to_string(),
        from,
        to,
        to_len: (to.representation == Representation::Bytes).then_some(CODE.len() as u64),
        strength: EvidenceStrength::ExactlyDecided,
        verdict: LinkVerdict::Established,
    }
}

/// TrustIR -> LIR -> raw -> (pass) -> pre-RA -> (post-RA) -> final -> bytes.
fn chain() -> TransitionRecord {
    let t = iface(Representation::TrustIr, 1);
    let l = iface(Representation::Lir, 2);
    let raw = iface(Representation::MachIr, 3);
    let pre_ra = iface(Representation::MachIr, 4);
    let last = iface(Representation::MachIr, 5);
    let bytes = bytes_interface(&CODE);
    let mut record = TransitionRecord::new("f");
    record.push(link(LinkStage::Legalization, "trust-ir->lir", t, l));
    record.push(link(LinkStage::Selection, "lir->raw-mach-ir", l, raw));
    record.push(link(LinkStage::PassRun, "dce", raw, pre_ra));
    record.push(link(
        LinkStage::PostAllocation,
        "post-ra-value-flow",
        pre_ra,
        last,
    ));
    record.push(link(LinkStage::Encoding, "encode", last, bytes));
    record
}

#[test]
fn a_complete_chain_composes() {
    let composed = chain().compose().expect("the chain composes");
    assert_eq!(composed.function, "f");
    assert_eq!(composed.origin, iface(Representation::TrustIr, 1));
    assert_eq!(composed.terminal, bytes_interface(&CODE));
    assert_eq!(composed.terminal_len, Some(CODE.len() as u64));
    assert_eq!(composed.links, 5);
    assert_eq!(composed.pass_runs, 1);
    assert_eq!(composed.strength, EvidenceStrength::ExactlyDecided);
    // The composition carries what it establishes and every link's strength.
    assert_eq!(composed.claim, ComposedTransition::CLAIM);
    assert_eq!(
        composed
            .link_strengths
            .iter()
            .map(|(stage, _, strength)| (*stage, *strength))
            .collect::<Vec<_>>(),
        chain()
            .links
            .iter()
            .map(|link| (link.stage, link.strength))
            .collect::<Vec<_>>()
    );
    let text = serde_json::to_string(&composed).unwrap();
    assert!(text.contains("\"claim\""), "{text}");
    composed.check_published(&CODE).expect("the encoded bytes");
    composed
        .check_origin(&iface(Representation::TrustIr, 1))
        .expect("its source");
}

#[test]
fn no_pass_runs_and_split_post_allocation_windows_compose() {
    let mut record = chain();
    // Drop the pass run and start the post-allocation link at the raw MachIR.
    record.links.remove(2);
    record.links[2].from = record.links[1].to;
    assert_eq!(record.compose().expect("composes").pass_runs, 0);

    let mut split = chain();
    let allocated = iface(Representation::MachIr, 9);
    let final_ir = split.links[3].to;
    split.links[3].to = allocated;
    split.links[3].name = "post-ra-allocation".into();
    split.links.insert(
        4,
        link(
            LinkStage::PostAllocation,
            "post-ra-frame-layout",
            allocated,
            final_ir,
        ),
    );
    assert_eq!(split.compose().expect("split windows compose").links, 6);
}

#[test]
fn corruption_dropping_any_link_is_refused_by_name() {
    for index in 0..chain().links.len() {
        let mut record = chain();
        let dropped = record.links.remove(index);
        let refusal = record.compose().expect_err("a dropped link refuses");
        match dropped.stage {
            LinkStage::PassRun => assert!(
                matches!(
                    &refusal,
                    CompositionRefusal::InterfaceMismatch { left_name, right_name, .. }
                        if left_name == "lir->raw-mach-ir" && right_name == "post-ra-value-flow"
                ),
                "dropping the pass run leaves its mutation unchecked: {refusal}"
            ),
            stage => assert!(
                matches!(
                    &refusal,
                    CompositionRefusal::MissingLink { stage: missing, .. } if *missing == stage
                ),
                "dropping {} must name it missing: {refusal}",
                stage.as_str()
            ),
        }
        assert!(refusal.to_string().starts_with(TAG), "{refusal}");
    }
}

#[test]
fn corruption_a_swapped_interface_hash_is_refused() {
    for index in 0..chain().links.len() {
        for end in ["from", "to"] {
            let mut record = chain();
            let link = &mut record.links[index];
            let target = if end == "from" {
                &mut link.from
            } else {
                &mut link.to
            };
            target.digest[0] ^= 0x80;
            let refusal = record.compose();
            // The chain's two outer ends have no neighbour: the origin and
            // the published bytes are checked against the route instead.
            let outer =
                (index == 0 && end == "from") || (index == chain().links.len() - 1 && end == "to");
            if outer {
                let composed = refusal.expect("an outer end has no neighbour");
                if index == 0 {
                    assert!(matches!(
                        composed.check_origin(&iface(Representation::TrustIr, 1)),
                        Err(CompositionRefusal::OriginMismatch { .. })
                    ));
                } else {
                    assert!(matches!(
                        composed.check_published(&CODE),
                        Err(CompositionRefusal::PublishedBytesMismatch { .. })
                    ));
                }
                continue;
            }
            let expected = if end == "from" { index - 1 } else { index };
            assert!(
                matches!(
                    &refusal,
                    Err(CompositionRefusal::InterfaceMismatch { index: at, .. }) if *at == expected
                ),
                "link {index} {end}: {refusal:?}"
            );
        }
    }
    // Swapping two links' digests moves both ends.
    let mut record = chain();
    let (a, b) = (record.links[1].to, record.links[2].to);
    record.links[1].to = b;
    record.links[2].to = a;
    assert!(matches!(
        record.compose(),
        Err(CompositionRefusal::InterfaceMismatch { index: 1, .. })
    ));
}

#[test]
fn corruption_an_inserted_unvalidated_pass_is_refused() {
    // A run recorded but not validated.
    let mut record = chain();
    let pre_ra = record.links[2].to;
    let mutated = iface(Representation::MachIr, 7);
    record.links[2].to = mutated;
    let mut unvalidated = link(LinkStage::PassRun, "evil-pass", mutated, pre_ra);
    unvalidated.verdict = LinkVerdict::NotEstablished {
        outcome: "uncovered".into(),
        reason: "no validator covers this pass".into(),
    };
    record.links.insert(3, unvalidated);
    let refusal = record.compose().expect_err("an unvalidated run refuses");
    assert!(
        matches!(
            &refusal,
            CompositionRefusal::LinkNotEstablished { index: 3, name, stage: LinkStage::PassRun, outcome, .. }
                if name == "evil-pass" && outcome == "uncovered"
        ),
        "{refusal}"
    );
    // A mutation with no record at all.
    let mut silent = chain();
    silent.links[3].from = iface(Representation::MachIr, 7);
    assert!(matches!(
        silent.compose(),
        Err(CompositionRefusal::InterfaceMismatch { index: 2, .. })
    ));
}

#[test]
fn corruption_bytes_mutated_after_the_last_link_are_refused() {
    let composed = chain().compose().expect("composes");
    for position in 0..CODE.len() {
        let mut published = CODE;
        published[position] ^= 1;
        let refusal = composed
            .check_published(&published)
            .expect_err("a changed byte refuses");
        assert_eq!(refusal.class(), "published-bytes-mismatch");
        assert_eq!(refusal.stage(), Some(LinkStage::Encoding));
    }
    let mut longer = CODE.to_vec();
    longer.extend_from_slice(&[0x1f, 0x20, 0x03, 0xd5]);
    assert!(composed.check_published(&longer).is_err());
    assert!(composed.check_published(&CODE[..4]).is_err());
}

#[test]
fn out_of_order_duplicate_and_mistyped_links_are_refused() {
    // Encoding before the post-allocation comparison skips a required stage.
    let mut swapped = chain();
    swapped.links.swap(3, 4);
    assert!(matches!(
        swapped.compose(),
        Err(CompositionRefusal::MissingLink {
            stage: LinkStage::PostAllocation,
            ..
        })
    ));
    let mut backwards = chain();
    backwards.links.swap(0, 1);
    assert!(matches!(
        backwards.compose(),
        Err(CompositionRefusal::MissingLink {
            stage: LinkStage::Legalization,
            ..
        })
    ));
    let mut reselected = chain();
    let selection = reselected.links[1].clone();
    reselected.links.insert(3, selection);
    assert!(matches!(
        reselected.compose(),
        Err(CompositionRefusal::OutOfOrder {
            index: 3,
            stage: LinkStage::Selection,
            after: LinkStage::PassRun,
            ..
        })
    ));
    let mut duplicated = chain();
    let again = duplicated.links[4].clone();
    duplicated.links.push(again);
    assert!(matches!(
        duplicated.compose(),
        Err(CompositionRefusal::OutOfOrder {
            index: 5,
            stage: LinkStage::Encoding,
            ..
        })
    ));
    let mut mistyped = chain();
    mistyped.links[2].to.representation = Representation::Bytes;
    assert!(matches!(
        mistyped.compose(),
        Err(CompositionRefusal::RepresentationMismatch { index: 2, .. })
    ));
    // A pass run after the post-allocation comparison, interfaces chained.
    let mut late_pass = chain();
    let pass = late_pass.links.remove(2);
    late_pass.links.insert(3, pass);
    for index in 2..late_pass.links.len() {
        late_pass.links[index].from = late_pass.links[index - 1].to;
        if index < late_pass.links.len() - 1 {
            late_pass.links[index].to = iface(Representation::MachIr, 20 + index as u8);
        }
    }
    assert!(matches!(
        late_pass.compose(),
        Err(CompositionRefusal::OutOfOrder {
            stage: LinkStage::PassRun,
            after: LinkStage::PostAllocation,
            ..
        })
    ));
    let mut empty = TransitionRecord::new("f");
    assert!(matches!(
        empty.compose(),
        Err(CompositionRefusal::MissingLink {
            stage: LinkStage::Legalization,
            ..
        })
    ));
    empty.format = "other".into();
    assert_eq!(empty.compose().unwrap_err().class(), "format");
}

#[test]
fn a_not_composed_record_is_refused_whatever_its_links() {
    let mut record = chain();
    record.mark_not_composed(LinkStage::Legalization, "unsupported affine TrustIR: mul");
    record.mark_not_composed(LinkStage::Encoding, "second reason is ignored");
    assert!(!record.is_open());
    let refusal = record.compose().expect_err("not composed");
    assert!(
        matches!(&refusal, CompositionRefusal::NotComposed { stage: LinkStage::Legalization, reason, .. } if reason.contains("mul")),
        "{refusal}"
    );
    assert!(!record.in_legalization_domain());
    let fresh = TransitionRecord::not_composed("g", LinkStage::Legalization, "no TrustIR source");
    assert_eq!(
        fresh.compose().unwrap_err().stage(),
        Some(LinkStage::Legalization)
    );
    let mut late = chain();
    late.links.truncate(4);
    late.mark_not_composed(LinkStage::Encoding, "the encoder refused");
    assert!(
        late.in_legalization_domain(),
        "a later stage stays in the domain"
    );
    assert!(chain().in_legalization_domain());
}

#[test]
fn strength_is_the_weakest_links_and_never_upgraded() {
    let mut record = chain();
    for link in &mut record.links {
        link.strength = EvidenceStrength::Formal;
    }
    assert_eq!(record.compose().unwrap().strength, EvidenceStrength::Formal);
    record.links[3].strength = EvidenceStrength::ExactlyDecided;
    assert_eq!(
        record.compose().unwrap().strength,
        EvidenceStrength::ExactlyDecided
    );
    record.links[2].strength = EvidenceStrength::Statistical;
    let composed = record.compose().unwrap();
    assert_eq!(composed.strength, EvidenceStrength::Statistical);
    // The other links keep their own strengths; none is lowered or raised.
    assert_eq!(composed.link_strengths[2].2, EvidenceStrength::Statistical);
    assert_eq!(
        composed.link_strengths[3].2,
        EvidenceStrength::ExactlyDecided
    );
    assert_eq!(composed.link_strengths[0].2, EvidenceStrength::Formal);
    let refusal = record
        .compose_at_least(EvidenceStrength::ExactlyDecided)
        .expect_err("a statistical link is too weak");
    assert!(
        matches!(&refusal, CompositionRefusal::InsufficientStrength { weakest, strength: EvidenceStrength::Statistical, .. } if weakest == "dce"),
        "{refusal}"
    );
    assert!(
        record
            .compose_at_least(EvidenceStrength::Statistical)
            .is_ok()
    );
    assert!(EvidenceStrength::Statistical < EvidenceStrength::ExactlyDecided);
    assert!(EvidenceStrength::ExactlyDecided < EvidenceStrength::Formal);
}

#[test]
fn records_round_trip_through_json() {
    let mut record = chain();
    record.links[2].verdict = LinkVerdict::NotEstablished {
        outcome: "unproved".into(),
        reason: "r".into(),
    };
    let text = serde_json::to_string(&record).unwrap();
    let back: TransitionRecord = serde_json::from_str(&text).unwrap();
    assert_eq!(back, record);
    let refusal = back.compose().unwrap_err();
    let text = serde_json::to_string(&refusal).unwrap();
    assert!(text.contains("link-not-established"), "{text}");
}

fn module(body: &str, functy: &str, name: &str) -> trust_ir::Module {
    let text = format!(
        "; TrustIr text format v1\nmodule \"ct\"\ntarget \"aarch64-apple-darwin\" 8 little abi=\"aapcs64\"\n\
         functy.0 = {functy}\nfn @{name}(functy.0) {{\n{body}}}\n"
    );
    trust_ir::parser::parse_module(&text).unwrap_or_else(|error| panic!("{error:?}\n{text}"))
}

#[test]
fn interface_digests_separate_programs_and_representations() {
    let add = module(
        "bb0(%0: i64, %1: i64):\n    %2 = add i64 %0, %1\n    ret %2\n",
        "(i64, i64) -> (i64)",
        "f",
    );
    let sub = module(
        "bb0(%0: i64, %1: i64):\n    %2 = sub i64 %0, %1\n    ret %2\n",
        "(i64, i64) -> (i64)",
        "f",
    );
    let t_add = trust_ir_function_interface(&add, 0).expect("in the module");
    let t_sub = trust_ir_function_interface(&sub, 0).expect("in the module");
    assert_eq!(t_add.representation, Representation::TrustIr);
    assert_ne!(t_add, t_sub);
    assert_eq!(Some(t_add), trust_ir_function_interface(&add, 0));
    assert!(trust_ir_function_interface(&add, 1).is_none());

    // Hand-built fixtures carry no codegen license; the test states Permit.
    let permit = trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit);
    let (lir_add, _) =
        trust_cg_lower::translate_function_with_license(&add.functions[0], &add, &permit).unwrap();
    let (lir_sub, _) =
        trust_cg_lower::translate_function_with_license(&sub.functions[0], &sub, &permit).unwrap();
    let l_add = lir_function_interface(&lir_add);
    assert_eq!(l_add.representation, Representation::Lir);
    assert_ne!(l_add, lir_function_interface(&lir_sub));
    assert_eq!(l_add, lir_function_interface(&lir_add.clone()));
    assert_ne!(l_add.digest, t_add.digest);

    let mut mach =
        trust_cg_ir::MachFunction::new("f".into(), trust_cg_ir::Signature::new(vec![], vec![]));
    let m0 = mach_function_interface(&mach);
    assert_eq!(m0.digest, mach_function_interface_digest(&mach));
    let entry = mach.entry;
    let ret = mach.push_inst(trust_cg_ir::MachInst::new(
        trust_cg_ir::AArch64Opcode::Ret,
        vec![],
    ));
    mach.append_inst(entry, ret);
    assert_ne!(m0, mach_function_interface(&mach));

    let b = bytes_interface(&CODE);
    assert_eq!(b.digest, <[u8; 32]>::from(Sha256::digest(CODE)));
    assert_eq!(b.hex().len(), 64);
    assert!(b.to_string().starts_with("bytes:"));
}
