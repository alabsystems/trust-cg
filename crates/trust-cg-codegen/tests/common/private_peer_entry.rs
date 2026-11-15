// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
//! Private lifetime and exact-final-image controls; no public proof mint.
use super::*;
use crate as cg;
#[path = "defined_call_fixture.rs"]
mod fixture;

#[test]
fn bound_peer_rejects_drift_and_certificate_dies_with_real_storage() {
    let (module, target, _) = fixture::certified(42).unwrap();
    let conditional = fixture::qualified_plan(module, target)
        .compile_for_owned_peer_entry("entry")
        .unwrap();
    let ConditionalCorePeerArtifact { plan, prepared } = conditional;
    let PreparedPeer {
        previous,
        caller,
        source_function,
        final_code,
        verifier_input,
        link,
        inventory,
        ..
    } = prepared;
    let check =
        |module: &trust_ir::Module, code: &[u8], inventory: &CoreAddressFreeFixupInventory| {
            link.check_prepared(
                module,
                &previous,
                source_function,
                &caller.name,
                caller.text_align_log2,
                code,
                inventory,
            )
        };
    check(&plan.plan.parts.module, &final_code, &inventory).unwrap();
    println!(
        "CORE_PEER_FINAL_CALLER_HEX={}",
        final_code
            .iter()
            .map(|b| format!("{b:02x}"))
            .collect::<String>()
    );
    println!(
        "CORE_PEER_FINAL_IMAGE_DIGEST={}",
        link.requirement().final_image_digest()
    );
    println!(
        "CORE_PEER_ORIGINAL_CALLER_ROWS={:?} arena_slots={}",
        caller.blocks[caller.entry.0 as usize].insts,
        caller.insts.len()
    );

    let mut foreign_source = plan.plan.parts.module.as_ref().clone();
    foreign_source.name.push_str("_foreign");
    assert!(check(&foreign_source, &final_code, &inventory).is_err());
    // Keep source bodies unchanged but mutate an actual source certificate.
    let mut foreign_certificate = plan.plan.parts.module.as_ref().clone();
    foreign_certificate.proof_certificates.pop();
    assert!(check(&foreign_certificate, &final_code, &inventory).is_err());
    for word in [0xd503201fu32, 0x94000000, 0x94000001, 0x95ffffff] {
        let mut wrong_code = final_code.clone();
        wrong_code[8..12].copy_from_slice(&word.to_le_bytes());
        assert!(check(&plan.plan.parts.module, &wrong_code, &inventory).is_err());
    }
    let mut wrong_site = inventory.clone();
    wrong_site.entries[0].offset = 12;
    assert!(check(&plan.plan.parts.module, &final_code, &wrong_site).is_err());
    let mut foreign_target = inventory.clone();
    foreign_target.entries[0].target = CoreAddressFreeFixupTarget::ExactModuleFunction {
        function: trust_ir::FuncId::new(999),
    };
    assert!(check(&plan.plan.parts.module, &final_code, &foreign_target).is_err());
    let mut empty_inventory = inventory.clone();
    empty_inventory.entries.clear();
    assert!(check(&plan.plan.parts.module, &final_code, &empty_inventory).is_err());
    for displacement in [2, -134_217_732, 134_217_728, i64::MIN, i64::MAX] {
        let mut original = 0x94000000u32.to_le_bytes();
        assert!(crate::macho::fixup::apply_branch26(&mut original, displacement).is_err());
        assert_eq!(original, 0x94000000u32.to_le_bytes());
    }
    assert!(
        !link
            .replay()
            .diagnostic_report()
            .emitted_opcode_inventory()
            .is_promotable()
    );
    let mut wrong_requirement =
        SourceEntryStackRequirement::from_conditional_peer(link.requirement()).unwrap();
    wrong_requirement.function += 1;
    let mut different_source_stack = OwnedEntryStack::allocate(16).unwrap();
    {
        let different_source_loan = different_source_stack
            .borrow_invocation(&wrong_requirement)
            .unwrap();
        assert!(matches!(
            different_source_loan.bind_peer_requirement(link.requirement()),
            Err(EntryStackError::StaleInvocation)
        ));
    }
    let stack = OwnedEntryStack::allocate(16).unwrap();
    let storage =
        CoreBoundPeerProof::new(stack, link, caller.name.clone(), verifier_input).unwrap();
    let (certificate, _) = storage
        .issue_caller_certificate(&caller, &final_code)
        .unwrap();
    let copy = certificate.clone();
    assert!(copy.is_verified());
    assert!(copy.has_checked_semantics());
    assert!(copy.replay_check());
    assert_eq!(copy.coverage_percent(), 100.0);
    drop(storage);
    assert!(!certificate.is_verified());
    assert!(!copy.has_checked_semantics());
    assert!(!copy.replay_check());
    assert_eq!(copy.coverage_percent(), 0.0);
    let json: serde_json::Value = serde_json::from_str(&copy.to_json()).unwrap();
    assert_eq!(json["verified"], false);
    assert_eq!(json["coverage_percent"], 0.0);
    println!("CORE_PEER_PRIVATE_FINAL_BINDING_AND_STORAGE_LIFETIME_CONTROLS=PASS");
}
