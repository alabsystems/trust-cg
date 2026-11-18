// Copyright 2026 Andrew Yates | Apache-2.0
//! Real replay/storage controls. No test-only replay receipt or permission mint.
use super::*;
use crate as cg;
#[path = "context_output_fixture.rs"]
mod fixture;

#[test]
fn bound_void_entry_refuses_storage_drift_aliases_and_expires_with_its_owner() {
    fixture::source_mutations_refuse();
    let module = fixture::certified(true, false);
    let generation = CompileGeneration::new(17);
    let manifest = fixture::manifest(&module, generation);
    let (mut entry, _) = fixture::plan(module)
        .compile_install_owned_context_output(
            OwnedEntryContext::from_words(vec![42, u64::MAX, 7, 8, 9]).unwrap(),
            OwnedEntryOutput::allocate_words(5).unwrap(),
            OwnedEntryStack::allocate(65_536).unwrap(),
            manifest,
            generation,
        )
        .expect("actual complete original replay and real installed owner required");
    let certificate = entry
        .installed
        .buffer
        .certificate(&entry.owner.function)
        .unwrap()
        .clone();
    assert!(certificate.is_verified());
    assert!(certificate.has_checked_semantics());
    assert!(certificate.replay_check());
    assert_eq!(certificate.coverage_percent(), 100.0);
    let original_output = {
        let mut storage = entry.owner.storage.lock().unwrap();
        std::mem::replace(
            &mut storage.output,
            OwnedEntryOutput::allocate_words(5).unwrap(),
        )
    };
    assert!(matches!(
        entry.invoke(),
        Err(EntryStackError::StaleInvocation)
    ));
    let replacement = {
        let mut storage = entry.owner.storage.lock().unwrap();
        std::mem::replace(&mut storage.output, original_output)
    };
    drop(replacement);
    let original_context = {
        let mut storage = entry.owner.storage.lock().unwrap();
        std::mem::replace(
            &mut storage.context,
            OwnedEntryContext::from_words(vec![42; 5]).unwrap(),
        )
    };
    assert!(matches!(
        entry.invoke(),
        Err(EntryStackError::StaleInvocation)
    ));
    let replacement = {
        let mut storage = entry.owner.storage.lock().unwrap();
        std::mem::replace(&mut storage.context, original_context)
    };
    drop(replacement);
    let original_stack = {
        let mut storage = entry.owner.storage.lock().unwrap();
        std::mem::replace(
            &mut storage.stack,
            OwnedEntryStack::allocate(65_536).unwrap(),
        )
    };
    assert!(matches!(
        entry.invoke(),
        Err(EntryStackError::StaleInvocation)
    ));
    let replacement = {
        let mut storage = entry.owner.storage.lock().unwrap();
        std::mem::replace(&mut storage.stack, original_stack)
    };
    drop(replacement);
    let original_signature = entry.manifest.symbols[0].signature.clone();
    entry.manifest.symbols[0]
        .signature
        .returns
        .push(crate::jit_contract::AbiValue::new(
            crate::jit_contract::AbiValueKind::I64,
        ));
    assert!(
        entry
            .invoke()
            .unwrap_err()
            .to_string()
            .contains("signature differs")
    );
    entry.manifest.symbols[0].signature = original_signature;
    {
        let mut storage = entry.owner.storage.lock().unwrap();
        let Storage {
            context,
            output,
            stack,
        } = &mut *storage;
        let image = output.extent().unwrap();
        let target = output.words().as_ptr().cast::<u8>();
        let invocation = stack.borrow_invocation(&entry.owner.requirement).unwrap();
        // This is an actual owned output allocation, presented as an invalid
        // purported image. The adapter must reject overlap before any call.
        assert!(matches!(
            unsafe { invocation.invoke_context_output(target, context, output, image) },
            Err(EntryStackError::AliasedStorage)
        ));
    }
    let input = crate::jit_cert::digest_hex(&entry.owner.input);
    let code =
        crate::jit_cert::digest_hex(&Sha256::digest(entry.owner.replay.final_bytes()).into());
    assert!(entry.owner.matches_certificate(
        &entry.owner.function,
        &input,
        &code,
        entry.owner.binding_digest
    ));
    let mut changed = entry.owner.replay.final_bytes().to_vec();
    changed[0] ^= 1;
    assert!(!entry.owner.matches_certificate(
        &entry.owner.function,
        &input,
        &crate::jit_cert::digest_hex(&Sha256::digest(&changed).into()),
        entry.owner.binding_digest
    ));
    assert_eq!(entry.output_words().unwrap(), [0; 5]);
    drop(entry);
    assert!(!certificate.is_verified());
    assert!(!certificate.has_checked_semantics());
    assert!(!certificate.replay_check());
    assert_eq!(certificate.coverage_percent(), 0.0);
    let json: serde_json::Value = serde_json::from_str(&certificate.to_json()).unwrap();
    assert_eq!(json["verified"], false);
    assert_eq!(json["coverage_percent"], 0.0);
    println!(
        "CORE_VOID_CONTEXT_OUTPUT_STORAGE_ALIAS_STALE_FINAL_BINDING_AND_LIFETIME_CONTROLS=PASS"
    );
}
