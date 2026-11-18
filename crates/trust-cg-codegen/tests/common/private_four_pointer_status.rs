// Copyright 2026 Andrew Yates | Apache-2.0
//! Actual sealed owners and replay; no test-created receipt or permission.
use super::*;
use crate as cg;
#[path = "four_pointer_status_fixture.rs"]
mod fixture;
fn entry() -> CoreOwnedFourPointerStatusEntry {
    let module = fixture::certified();
    let manifest = fixture::manifest(&module);
    fixture::plan(module)
        .compile_install_owned_four_pointer_status(
            [
                OwnedEntryContext::from_words(vec![0x8055_1234_6789_abcd]).unwrap(),
                OwnedEntryContext::from_words(vec![0x1122_3344_5566_7788]).unwrap(),
            ],
            [
                OwnedEntryOutput::allocate_words(1).unwrap(),
                OwnedEntryOutput::allocate_words(1).unwrap(),
            ],
            OwnedEntryStack::allocate(65_536).unwrap(),
            manifest,
            CompileGeneration::new(1),
        )
        .unwrap()
        .0
}
#[test]
fn four_pointer_observation_false_status_bytes_address_foreign_source_and_lifetime_refuse() {
    // These definitions are not derived from the target, including wrong status
    // and erased-fault controls that must lose in the real source kernel.
    let m = fixture::module();
    for change in [
        fixture::Change::ReadOther,
        fixture::Change::SwapOutputs,
        fixture::Change::WrongStatus,
        fixture::Change::EraseFault,
    ] {
        let error = fixture::mint(&m, &fixture::source(change)).unwrap_err();
        assert!(error.contains("TypeMismatch"), "{error}");
    }
    let mut first = entry();
    let observed = first.invoke_observed().unwrap();
    let claim = observed.historical_words_and_status();
    observed.check_current(&first).unwrap();
    for status in [true, false] {
        let mut bad = claim;
        if status {
            bad.status ^= 1u64 << 63;
        } else {
            bad.after[3] ^= 1;
        }
        let proof_started = std::time::Instant::now();
        let error = first
            .owner
            .replay
            .replay_word_memory_claim(bad)
            .err()
            .expect("false actual status/post byte cannot mint original-Core proof");
        assert!(
            error.attempted(),
            "a boundary/resource failure is not a semantic negative: {error}"
        );
        assert_eq!(
            error.part(),
            Some(if status {
                "Original Core actual U64 return"
            } else {
                "Original Core all 32 physical post bytes"
            })
        );
        let Some(trust_cg_verify::verify::VerificationResult::Invalid { counterexample }) =
            error.verdict()
        else {
            panic!(
                "actual Invalid required; Unknown/timeout/unavailable/non-attempted cannot count: {error}"
            )
        };
        // These physical propositions instantiate every ABI scalar. The
        // existing AY parser projects only declared scalar inputs, so [] is
        // expected here and never a populated-model claim. Require a separate
        // real Clean proof of the original conclusion's denial, retaining all
        // original premises and the captured enforcing request.
        assert_eq!(error.scalar_input_count(), Some(0));
        assert_eq!(counterexample.trim(), "[]");
        assert!(error.original_query().is_some());
        let denial = error
            .denial_replay()
            .expect("actual Invalid must retain a separate denial attempt");
        assert!(
            denial.attempted(),
            "denial resource refusal cannot count: {denial:?}"
        );
        assert!(
            matches!(
                denial.verdict(),
                Some(trust_cg_verify::verify::VerificationResult::Valid)
            ),
            "actual independent denial proof required: {denial:?}"
        );
        assert!(denial.query().is_some());
        assert_ne!(denial.query(), error.original_query());
        println!(
            "FALSE_FOUR_POINTER_SEPARATE_DENIAL status_control={status} projected_scalar_inputs=0 populated_model=false denial_replay_seconds={:.9} attribution={} query={}",
            denial.replay_time().as_secs_f64(),
            denial.why(),
            denial.query().unwrap()
        );
        println!(
            "FALSE_FOUR_POINTER_STATUS_OR_BYTE_REFUSED status_control={status} proof_seconds={:.9} error={error}",
            proof_started.elapsed().as_secs_f64()
        );
    }
    let mut logical = claim;
    logical.addresses[3] = [0x1000, 0x2000, 0x3000, 0x4000, 0x5000]
        .into_iter()
        .find(|a| !claim.addresses.contains(a))
        .unwrap();
    let proof = first
        .owner
        .replay
        .replay_word_memory_claim(logical)
        .expect("relocated logical bytes may be valid but confer no physical address");
    assert!(
        CoreFourWordStatusObservation::new(
            Arc::clone(&first.installed),
            Arc::clone(&first.owner),
            observed.generation,
            logical,
            proof,
            std::time::Duration::ZERO
        )
        .is_err()
    );
    let second = entry();
    let storage = second.owner.storage.lock().unwrap();
    let before = storage.words();
    let foreign_claim = FourWordStatusClaim {
        addresses: second.owner.extents.map(|(a, _)| a as u64),
        before,
        after: [before[0], before[1], before[0], before[1]],
        status: before[0],
    };
    drop(storage);
    let proof = first
        .owner
        .replay
        .replay_word_memory_claim(foreign_claim)
        .unwrap();
    assert_eq!(
        first.owner.replay.statement_digest(),
        second.owner.replay.statement_digest()
    );
    assert!(!second.owner.replay.owns_word_memory_claim(&proof));
    assert!(
        CoreFourWordStatusObservation::new(
            Arc::clone(&second.installed),
            Arc::clone(&second.owner),
            0,
            foreign_claim,
            proof,
            std::time::Duration::ZERO
        )
        .is_err()
    );
    assert!(observed.check_current(&second).is_err());
    let certificate = first
        .installed
        .buffer
        .certificate(&first.owner.function)
        .unwrap()
        .clone();
    drop(first);
    assert!(
        certificate.is_verified(),
        "historical observation retains exact image/source allocations"
    );
    assert_eq!(observed.historical_words_and_status(), claim);
    drop(observed);
    assert!(
        !certificate.is_verified(),
        "last actual source/image owner expired"
    );
    println!("FOUR_POINTER_FALSE_STATUS_ADDRESS_BYTES_FOREIGN_SOURCE_AND_LIFETIME_CONTROLS=PASS");
}
#[test]
fn four_pointer_storage_roles_manifest_aliases_and_final_binding_refuse_before_dispatch() {
    let mut entry = entry();
    let certificate = entry
        .installed
        .buffer
        .certificate(&entry.owner.function)
        .unwrap()
        .clone();
    assert!(
        certificate.is_verified()
            && certificate.has_checked_semantics()
            && certificate.replay_check()
    );
    for index in 0..2 {
        let original = {
            let mut storage = entry.owner.storage.lock().unwrap();
            std::mem::replace(
                &mut storage.inputs[index],
                OwnedEntryContext::from_words(vec![42]).unwrap(),
            )
        };
        assert!(matches!(
            entry.invoke_observed(),
            Err(EntryStackError::StaleInvocation)
        ));
        let replacement = {
            let mut storage = entry.owner.storage.lock().unwrap();
            std::mem::replace(&mut storage.inputs[index], original)
        };
        drop(replacement);
    }
    for index in 0..2 {
        let original = {
            let mut storage = entry.owner.storage.lock().unwrap();
            std::mem::replace(
                &mut storage.outputs[index],
                OwnedEntryOutput::allocate_words(1).unwrap(),
            )
        };
        assert!(matches!(
            entry.invoke_observed(),
            Err(EntryStackError::StaleInvocation)
        ));
        let replacement = {
            let mut storage = entry.owner.storage.lock().unwrap();
            std::mem::replace(&mut storage.outputs[index], original)
        };
        drop(replacement);
    }
    let original = {
        let mut storage = entry.owner.storage.lock().unwrap();
        std::mem::replace(
            &mut storage.stack,
            OwnedEntryStack::allocate(65_536).unwrap(),
        )
    };
    assert!(matches!(
        entry.invoke_observed(),
        Err(EntryStackError::StaleInvocation)
    ));
    let replacement = {
        let mut storage = entry.owner.storage.lock().unwrap();
        std::mem::replace(&mut storage.stack, original)
    };
    drop(replacement);
    let signature = entry.manifest.symbols[0].signature.clone();
    entry.manifest.symbols[0].signature.returns.clear();
    assert!(
        entry
            .invoke_observed()
            .unwrap_err()
            .to_string()
            .contains("signature differs")
    );
    entry.manifest.symbols[0].signature = signature;
    {
        let mut storage = entry.owner.storage.lock().unwrap();
        let Storage {
            inputs,
            outputs,
            stack,
        } = &mut *storage;
        let image = outputs[1].extent().unwrap();
        let target = outputs[1].words().as_ptr().cast::<u8>();
        let invocation = stack.borrow_invocation(&entry.owner.requirement).unwrap();
        assert!(matches!(
            unsafe { invocation.invoke_four_pointer_status(target, inputs, outputs, image) },
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
        entry.owner.binding
    ));
    let mut changed = entry.owner.replay.final_bytes().to_vec();
    changed[0] ^= 1;
    assert!(!entry.owner.matches_certificate(
        &entry.owner.function,
        &input,
        &crate::jit_cert::digest_hex(&Sha256::digest(&changed).into()),
        entry.owner.binding
    ));
    assert_eq!(
        entry.words().unwrap(),
        [0x8055_1234_6789_abcd, 0x1122_3344_5566_7788, 0, 0]
    );
    drop(entry);
    assert!(
        !certificate.is_verified()
            && !certificate.has_checked_semantics()
            && !certificate.replay_check()
    );
    println!("FOUR_POINTER_STORAGE_ALIAS_RETURN_MANIFEST_AND_EXACT_BYTE_CONTROLS=PASS");
}
