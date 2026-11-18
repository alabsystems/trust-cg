// Copyright 2026 Andrew Yates | Apache-2.0
use super::*;
use crate as cg;
#[path = "word_context_output_fixture.rs"]
mod fixture;

fn entry() -> CoreOwnedContextOutputEntry {
    let module = fixture::certified(None);
    let manifest = fixture::manifest(&module);
    fixture::plan(module)
        .compile_install_owned_context_output(
            OwnedEntryContext::from_words(vec![0x8055_1234_6789_abcd]).unwrap(),
            OwnedEntryOutput::allocate_words(1).unwrap(),
            OwnedEntryStack::allocate(65_536).unwrap(),
            manifest,
            CompileGeneration::new(1),
        )
        .unwrap()
        .0
}

#[test]
fn word_observation_false_value_address_foreign_source_and_lifetime_refuse() {
    fixture::false_source_refuses();
    let mut first = entry();
    let observed = first.invoke_observed_word().unwrap();
    observed.check_current(&first).unwrap();
    let claim = observed.historical_words();
    let mut false_value = claim;
    false_value.output_after ^= 1;
    let error = first
        .owner
        .replay
        .replay_word_memory_claim(false_value)
        .err()
        .expect("an independently false observed byte cannot mint a proof");
    println!("FALSE_WORD_POST_VALUE_REFUSED={error}");
    let mut false_address = claim;
    false_address.output_address = [0x1000, 0x2000, 0x3000]
        .into_iter()
        .find(|address| *address != claim.context_address && *address != claim.output_address)
        .unwrap();
    let proof = first.owner.replay.replay_word_memory_claim(false_address).expect("the same generic source can prove a different LOGICAL address, without live permission");
    assert!(
        CoreWordMemoryObservation::new(
            Arc::clone(&first.installed),
            Arc::clone(&first.owner),
            observed.generation,
            false_address,
            proof,
            std::time::Duration::ZERO
        )
        .is_err(),
        "a genuine logical proof cannot replace the actual physical address"
    );
    let second = entry();
    let storage = second.owner.storage.lock().unwrap();
    let foreign_claim = VoidWordMemoryClaim {
        context_address: second.owner.context_extent.0 as u64,
        output_address: second.owner.output_extent.0 as u64,
        context_before: storage.context.value()[0],
        output_before: storage.output.words()[0],
        context_after: storage.context.value()[0],
        output_after: storage.context.value()[0],
    };
    drop(storage);
    let foreign = first
        .owner
        .replay
        .replay_word_memory_claim(foreign_claim)
        .unwrap();
    assert_eq!(
        first.owner.replay.statement_digest(),
        second.owner.replay.statement_digest(),
        "content-equal compilations still have distinct original owners"
    );
    assert!(!second.owner.replay.owns_word_memory_claim(&foreign));
    assert!(
        CoreWordMemoryObservation::new(
            Arc::clone(&second.installed),
            Arc::clone(&second.owner),
            0,
            foreign_claim,
            foreign,
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
        "the historical observation retains the exact live image and proof owner"
    );
    assert_eq!(observed.historical_words(), claim);
    drop(observed);
    assert!(
        !certificate.is_verified(),
        "releasing the last actual owner expires the image certificate"
    );
    println!("WORD_OBSERVATION_FALSE_ADDRESS_FOREIGN_SOURCE_AND_REAL_LIFETIME_CONTROLS=PASS");
}
