// Copyright 2026 Andrew Yates | Apache-2.0
//! Actual bounded physical observations, not a model or wider K3 entry.
#![cfg(all(
    feature = "source-defined-call",
    target_arch = "aarch64",
    target_os = "macos"
))]
use cg::jit::context_output::{OwnedEntryContext, OwnedEntryOutput};
use cg::jit::entry_stack::OwnedEntryStack;
use trust_cg_codegen as cg;
#[path = "common/word_context_output_fixture.rs"]
mod fixture;

fn entry(
    literal: Option<u64>,
    word: u64,
) -> (
    cg::compiler::CoreOwnedContextOutputEntry,
    trust_ir::proof::ProofDigest,
) {
    let module = fixture::certified(literal);
    let manifest = fixture::manifest(&module);
    let digest = module.stable_digest();
    let mut output = OwnedEntryOutput::allocate_words(1).unwrap();
    output.words_mut()[0] = 0xfedc_ba98_7654_3210;
    (
        fixture::plan(module)
            .compile_install_owned_context_output(
                OwnedEntryContext::from_words(vec![word]).unwrap(),
                output,
                OwnedEntryStack::allocate(65_536).unwrap(),
                manifest,
                cg::compile_service::CompileGeneration::new(1),
            )
            .unwrap()
            .0,
        digest,
    )
}

#[test]
fn actual_copy_word_observation_retains_core_image_and_rejects_later_call_and_mutation() {
    let first = 0x0102_0304_0506_0780;
    let (mut entry, expected_core) = entry(None, first);
    let observation = entry
        .invoke_observed_word()
        .expect("actual call and every concrete original-Core post byte must replay");
    let words = observation.historical_words();
    println!(
        "ACTUAL_PHYSICAL_WORD_OBSERVATION={observation:?} extents={:?}",
        observation.historical_extents()
    );
    assert_eq!(
        (
            words.context_before,
            words.output_before,
            words.context_after,
            words.output_after
        ),
        (first, 0xfedc_ba98_7654_3210, first, first)
    );
    assert_eq!(observation.historical_extents().map(|(a, b)| b - a), [8, 8]);
    assert_eq!(observation.proof_replay_diagnostics().len(), 18);
    observation.check_current(&entry).unwrap();
    let source = observation.core_module().stable_digest();
    assert_eq!(source, expected_core);
    assert_eq!(observation.source_function(), entry.source_function());
    entry.invoke().unwrap();
    assert!(observation.check_current(&entry).is_err());
    assert_eq!(observation.historical_words(), words);
    let next = entry.invoke_observed_word().unwrap();
    next.check_current(&entry).unwrap();
    assert_eq!(entry.replace_context_word(first).unwrap(), first);
    assert!(
        next.check_current(&entry).is_err(),
        "equal host replacement still advances the physical epoch"
    );
    let value = first ^ 0x80;
    entry.replace_context_word(value).unwrap();
    let changed = entry.invoke_observed_word().unwrap();
    changed.check_current(&entry).unwrap();
    assert_eq!(
        (
            changed.historical_words().context_before,
            changed.historical_words().output_before,
            changed.historical_words().output_after
        ),
        (value, first, value)
    );
    println!(
        "OWNED_WORD_COPY_OBSERVATION source={source} post_memory={} first_post_replay_seconds={:.9} next_post_replay_seconds={:.9} changed_post_replay_seconds={:.9} historical_call_and_mutation_refused=true wider_abi=false",
        changed.post_memory_statement(),
        observation.proof_replay_time().as_secs_f64(),
        next.proof_replay_time().as_secs_f64(),
        changed.proof_replay_time().as_secs_f64()
    );
    println!(
        "WORD_FORMAL_REPLAY_PROVENANCE={:?}",
        changed.proof_replay_diagnostics()
    );
}

#[test]
fn non_tla_literal_store_has_an_independently_certified_physical_post_memory_relation() {
    fixture::false_source_refuses();
    let (mut entry, expected_core) = entry(Some(42), 0x8877_6655_4433_2211);
    let observation = entry.invoke_observed_word().unwrap();
    observation.check_current(&entry).unwrap();
    let words = observation.historical_words();
    println!(
        "ACTUAL_NON_TLA_PHYSICAL_WORD_OBSERVATION={observation:?} extents={:?}",
        observation.historical_extents()
    );
    assert_eq!(
        (words.context_after, words.output_after),
        (0x8877_6655_4433_2211, 42)
    );
    assert_eq!(observation.core_module().stable_digest(), expected_core);
    println!(
        "NON_TLA_WORD_STORE_OBSERVATION post_memory={} post_replay_seconds={:.9} false_independent_source=rejected",
        observation.post_memory_statement(),
        observation.proof_replay_time().as_secs_f64()
    );
}
