// Copyright 2026 Andrew Yates | Apache-2.0
//! Actual flat four-pointer/U64 contract; no nested sink, model or K3 grade.
#![cfg(all(
    feature = "source-defined-call",
    target_arch = "aarch64",
    target_os = "macos"
))]
use cg::jit::context_output::{OwnedEntryContext, OwnedEntryOutput};
use cg::jit::entry_stack::OwnedEntryStack;
use trust_cg_codegen as cg;
#[path = "common/four_pointer_status_fixture.rs"]
mod fixture;
fn install() -> cg::compiler::CoreOwnedFourPointerStatusEntry {
    let module = fixture::certified();
    let manifest = fixture::manifest(&module);
    let inputs = [
        OwnedEntryContext::from_words(vec![0x8877_6655_4433_2211]).unwrap(),
        OwnedEntryContext::from_words(vec![0x0102_0304_0506_0780]).unwrap(),
    ];
    let mut outputs = [
        OwnedEntryOutput::allocate_words(1).unwrap(),
        OwnedEntryOutput::allocate_words(1).unwrap(),
    ];
    outputs[0].words_mut()[0] = 0xcccc_dddd_eeee_ffff;
    outputs[1].words_mut()[0] = 0xaaaa_bbbb_0000_1234;
    fixture::plan(module)
        .compile_install_owned_four_pointer_status(
            inputs,
            outputs,
            OwnedEntryStack::allocate(65_536).unwrap(),
            manifest,
            cg::compile_service::CompileGeneration::new(1),
        )
        .unwrap()
        .0
}
#[test]
fn actual_non_tla_four_pointer_call_observes_all_arguments_full_return_and_current_epoch() {
    let mut entry = install();
    let first = entry.invoke_observed().expect(
        "actual full compiler replay, four-pointer dispatch and independent physical post replay",
    );
    let claim = first.historical_words_and_status();
    assert_eq!(
        claim.before,
        [
            0x8877_6655_4433_2211,
            0x0102_0304_0506_0780,
            0xcccc_dddd_eeee_ffff,
            0xaaaa_bbbb_0000_1234
        ]
    );
    assert_eq!(
        claim.after,
        [
            claim.before[0],
            claim.before[1],
            claim.before[0],
            claim.before[1]
        ]
    );
    assert_eq!(claim.status, claim.before[0]);
    assert_eq!(first.historical_extents().map(|(a, b)| b - a), [8; 4]);
    assert_eq!(first.proof_replay_diagnostics().len(), 4);
    assert_eq!(first.source_function(), entry.source_function());
    first.check_current(&entry).unwrap();
    println!(
        "ACTUAL_FOUR_POINTER_STATUS={first:?} extents={:?} source={} post={} post_replay_seconds={:.9}",
        first.historical_extents(),
        first.core_module().stable_digest(),
        first.post_memory_statement(),
        first.proof_replay_time().as_secs_f64()
    );
    println!(
        "FOUR_POINTER_FORMAL_PROVENANCE={:?}",
        first.proof_replay_diagnostics()
    );
    let second = entry.invoke_observed().unwrap();
    assert!(first.check_current(&entry).is_err());
    assert_eq!(first.historical_words_and_status(), claim);
    second.check_current(&entry).unwrap();
    entry.replace_input_word(0, claim.before[0]).unwrap();
    assert!(
        second.check_current(&entry).is_err(),
        "equal replacement must invalidate current bytes"
    );
    entry.replace_input_word(0, 0xfedc_ba98_7654_3210).unwrap();
    let third = entry.invoke_observed().unwrap();
    third.check_current(&entry).unwrap();
    assert_eq!(
        third.historical_words_and_status().status,
        0xfedc_ba98_7654_3210
    );
    assert_eq!(
        third.historical_words_and_status().after[2],
        0xfedc_ba98_7654_3210
    );
    println!(
        "FOUR_POINTER_ALL_POST_REPLAY_SECONDS first={:.9} second={:.9} third={:.9}",
        first.proof_replay_time().as_secs_f64(),
        second.proof_replay_time().as_secs_f64(),
        third.proof_replay_time().as_secs_f64()
    );
    println!(
        "FOUR_POINTER_EPOCH_CONTROLS=PASS later_call=true equal_update=true changed_status=true nested_sink=false model_grade=false"
    );
}
#[test]
fn false_independent_source_and_wrong_geometry_or_manifest_are_refused() {
    let module = fixture::module();
    for change in [
        fixture::Change::ReadOther,
        fixture::Change::SwapOutputs,
        fixture::Change::WrongStatus,
        fixture::Change::EraseFault,
    ] {
        let error = fixture::mint(&module, &fixture::source(change)).unwrap_err();
        assert!(error.contains("TypeMismatch"), "{error}");
    }
    let module = fixture::certified();
    let error = fixture::plan(module.clone())
        .compile_for_installation()
        .unwrap_err();
    assert!(
        error
            .to_string()
            .contains("owned four-pointer/status consumer")
    );
    let mut manifest = fixture::manifest(&module);
    manifest.symbols[0].signature = cg::jit_contract::SymbolSignature::extern_c(
        vec![cg::jit_contract::AbiValue::new(cg::jit_contract::AbiValueKind::Ptr); 2],
        vec![],
    );
    let err = fixture::plan(module)
        .compile_install_owned_four_pointer_status(
            [
                OwnedEntryContext::from_words(vec![1]).unwrap(),
                OwnedEntryContext::from_words(vec![2]).unwrap(),
            ],
            [
                OwnedEntryOutput::allocate_words(1).unwrap(),
                OwnedEntryOutput::allocate_words(1).unwrap(),
            ],
            OwnedEntryStack::allocate(0).unwrap(),
            manifest,
            cg::compile_service::CompileGeneration::new(1),
        )
        .unwrap_err();
    assert!(err.to_string().contains("manifest"));
    let module = fixture::certified();
    let manifest = fixture::manifest(&module);
    let err = fixture::plan(module)
        .compile_install_owned_four_pointer_status(
            [
                OwnedEntryContext::from_words(vec![1, 2]).unwrap(),
                OwnedEntryContext::from_words(vec![2]).unwrap(),
            ],
            [
                OwnedEntryOutput::allocate_words(1).unwrap(),
                OwnedEntryOutput::allocate_words(1).unwrap(),
            ],
            OwnedEntryStack::allocate(0).unwrap(),
            manifest,
            cg::compile_service::CompileGeneration::new(1),
        )
        .unwrap_err();
    assert!(err.to_string().contains("one initialized word"));
}
