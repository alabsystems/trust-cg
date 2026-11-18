// Copyright 2026 Andrew Yates | Apache-2.0
//! Exact external no-import source/Core/machine/installed two-pointer ABI.
#![cfg(all(
    feature = "source-defined-call",
    target_arch = "aarch64",
    target_os = "macos"
))]
use cg::jit::context_output::{OwnedEntryContext, OwnedEntryOutput};
use cg::jit::entry_stack::OwnedEntryStack;
use trust_cg_codegen as cg;
#[path = "common/context_output_fixture.rs"]
mod fixture;

#[test]
fn genuine_void_context_five_word_output_uses_source_replay_and_opaque_owned_install() {
    let module = fixture::certified(true, false);
    let generation = cg::compile_service::CompileGeneration::new(1);
    let manifest = fixture::manifest(&module, generation);
    let expected = [42, u64::MAX, (-7i64) as u64, 0x1234_5678_9abc_def0, 23];
    let context = OwnedEntryContext::from_words(expected.to_vec()).unwrap();
    let output = OwnedEntryOutput::allocate_words(5).unwrap();
    let stack = OwnedEntryStack::allocate(65_536).unwrap();
    let (mut entry, manifest) = fixture::plan(module)
        .compile_install_owned_context_output(
            context,
            output,
            stack,
            manifest,
            generation,
        )
        .unwrap_or_else(|error| panic!("actual whole source, original request, final words, real memory and installed replay: {error}"));
    assert_eq!(entry.output_words().unwrap(), [0; 5]);
    assert!(
        entry.invoke_observed_word().is_err(),
        "the separate one-word observer must refuse this five-word entry before dispatch"
    );
    assert_eq!(entry.output_words().unwrap(), [0; 5]);
    assert!(manifest.symbols[0].signature.returns.is_empty());
    entry.invoke().unwrap();
    assert_eq!(entry.output_words().unwrap(), expected);
    assert_eq!(entry.context_words().unwrap(), expected);
    entry.invoke().unwrap();
    assert_eq!(entry.output_words().unwrap(), expected);
    println!(
        "CORE_SOURCE_VOID_CONTEXT_OUTPUT_NATIVE=PASS words={expected:?} void=true imports=0 providers=0 fixups=0"
    );
}

#[test]
fn original_source_certificate_roles_footprint_and_signature_refuse_before_native_dispatch() {
    fixture::source_mutations_refuse();
    let module = fixture::certified(false, false);
    let unbound = fixture::plan(module.clone())
        .compile_for_installation()
        .unwrap_err();
    assert!(format!("{unbound:?}").contains("owned context/output consumer"));
    for (input, output) in [(4, 5), (5, 4)] {
        let generation = cg::compile_service::CompileGeneration::new(2);
        let manifest = fixture::manifest(&module, generation);
        let error = fixture::plan(module.clone())
            .compile_install_owned_context_output(
                OwnedEntryContext::from_words(vec![42; input]).unwrap(),
                OwnedEntryOutput::allocate_words(output).unwrap(),
                OwnedEntryStack::allocate(0).unwrap(),
                manifest,
                generation,
            )
            .unwrap_err();
        assert!(
            error.to_string().contains("does not cover"),
            "actual refusal: {error}"
        );
    }
    // Owning non-null allocations does not rewrite the module's raw-pointer
    // ABI. The original publisher derives nullable pointers in this source.
    let generation = cg::compile_service::CompileGeneration::new(4);
    let mut wrong_nullable = fixture::manifest(&module, generation);
    assert!(
        wrong_nullable.symbols[0]
            .signature
            .params
            .iter()
            .all(|p| p.nullable)
    );
    for parameter in &mut wrong_nullable.symbols[0].signature.params {
        parameter.nullable = false;
    }
    let error = fixture::plan(module.clone())
        .compile_install_owned_context_output(
            OwnedEntryContext::from_words(vec![42; 5]).unwrap(),
            OwnedEntryOutput::allocate_words(5).unwrap(),
            OwnedEntryStack::allocate(0).unwrap(),
            wrong_nullable,
            generation,
        )
        .unwrap_err();
    assert!(
        error.to_string().contains("actual Core signature"),
        "{error}"
    );
    let mut missing = module.clone();
    missing.proof_certificates.clear();
    assert!(
        cg::admit_identity_core_module_for_host_jit(
            missing,
            &cg::CoreHostJitTarget::detect().unwrap(),
            cg::CoreDeclaredImportManifest::empty()
        )
        .is_err()
    );
    let mut changed = module.clone();
    changed.func_types[0].returns = vec![trust_ir::Ty::U64];
    assert!(
        cg::admit_identity_core_module_for_host_jit(
            changed,
            &cg::CoreHostJitTarget::detect().unwrap(),
            cg::CoreDeclaredImportManifest::empty()
        )
        .is_err()
    );
    let inbounds = fixture::certified(false, true);
    let generation = cg::compile_service::CompileGeneration::new(3);
    let manifest = fixture::manifest(&inbounds, generation);
    let error = fixture::plan(inbounds)
        .compile_install_owned_context_output(
            OwnedEntryContext::from_words(vec![42; 5]).unwrap(),
            OwnedEntryOutput::allocate_words(5).unwrap(),
            OwnedEntryStack::allocate(0).unwrap(),
            manifest,
            generation,
        )
        .unwrap_err();
    assert!(
        error.to_string().contains("inbounds"),
        "actual refusal: {error}"
    );
    println!("CORE_SOURCE_VOID_CONTEXT_OUTPUT_BEFORE_NATIVE_REFUSALS=PASS");
}
