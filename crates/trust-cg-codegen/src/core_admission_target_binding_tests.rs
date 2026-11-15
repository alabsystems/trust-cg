// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Target-metadata correspondence controls, not native execution or proofs.

use super::*;
use trust_ir::{Block, BlockId, Function, InstrNode, ValueId};

fn source_module() -> Module {
    let mut module = Module::new("ordinary_original_target_consumer");
    let signature = module
        .add_func_type(FuncTy {
            params: vec![Ty::Ptr, Ty::U32],
            returns: vec![Ty::U64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = Function::new(FuncId::new(0), "original_entry", signature, BlockId::new(0));
    let mut block = Block::new(BlockId::new(0));
    block.params = vec![(ValueId::new(0), Ty::Ptr), (ValueId::new(1), Ty::U32)];
    block.body = vec![
        InstrNode::new(Inst::Const {
            ty: Ty::U64,
            value: Constant::Int(0),
        })
        .with_result(ValueId::new(2)),
        InstrNode::new(Inst::Return {
            values: vec![ValueId::new(2)],
        }),
    ];
    function.blocks.push(block);
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
    module
}

fn bytes(module: &Module) -> Vec<u8> {
    serialize_core_identity(module, "target-binding regression original module").unwrap()
}

#[test]
fn binding_missing_target_changes_only_exact_metadata_without_cloning_bodies() {
    let target = tests::core_host_target();
    let mut module = source_module();
    assert_eq!(
        target.check_module(&module),
        Err(CoreTargetContractError::ModuleTargetMissing)
    );
    let name = module.name.as_ptr();
    let functions = module.functions.as_ptr();
    let signatures = module.func_types.as_ptr();
    let signature_params = module.func_types[0].params.as_ptr();
    let blocks = module.functions[0].blocks.as_ptr();
    let params = module.functions[0].blocks[0].params.as_ptr();
    let instructions = module.functions[0].blocks[0].body.as_ptr();
    let results = module.functions[0].blocks[0].body[0].results.as_ptr();
    let owner = target.clone();
    let mut expected = module.clone(); // Independent test expectation only.
    expected.target_info = Some(target.trust_ir_target_info().clone());

    target.bind_module_target(&mut module).unwrap();
    assert_eq!(bytes(&module), bytes(&expected));
    assert_eq!(module.name.as_ptr(), name);
    assert_eq!(module.functions.as_ptr(), functions);
    assert_eq!(module.func_types.as_ptr(), signatures);
    assert_eq!(module.func_types[0].params.as_ptr(), signature_params);
    assert_eq!(module.functions[0].blocks.as_ptr(), blocks);
    assert_eq!(module.functions[0].blocks[0].params.as_ptr(), params);
    assert_eq!(module.functions[0].blocks[0].body.as_ptr(), instructions);
    assert_eq!(
        module.functions[0].blocks[0].body[0].results.as_ptr(),
        results
    );
    assert_eq!(
        target, owner,
        "binding does not re-detect optional ISA or alter the owner"
    );
    assert!(target.check_module(&module).is_ok());
}

#[test]
fn binding_matching_target_is_idempotent_without_replacing_target_strings() {
    let target = tests::core_host_target();
    let mut module = source_module();
    target.bind_module_target(&mut module).unwrap();
    let original = bytes(&module);
    let triple = module.target_info.as_ref().unwrap().triple.as_ptr();
    let abi = module
        .target_info
        .as_ref()
        .unwrap()
        .abi
        .as_ref()
        .unwrap()
        .as_ptr();
    for _ in 0..2 {
        target.bind_module_target(&mut module).unwrap();
        assert_eq!(bytes(&module), original);
        assert_eq!(module.target_info.as_ref().unwrap().triple.as_ptr(), triple);
        assert_eq!(
            module
                .target_info
                .as_ref()
                .unwrap()
                .abi
                .as_ref()
                .unwrap()
                .as_ptr(),
            abi
        );
    }
}

#[test]
fn every_conflicting_target_refuses_specifically_and_preserves_the_original_module() {
    let target = tests::core_host_target();
    let expected = target.trust_ir_target_info();
    let mut cases = Vec::new();
    let mut changed = expected.clone();
    changed.triple = "foreign-unknown-target".into();
    cases.push((
        changed,
        CoreTargetContractError::TrustIrTripleMismatch {
            expected: expected.triple.clone(),
            actual: "foreign-unknown-target".into(),
        },
    ));
    let mut changed = expected.clone();
    changed.pointer_size = 4;
    cases.push((
        changed,
        CoreTargetContractError::TrustIrPointerWidthMismatch {
            expected: 8,
            actual: 4,
        },
    ));
    let mut changed = expected.clone();
    changed.endianness = trust_ir::Endianness::Big;
    cases.push((
        changed,
        CoreTargetContractError::UnsupportedTrustIrEndianness {
            actual: trust_ir::Endianness::Big,
        },
    ));
    let mut changed = expected.clone();
    changed.abi = None;
    cases.push((changed, CoreTargetContractError::TrustIrAbiMissing));
    let mut changed = expected.clone();
    changed.abi = Some("different_abi".into());
    cases.push((
        changed,
        CoreTargetContractError::TrustIrAbiMismatch {
            expected: expected.abi.clone().unwrap(),
            actual: "different_abi".into(),
        },
    ));
    for abi in [
        String::new(),
        " aapcs64".into(),
        "aapcs64\n".into(),
        "a".repeat(MAX_CONTRACT_TEXT_BYTES + 1),
    ] {
        let mut changed = expected.clone();
        changed.abi = Some(abi);
        cases.push((
            changed,
            CoreTargetContractError::InvalidContractText {
                field: "TrustIR ABI",
            },
        ));
    }
    for policy in [
        StructPassingPolicy::AlwaysMemory,
        StructPassingPolicy::Unclassified,
    ] {
        let mut changed = expected.clone();
        changed.struct_passing = policy;
        cases.push((
            changed,
            CoreTargetContractError::TrustIrStructPassingUnsupported { actual: policy },
        ));
    }
    assert_eq!(cases.len(), 11);
    for (metadata, refusal) in cases {
        let mut module = source_module();
        module.target_info = Some(metadata);
        let original = bytes(&module);
        let target_strings = module.target_info.as_ref().unwrap().triple.as_ptr();
        let functions = module.functions.as_ptr();
        assert_eq!(target.check_module(&module), Err(refusal.clone()));
        assert_eq!(target.bind_module_target(&mut module), Err(refusal));
        assert_eq!(
            bytes(&module),
            original,
            "refusal may not silently retarget anything"
        );
        assert_eq!(
            module.target_info.as_ref().unwrap().triple.as_ptr(),
            target_strings
        );
        assert_eq!(module.functions.as_ptr(), functions);
    }
}

#[test]
fn all_supported_explicit_targets_bind_their_own_metadata_not_a_host_fallback() {
    for (architecture, vendor, os, environment) in [
        (
            Target::Aarch64,
            TargetVendor::Apple,
            TargetOperatingSystem::Darwin,
            TargetEnvironment::Unknown,
        ),
        (
            Target::Aarch64,
            TargetVendor::Unknown,
            TargetOperatingSystem::Linux,
            TargetEnvironment::Gnu,
        ),
        (
            Target::X86_64,
            TargetVendor::Apple,
            TargetOperatingSystem::Darwin,
            TargetEnvironment::Unknown,
        ),
        (
            Target::X86_64,
            TargetVendor::Unknown,
            TargetOperatingSystem::Linux,
            TargetEnvironment::Gnu,
        ),
        (
            Target::X86_64,
            TargetVendor::Pc,
            TargetOperatingSystem::Windows,
            TargetEnvironment::Msvc,
        ),
    ] {
        let profile = match architecture {
            Target::Aarch64 => CoreHostJitMachineProfile::AArch64(AArch64IsaProfile::BASELINE),
            Target::X86_64 => {
                CoreHostJitMachineProfile::X86_64(X86TargetFeatures::generic_x86_64())
            }
            Target::Riscv64 => unreachable!("test matrix excludes unsupported RISC-V"),
        };
        let target = CoreHostJitTarget::try_from_detected_facts(
            architecture,
            vendor,
            os,
            environment,
            true,
            8,
            trust_ir::Endianness::Little,
            profile,
        )
        .unwrap();
        let mut module = source_module();
        target.bind_module_target(&mut module).unwrap();
        assert_eq!(
            module.target_info.as_ref(),
            Some(target.trust_ir_target_info())
        );
        assert_eq!(
            module.target_info.as_ref().unwrap().triple,
            target.target_spec().triple()
        );
    }
}

#[test]
fn target_binding_does_not_validate_or_admit_malformed_original_source() {
    let target = tests::core_host_target();
    let mut module = source_module();
    module.functions[0].blocks[0].body[1].inst = Inst::Return {
        values: vec![ValueId::new(99)],
    };
    assert!(!trust_ir_build::validate_module(&module).is_empty());
    target.bind_module_target(&mut module).unwrap();
    assert!(!trust_ir_build::validate_module(&module).is_empty());
    assert!(
        admit_identity_core_module_for_host_jit(
            module,
            &target,
            CoreDeclaredImportManifest::empty()
        )
        .is_err()
    );
}

#[test]
fn identity_admission_still_requires_binding_then_all_existing_source_gates() {
    let target = tests::core_host_target();
    let module = source_module();
    let manifest = CoreDeclaredImportManifest::empty();
    assert!(matches!(
        admit_identity_core_module_for_host_jit(module.clone(), &target, manifest.clone()),
        Err(CoreAdmissionError::Target(
            CoreTargetContractError::ModuleTargetMissing
        ))
    ));
    let mut bound = module;
    target.bind_module_target(&mut bound).unwrap();
    let admitted = admit_identity_core_module_for_host_jit(bound, &target, manifest).unwrap();
    assert_eq!(
        admitted.target_contract().target_info(),
        target.trust_ir_target_info()
    );
}
