// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

use crate::adapter::{
    AdapterError, GuardCarrierArch, prepare_module_for_lir, reject_unconsumed_v41_surface,
    reject_unconsumed_v41_target_neutral_surface,
};
use trust_ir::signature_abi::{
    AbiArgument, AbiAttributes, AbiBinding, AbiBindingPlace, AbiExtension, AbiFrontend,
    AbiPassMode, AbiRegister, AbiRegisterClass, AbiScalar, AbiTarget, SignatureAbi,
};
use trust_ir::{CallingConv, Endianness, Module, StructPassingPolicy, TargetInfo, Ty};
use trust_ir_build::ModuleBuilder;

fn argument(place: AbiBindingPlace) -> AbiArgument {
    AbiArgument {
        size: 8,
        align: 8,
        mode: AbiPassMode::Direct(AbiScalar {
            register: AbiRegister {
                class: AbiRegisterClass::Integer,
                bytes: 8,
            },
            source_offset: 0,
            source_bytes: 8,
            value_bits: 64,
            attributes: AbiAttributes::default(),
        }),
        bindings: vec![AbiBinding {
            place,
            source_offset: 0,
            source_bytes: 8,
            carrier_offset: 0,
            carrier_bytes: 8,
        }],
    }
}

fn recorded_module() -> Module {
    let mut builder = ModuleBuilder::new_with_target_info(
        "recorded_placement",
        TargetInfo {
            triple: "aarch64-apple-darwin".into(),
            pointer_size: 8,
            endianness: Endianness::Little,
            abi: Some("aapcs64".into()),
            struct_passing: StructPassingPolicy::NativeC,
        },
    );
    let signature = builder.add_func_type(vec![Ty::I64], vec![Ty::I64]);
    {
        let mut function = builder.function("identity", signature);
        let entry = function.create_block();
        let input = function.add_block_param(entry, Ty::I64);
        function.switch_to_block(entry);
        function.ret(vec![input]);
        function.build();
    }
    let mut module = builder.build().expect("ModuleBuilder::build: test fixture");
    module.func_types[0].abi = Some(SignatureAbi {
        target: AbiTarget {
            triple: "aarch64-apple-darwin".into(),
            data_layout: "e-m:o-i64:64-i128:128-n32:64-S128".into(),
            abi: "aapcs64".into(),
            cpu: "generic".into(),
            features: vec![],
            target_spec: "adapter-fixture-v1".into(),
            pointer_bytes: 8,
            little_endian: true,
        },
        frontend: AbiFrontend {
            name: "adapter-fixture".into(),
            revision: "v1".into(),
        },
        convention: "aapcs64".into(),
        lowered_convention: CallingConv::C,
        source_abi: "C".into(),
        can_unwind: true,
        variadic: false,
        fixed_count: 1,
        arguments: vec![argument(AbiBindingPlace::Parameter(0))],
        result: argument(AbiBindingPlace::Result(0)),
    });
    assert!(module.functions[0].fn_abi(&module).unwrap().is_some());
    assert!(trust_ir_build::validate_module(&module).is_empty());
    module
}

fn refused(error: AdapterError, signature: usize) {
    assert!(
        matches!(&error, AdapterError::UnsupportedSignatureAbi {
        signature: found, ..
    } if *found == signature),
        "{error}"
    );
}

#[test]
fn valid_recorded_claims_refuse_before_preparation_or_native_translation() {
    let module = recorded_module();
    let before = module.clone();
    refused(
        reject_unconsumed_v41_target_neutral_surface(&module).unwrap_err(),
        0,
    );
    for arch in [
        GuardCarrierArch::AArch64,
        GuardCarrierArch::X86_64,
        GuardCarrierArch::Riscv64,
    ] {
        refused(reject_unconsumed_v41_surface(&module, arch).unwrap_err(), 0);
        match prepare_module_for_lir(&module, arch) {
            Err(error) => refused(error, 0),
            Ok(_) => panic!("recorded placement reached compatibility preparation"),
        }
    }
    refused(permit_translate_module(&module).unwrap_err(), 0);
    refused(
        crate::translate_function_with_license(&module.functions[0], &module, &permit_unlicensed())
            .unwrap_err(),
        0,
    );
    assert_eq!(module, before);
    let mut legacy = module.clone();
    legacy.func_types[0].abi = None;
    reject_unconsumed_v41_target_neutral_surface(&legacy).unwrap();
    reject_unconsumed_v41_surface(&legacy, GuardCarrierArch::AArch64).unwrap();
    assert!(prepare_module_for_lir(&legacy, GuardCarrierArch::AArch64).is_ok());
    assert!(permit_translate_module(&legacy).is_ok());
    assert!(
        crate::translate_function_with_license(&legacy.functions[0], &legacy, &permit_unlicensed())
            .is_ok()
    );
}

#[test]
fn unused_signature_rows_do_not_bypass_the_floor() {
    let mut module = recorded_module();
    module.func_types.push(module.func_types[0].clone());
    module.func_types[0].abi = None;
    assert!(module.functions[0].fn_abi(&module).unwrap().is_none());
    refused(
        reject_unconsumed_v41_target_neutral_surface(&module).unwrap_err(),
        1,
    );
    module.functions.clear();
    refused(
        reject_unconsumed_v41_target_neutral_surface(&module).unwrap_err(),
        1,
    );
    module.func_types[1].abi = None;
    reject_unconsumed_v41_target_neutral_surface(&module).unwrap();
}

#[test]
fn explicit_extensions_hidden_results_and_invalid_records_never_become_legacy() {
    let mut extended = recorded_module();
    let claim = extended.func_types[0].abi.as_mut().unwrap();
    let AbiPassMode::Direct(scalar) = &mut claim.arguments[0].mode else {
        unreachable!()
    };
    scalar.attributes.extension = AbiExtension::Sign;
    assert!(extended.functions[0].fn_abi(&extended).is_ok());
    refused(
        reject_unconsumed_v41_target_neutral_surface(&extended).unwrap_err(),
        0,
    );

    let mut hidden = recorded_module();
    hidden.functions[0].blocks.clear();
    hidden.func_types[0].params = vec![Ty::Ptr];
    hidden.func_types[0].returns.clear();
    let claim = hidden.func_types[0].abi.as_mut().unwrap();
    claim.arguments.clear();
    claim.fixed_count = 0;
    claim.result = AbiArgument {
        size: 16,
        align: 8,
        mode: AbiPassMode::Indirect {
            attributes: AbiAttributes::default(),
            metadata_attributes: None,
            on_stack: false,
            caller_copy: false,
        },
        bindings: vec![AbiBinding {
            place: AbiBindingPlace::HiddenResult(0),
            source_offset: 0,
            source_bytes: 16,
            carrier_offset: 0,
            carrier_bytes: 8,
        }],
    };
    assert!(hidden.functions[0].fn_abi(&hidden).is_ok());
    refused(
        reject_unconsumed_v41_target_neutral_surface(&hidden).unwrap_err(),
        0,
    );
    let mut invalid = hidden.clone();
    invalid.func_types[0]
        .abi
        .as_mut()
        .unwrap()
        .target
        .triple
        .clear();
    assert!(invalid.functions[0].fn_abi(&invalid).is_err());
    refused(
        reject_unconsumed_v41_target_neutral_surface(&invalid).unwrap_err(),
        0,
    );
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> crate::CodegenLicensePolicy {
    crate::CodegenLicensePolicy::default().with_unlicensed(crate::UnlicensedBodyPolicy::Permit)
}

/// `translate_module` under [`permit_unlicensed`].
fn permit_translate_module(
    module: &Module,
) -> Result<Vec<(crate::Function, crate::ProofContext)>, AdapterError> {
    crate::translate_module_for_arch_with_tls_with_license(
        module,
        GuardCarrierArch::default(),
        crate::TlsDialect::default(),
        &permit_unlicensed(),
    )
}
