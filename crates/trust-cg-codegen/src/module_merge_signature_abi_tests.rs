// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Ordinary module batching retains producer records; it does not certify
//! that native calls implement these records.

use super::{
    TY_CMP_DEPTH_LIMIT, func_tys_equal_name_resolved, merge_modules, signature_abi_custody,
};
use trust_ir::signature_abi::{
    AbiArgument, AbiAttributes, AbiBinding, AbiBindingPlace, AbiFrontend, AbiPassMode, AbiRegister,
    AbiRegisterClass, AbiScalar, AbiTarget, SignatureAbi,
};
use trust_ir::{CallingConv, Endianness, FuncTyId, Module, StructPassingPolicy, TargetInfo, Ty};
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

fn placement() -> SignatureAbi {
    SignatureAbi {
        target: AbiTarget {
            triple: "aarch64-apple-darwin".into(),
            data_layout: "e-m:o-i64:64-i128:128-n32:64-S128".into(),
            abi: "aapcs64".into(),
            cpu: "generic".into(),
            features: vec![],
            target_spec: "merge-fixture-v1".into(),
            pointer_bytes: 8,
            little_endian: true,
        },
        frontend: AbiFrontend {
            name: "merge-fixture".into(),
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
    }
}

fn declaration(name: &str, recorded: bool) -> Module {
    let mut builder = ModuleBuilder::new_with_target_info(
        name,
        TargetInfo {
            triple: "aarch64-apple-darwin".into(),
            pointer_size: 8,
            endianness: Endianness::Little,
            abi: Some("aapcs64".into()),
            struct_passing: StructPassingPolicy::NativeC,
        },
    );
    let signature = builder.add_func_type(vec![Ty::I64], vec![Ty::I64]);
    builder.declare_function(name, signature);
    let mut module = builder.build().expect("ModuleBuilder::build: test fixture");
    if recorded {
        module.func_types[0].abi = Some(placement());
        assert!(module.functions[0].fn_abi(&module).unwrap().is_some());
    }
    assert!(trust_ir_build::validate_module(&module).is_empty());
    module
}

#[test]
fn merge_retains_recorded_abi_on_every_signature_including_unused_rows() {
    let mut left = declaration("left", true);
    left.func_types.push(left.func_types[0].clone());
    left.func_types[1].abi.as_mut().unwrap().frontend.revision = "unused-v2".into();
    let right = declaration("right", true);
    let input = [left, right];
    let before = input.clone();
    let merged = merge_modules(&input).unwrap();
    let original_signatures = input
        .iter()
        .flat_map(|module| module.func_types.iter().cloned())
        .collect::<Vec<_>>();
    assert_eq!(merged.func_types, original_signatures);
    for function in &merged.functions {
        assert!(function.fn_abi(&merged).unwrap().is_some());
    }
    assert_eq!(input, before);
}

#[test]
fn duplicate_declarations_require_exact_recorded_abi_custody() {
    let recorded = declaration("shared", true);
    let unrecorded = declaration("shared", false);
    let merged = merge_modules(&[recorded.clone(), recorded.clone()]).unwrap();
    assert_eq!(merged.functions.len(), 1);
    assert_eq!(merged.func_types[0].abi, recorded.func_types[0].abi);
    assert_eq!(merged.func_types[1].abi, recorded.func_types[0].abi);
    assert!(merge_modules(&[unrecorded.clone(), unrecorded.clone()]).is_ok());
    for inputs in [
        [recorded.clone(), unrecorded.clone()],
        [unrecorded, recorded.clone()],
    ] {
        let before = inputs.clone();
        let error = merge_modules(&inputs).unwrap_err();
        assert!(
            error.contains("recorded and unrecorded signature ABI"),
            "{error}"
        );
        assert_eq!(inputs, before);
    }
    for change in 0..3 {
        let mut conflicting = recorded.clone();
        let claim = conflicting.func_types[0].abi.as_mut().unwrap();
        match change {
            0 => claim.target.cpu = "other-cpu".into(),
            1 => claim.frontend.revision = "other-revision".into(),
            2 => claim.source_abi = "other-source-abi".into(),
            _ => unreachable!(),
        }
        assert!(conflicting.functions[0].fn_abi(&conflicting).is_ok());
        let error = merge_modules(&[recorded.clone(), conflicting]).unwrap_err();
        assert!(
            error.contains("recorded signature ABI claims disagree"),
            "{error}"
        );
    }
}

#[test]
fn independent_signature_comparison_refuses_erased_or_changed_claims() {
    let source = declaration("original", true);
    let merged = merge_modules(std::slice::from_ref(&source)).unwrap();
    let signature = FuncTyId::new(0);
    func_tys_equal_name_resolved(&source, signature, &merged, signature, TY_CMP_DEPTH_LIMIT)
        .unwrap();
    for erase in [false, true] {
        let mut changed = merged.clone();
        if erase {
            changed.func_types[0].abi = None;
        } else {
            changed.func_types[0].abi.as_mut().unwrap().target.cpu = "changed".into();
        }
        let error = func_tys_equal_name_resolved(
            &source,
            signature,
            &changed,
            signature,
            TY_CMP_DEPTH_LIMIT,
        )
        .unwrap_err();
        assert!(error.contains("signature ABI changed"), "{error}");
    }
    assert_eq!(
        signature_abi_custody::require_same(None, Some(&source.func_types[0])),
        Err(signature_abi_custody::CustodyError::MissingSignature)
    );
}
