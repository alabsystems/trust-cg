// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

use super::*;
use trust_ir::{ArgExt, PassMode};

#[test]
fn typed_output_abi_valid_pass_annotations_cannot_reuse_ordinary_register_bytes() {
    let original = fixture();
    assert!(trust_ir_build::validate_module(&original).is_empty());
    let lir = lower(&original);
    for parameter in 0..original.func_types[0].params.len() {
        for pass in [
            PassMode::Direct,
            PassMode::Cast {
                pieces: vec![Ty::U32, Ty::U32],
            },
        ] {
            let mut changed = original.clone();
            let attrs = &mut changed.functions[0].attrs;
            attrs.params.resize(parameter + 1, ParamAttrs::default());
            attrs.params[parameter].pass = Some(pass.clone());
            let errors = trust_ir_build::validate_module(&changed);
            assert!(
                errors.is_empty(),
                "{pass:?} parameter {parameter}: {errors:?}"
            );
            assert!(
                trust_cg_lower::translate_function_with_license(
                    &changed.functions[0],
                    &changed,
                    &permit_unlicensed()
                )
                .is_err()
            );
            for paired in [false, true] {
                assert!(
                    matches!(
                        check_aarch64_trust_ir_output_bytes(&changed, 0, &lir, &code(paired)),
                        Err(TrustIrOutputError::Source(_))
                    ),
                    "{pass:?} parameter {parameter}, paired={paired}"
                );
            }
        }
    }
}

#[test]
fn typed_output_abi_unchecked_extension_and_return_facts_are_refused() {
    let original = fixture();
    let lir = lower(&original);
    let annotations = [
        ParamAttrs {
            ext: ArgExt::ZeroExt,
            ..Default::default()
        },
        ParamAttrs {
            ext: ArgExt::SignExt,
            ..Default::default()
        },
        ParamAttrs {
            pass: Some(PassMode::Ignore),
            ..Default::default()
        },
        ParamAttrs {
            pass: Some(PassMode::Pair),
            ..Default::default()
        },
        ParamAttrs {
            pass: Some(PassMode::Indirect { on_stack: false }),
            ..Default::default()
        },
        ParamAttrs {
            pass: Some(PassMode::Indirect { on_stack: true }),
            ..Default::default()
        },
    ];
    for annotation in annotations {
        // This public checker must also refuse malformed ABI facts when the
        // caller has not run canonical module validation first.
        for parameter in [0, 1] {
            let mut changed = original.clone();
            changed.functions[0]
                .attrs
                .params
                .resize(parameter + 1, ParamAttrs::default());
            changed.functions[0].attrs.params[parameter] = annotation.clone();
            assert!(matches!(
                check_aarch64_trust_ir_output_bytes(&changed, 0, &lir, &code(false)),
                Err(TrustIrOutputError::Source(_))
            ));
        }
        let mut changed = original.clone();
        changed.functions[0].attrs.ret = annotation;
        assert!(matches!(
            check_aarch64_trust_ir_output_bytes(&changed, 0, &lir, &code(true)),
            Err(TrustIrOutputError::Source(_))
        ));
    }
    let mut changed = original;
    changed.functions[0].attrs.ret.nonnull = true;
    assert!(matches!(
        check_aarch64_trust_ir_output_bytes(&changed, 0, &lir, &code(true)),
        Err(TrustIrOutputError::Source(_))
    ));
}

#[test]
fn typed_output_abi_empty_slots_and_pointer_facts_preserve_declared_requirements() {
    let mut module = fixture();
    let lir = lower(&module);
    module.functions[0]
        .attrs
        .params
        .resize(module.func_types[0].params.len(), ParamAttrs::default());
    module.functions[0].attrs.params[0] = ParamAttrs {
        noalias: true,
        nonnull: true,
        align: Some(8),
        dereferenceable: Some(40),
        ..Default::default()
    };
    assert!(trust_ir_build::validate_module(&module).is_empty());
    for paired in [false, true] {
        let bytes = code(paired);
        let checked = check_aarch64_trust_ir_output_bytes(&module, 0, &lir, &bytes).unwrap();
        assert_eq!(checked.requirements().byte_extent, 40);
        assert_eq!(checked.requirements().alignment, 8);
    }
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
