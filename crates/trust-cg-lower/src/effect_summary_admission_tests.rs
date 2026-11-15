// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

use super::{AdapterError, validate_codegen_prerequisites};
use trust_ir::{EffectPlace, EffectSet, EffectSummary, FunctionSummary, Module, Ty};
use trust_ir_build::{ModuleBuilder, ValidationError};

fn writing_module(writes: EffectSet) -> Module {
    let pointer = Ty::PtrMut(Box::new(Ty::U64));
    let mut builder = ModuleBuilder::new("actual_effect_frame");
    let signature = builder.add_func_type(vec![pointer.clone(), pointer.clone()], vec![]);
    {
        let mut function = builder.function("write_second", signature);
        let entry = function.create_block();
        function.add_block_param(entry, pointer.clone());
        let second = function.add_block_param(entry, pointer);
        function.switch_to_block(entry);
        let value = function.iconst(Ty::U64, 7);
        function.store(Ty::U64, second, value);
        function.ret(vec![]);
        function.build();
    }
    let mut module = builder.build().expect("ModuleBuilder::build: test fixture");
    module.functions[0].summary =
        Some(FunctionSummary::new().with_effects(EffectSummary::pure().writing(writes)));
    module
}

#[test]
fn uncovered_write_refuses_with_the_shared_typed_frame_verdict() {
    let module = writing_module(EffectSet::of([EffectPlace::ParamPointee { index: 0 }]));
    let before = module.clone();
    let findings = trust_ir_build::validate_module(&module);
    let actual = findings
        .iter()
        .find(|error| {
            matches!(error, ValidationError::EffectSummaryViolated {
            function, effect: "writes", ..
        } if function == "write_second")
        })
        .expect("independent upstream validator names the actual missed write");
    match validate_codegen_prerequisites(&module) {
        Err(AdapterError::TrustIrAdmissionRefused { error }) => {
            assert_eq!(error, actual.to_string());
        }
        other => panic!("wrong coverage verdict: {other:?}"),
    }
    assert_eq!(module, before);
}

#[test]
fn independently_covered_and_conservative_frames_keep_compatibility_admission() {
    for writes in [
        EffectSet::of([EffectPlace::ParamPointee { index: 1 }]),
        EffectSet::Everything,
    ] {
        let module = writing_module(writes);
        let findings = trust_ir_build::validate_module(&module);
        assert!(
            !findings
                .iter()
                .any(|error| matches!(error, ValidationError::EffectSummaryViolated { .. })),
            "{findings:?}"
        );
        validate_codegen_prerequisites(&module).expect("actual write has an admitted frame");
    }
}

#[test]
fn pure_frame_refuses_the_real_write_and_absent_frame_claims_nothing() {
    let mut module = writing_module(EffectSet::Nothing);
    assert!(matches!(
        validate_codegen_prerequisites(&module),
        Err(AdapterError::TrustIrAdmissionRefused { .. })
    ));
    module.functions[0].summary = None;
    validate_codegen_prerequisites(&module).expect("no effect-frame claim to contradict");
}
