// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Recorded signature custody in the ordinary argument-promotion consumer.
//! A structurally reconciled ABI is still not native authority. Promotion
//! changes carriers, so these controls require refusal, never record erasure.

use super::*;
use trust_cg_verify::trust_ir_mid_tv::check_pass;
use trust_ir::CallingConv;
use trust_ir::signature_abi::{
    AbiArgument, AbiAttributes, AbiBinding, AbiBindingPlace, AbiFrontend, AbiPassMode, AbiRegister,
    AbiRegisterClass, AbiScalar, AbiTarget, SignatureAbi,
};

const CALLEE: &str = "read.tcg.crate.00000000000000aa";

fn program() -> Module {
    trust_ir::parser::parse_module(
        "; TrustIr text format v1\n\
         module \"argpromo_signature_custody\"\n\
         target \"wasm32-unknown-unknown\" 4 little\n\
         functy.0 = (ptr) -> (i64)\n\
         functy.1 = () -> (i64)\n\
         fn @read.tcg.crate.00000000000000aa(functy.0) {\n\
             ; #visibility: hidden\n\
         bb0(%0: ptr):\n\
             %1 = load i64, ptr %0\n\
             ret %1\n\
         }\n\
         fn @caller(functy.1) {\n\
         bb0():\n\
             %0 = alloca i64, align 8\n\
             %1 = const i64 17\n\
             store i64 %1, ptr %0\n\
             %2 = call @func.0(%0)\n\
             ret %2\n\
         }\n",
    )
    .expect("ordinary initialized-slot argument-promotion source")
}

fn argument(place: AbiBindingPlace, bytes: u16) -> AbiArgument {
    AbiArgument {
        size: u64::from(bytes),
        align: u64::from(bytes),
        mode: AbiPassMode::Direct(AbiScalar {
            register: AbiRegister {
                class: AbiRegisterClass::Integer,
                bytes: u64::from(bytes),
            },
            source_offset: 0,
            source_bytes: u64::from(bytes),
            value_bits: bytes * 8,
            attributes: AbiAttributes::default(),
        }),
        bindings: vec![AbiBinding {
            place,
            source_offset: 0,
            source_bytes: u64::from(bytes),
            carrier_offset: 0,
            carrier_bytes: u64::from(bytes),
        }],
    }
}

fn recorded() -> Module {
    let mut module = program();
    module.func_types[0].abi = Some(SignatureAbi {
        target: AbiTarget {
            triple: "wasm32-unknown-unknown".into(),
            data_layout: "e-m:e-p:32:32-i64:64-n32:64-S128".into(),
            abi: "wasm32".into(),
            cpu: "generic".into(),
            features: vec![],
            target_spec: "argpromo-custody-control-v1".into(),
            pointer_bytes: 4,
            little_endian: true,
        },
        frontend: AbiFrontend {
            name: "argpromo-custody-control".into(),
            revision: "v1".into(),
        },
        convention: "wasm32".into(),
        lowered_convention: CallingConv::C,
        source_abi: "C".into(),
        can_unwind: true,
        variadic: false,
        fixed_count: 1,
        arguments: vec![argument(AbiBindingPlace::Parameter(0), 4)],
        result: argument(AbiBindingPlace::Result(0), 8),
    });
    // Use the actual shared reconciliation contract, not a malformed record
    // that would make any downstream refusal vacuous. This is structural only.
    let view = module.functions[0]
        .fn_abi(&module)
        .expect("record agrees with actual signature, target and function")
        .expect("recorded ABI");
    assert_eq!(view.calling_convention(), CallingConv::C);
    assert_eq!(view.placement(), module.func_types[0].abi.as_ref().unwrap());
    module
}

fn context(module: &Module) -> PassContext<'_> {
    PassContext {
        module,
        pointer_bits: 32,
    }
}

fn plan(module: &Module) -> Vec<(ArgPromoParam, Shape)> {
    let shape = shape(module, &module.functions[0], 0).expect("actual read-only pointer shape");
    assert_eq!(
        shape.reads,
        vec![ArgPromoField {
            offset: 0,
            ty: Ty::I64
        }]
    );
    assert!(shape.writes.is_empty());
    vec![(
        ArgPromoParam {
            index: 0,
            reads: shape.reads.clone(),
            writes: shape.writes.clone(),
        },
        shape,
    )]
}

#[test]
fn valid_recorded_abi_refuses_before_template_or_caller_carrier_rewrite() {
    let module = recorded();
    let before = serde_json::to_value(&module).unwrap();
    let callee = &module.functions[0];
    assert_eq!(callee.name, CALLEE);
    assert_eq!(module.func_types[0].params, [Ty::Ptr]);
    assert_eq!(callee.blocks[0].params[0].1, Ty::Ptr);
    assert!(template(&module, callee.id).is_none());
    assert!(
        ArgPromo::new(BTreeSet::new())
            .run(&context(&module), &module.functions[1])
            .is_none()
    );
    assert_eq!(
        refusals(&context(&module), &module.functions[1]),
        [(CALLEE.to_owned(), 0, "callee_not_admitted")],
    );
    assert_eq!(serde_json::to_value(&module).unwrap(), before);
}

#[test]
fn legacy_unrecorded_signature_still_promotes_and_replays_actual_witness() {
    let module = program();
    let before = serde_json::to_value(&module).unwrap();
    assert!(module.func_types[0].abi.is_none());
    assert!(template(&module, module.functions[0].id).is_some());
    let (rewritten, witness) = ArgPromo::new(BTreeSet::new())
        .run(&context(&module), &module.functions[1])
        .expect("otherwise identical unrecorded callee remains promotable");
    check_pass(&module, 32, &module.functions[1], &rewritten, &witness)
        .expect("ordinary independent argument-promotion witness replay");
    let PassWitness::ArgPromo(witness) = witness else {
        panic!("actual argument-promotion witness");
    };
    assert_eq!(witness.sites.len(), 1);
    assert_eq!(witness.sites[0].callee, module.functions[0].id);
    assert_eq!(witness.new_functions.len(), 1);
    assert_eq!(witness.new_func_types.len(), 1);
    assert_eq!(witness.new_func_types[0].params, [Ty::I64]);
    assert_eq!(witness.new_func_types[0].returns, [Ty::I64]);
    assert!(witness.new_func_types[0].abi.is_none());
    assert_ne!(rewritten, module.functions[1]);
    assert_eq!(serde_json::to_value(&module).unwrap(), before);
}

#[test]
fn direct_clone_seam_refuses_record_even_when_unrecorded_clone_already_exists() {
    let legacy = program();
    let recorded = recorded();
    let before = serde_json::to_value(&recorded).unwrap();
    for seeded in [false, true] {
        let mut types = vec![];
        let mut functions = vec![];
        if seeded {
            let id = Clones {
                new_types: &mut types,
                new_functions: &mut functions,
            }
            .get(
                &legacy,
                &legacy.functions[0],
                &legacy.func_types[0],
                &plan(&legacy),
            )
            .expect("actual legacy clone, not invented remap state");
            assert_eq!(functions[0].id, id);
            assert_eq!(types[0].params, [Ty::I64]);
            assert!(types[0].abi.is_none());
        }
        let retained_types = types.clone();
        let retained_functions = functions.clone();
        assert!(
            Clones {
                new_types: &mut types,
                new_functions: &mut functions,
            }
            .get(
                &recorded,
                &recorded.functions[0],
                &recorded.func_types[0],
                &plan(&recorded),
            )
            .is_none(),
            "recorded ABI cannot create or reuse carrier-changing clone; seeded={seeded}"
        );
        assert_eq!(types, retained_types);
        assert_eq!(functions, retained_functions);
        assert_eq!(serde_json::to_value(&recorded).unwrap(), before);
    }
}
