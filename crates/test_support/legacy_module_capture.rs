// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Test-only v55-v57 capture compatibility with the v58+ module schema.
//! `closure_layouts` follows `drop_glue` in positional serialization, so the
//! latter now always emits, including when empty. Upgrade only the EXPECTED
//! historical JSON's missing table; retain all actual fields and every authored
//! expected field exactly. This grants no source, caller, proof or native authority.

use serde_json::Value;
use trust_ir::Module;

fn upgraded_expected(legacy: &Value) -> Value {
    let mut expected = legacy.clone();
    expected
        .as_object_mut()
        .expect("legacy module capture must be a JSON object")
        .entry("drop_glue")
        .or_insert_with(|| Value::Array(vec![]));
    expected
}

fn assert_serialized_image(actual: Value, legacy: &Value, context: &str) {
    assert_eq!(actual, upgraded_expected(legacy), "{context}");
}

pub(crate) fn assert_legacy_module_image(actual: &Module, legacy: &Value, context: &str) {
    assert_serialized_image(serde_json::to_value(actual).unwrap(), legacy, context);
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;
    use trust_ir::signature_abi::{
        AbiArgument, AbiAttributes, AbiBinding, AbiBindingPlace, AbiFrontend, AbiPassMode,
        AbiRegister, AbiRegisterClass, AbiScalar, AbiTarget, SignatureAbi,
    };
    use trust_ir::ty::StructDef;
    use trust_ir::value::StructId;
    use trust_ir::{CallingConv, DropGlueEntry, Endianness, StructPassingPolicy, TargetInfo, Ty};
    use trust_ir_build::ModuleBuilder;

    fn builder() -> ModuleBuilder {
        ModuleBuilder::new_with_target_info(
            "legacy_module_capture_control",
            TargetInfo {
                triple: "aarch64-apple-darwin".into(),
                pointer_size: 8,
                endianness: Endianness::Little,
                abi: Some("aapcs64".into()),
                struct_passing: StructPassingPolicy::NativeC,
            },
        )
    }

    fn module(value: i128) -> Module {
        let mut builder = builder();
        let signature = builder.add_func_type(vec![], vec![Ty::I64]);
        let mut function = builder.function("value", signature);
        let entry = function.create_block();
        function.switch_to_block(entry);
        let result = function.iconst(Ty::I64, value);
        function.ret(vec![result]);
        function.build();
        let module = builder.build().expect("ModuleBuilder::build: test fixture");
        assert!(trust_ir_build::validate_module(&module).is_empty());
        module
    }

    fn legacy(module: &Module) -> Value {
        let mut image = serde_json::to_value(module).unwrap();
        assert_eq!(
            image.as_object_mut().unwrap().remove("drop_glue"),
            Some(json!([])),
        );
        image
    }

    fn refuses(actual: &Module, expected: &Value) {
        assert!(
            std::panic::catch_unwind(|| {
                assert_legacy_module_image(actual, expected, "exact capture control");
            })
            .is_err()
        );
    }

    fn recorded_abi() -> SignatureAbi {
        SignatureAbi {
            target: AbiTarget {
                triple: "aarch64-apple-darwin".into(),
                data_layout: "e-m:o-i64:64-i128:128-n32:64-S128".into(),
                abi: "aapcs64".into(),
                cpu: "generic".into(),
                features: vec![],
                target_spec: "capture-control-v1".into(),
                pointer_bytes: 8,
                little_endian: true,
            },
            frontend: AbiFrontend {
                name: "capture-control".into(),
                revision: "v1".into(),
            },
            convention: "aapcs64".into(),
            lowered_convention: CallingConv::C,
            source_abi: "C".into(),
            can_unwind: true,
            variadic: false,
            fixed_count: 0,
            arguments: vec![],
            result: AbiArgument {
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
                    place: AbiBindingPlace::Result(0),
                    source_offset: 0,
                    source_bytes: 8,
                    carrier_offset: 0,
                    carrier_bytes: 8,
                }],
            },
        }
    }

    #[test]
    fn missing_empty_drop_glue_upgrades_expected_only() {
        let module = module(17);
        let expected = legacy(&module);
        let retained = expected.clone();
        assert_legacy_module_image(&module, &expected, "unchanged historical image");
        assert_eq!(expected, retained);
        assert!(expected.get("drop_glue").is_none());
        assert_eq!(upgraded_expected(&expected)["drop_glue"], json!([]));
    }

    #[test]
    fn explicit_empty_table_is_already_exact() {
        let module = module(17);
        let expected = serde_json::to_value(&module).unwrap();
        assert_eq!(upgraded_expected(&expected), expected);
        assert_legacy_module_image(&module, &expected, "already current schema");
    }

    #[test]
    fn changed_instruction_is_not_schema_compatibility() {
        let expected = legacy(&module(17));
        refuses(&module(18), &expected);
    }

    #[test]
    fn missing_other_empty_table_is_not_defaulted() {
        let module = module(17);
        let mut expected = legacy(&module);
        assert_eq!(
            expected.as_object_mut().unwrap().remove("files"),
            Some(json!([])),
        );
        refuses(&module, &expected);
    }

    #[test]
    fn added_and_changed_abi_records_are_not_erased() {
        let mut actual = module(17);
        let unrecorded = legacy(&actual);
        actual.func_types[0].abi = Some(recorded_abi());
        assert!(trust_ir_build::validate_module(&actual).is_empty());
        assert!(actual.functions[0].fn_abi(&actual).unwrap().is_some());
        refuses(&actual, &unrecorded);
        let recorded = legacy(&actual);
        assert_legacy_module_image(&actual, &recorded, "exact recorded ABI");
        actual.func_types[0].abi.as_mut().unwrap().frontend.revision = "v2".into();
        refuses(&actual, &recorded);
    }

    #[test]
    fn unexpected_actual_and_expected_fields_remain_visible() {
        let actual = module(17);
        let expected = legacy(&actual);
        let mut serialized = serde_json::to_value(&actual).unwrap();
        serialized["unexpected_serializer_field"] = json!(true);
        assert!(
            std::panic::catch_unwind(|| {
                assert_serialized_image(serialized, &expected, "unexpected actual field");
            })
            .is_err()
        );
        let mut expected = expected;
        expected["unexpected_capture_field"] = json!(true);
        refuses(&actual, &expected);
    }

    #[test]
    fn explicit_nonempty_drop_glue_is_retained_not_replaced() {
        let mut builder = builder();
        let owned = builder.add_struct(StructDef {
            id: StructId::new(0),
            name: "Owned".into(),
            fields: vec![],
            size: Some(0),
            align: Some(1),
            repr: Default::default(),
            origin: None,
        });
        let signature = builder.add_func_type(vec![Ty::Ptr], vec![]);
        let glue = builder.declare_function("drop_owned", signature);
        let mut actual = builder.build().expect("ModuleBuilder::build: test fixture");
        actual.drop_glue.push(DropGlueEntry {
            glue,
            ty: Ty::Struct(owned),
        });
        assert!(trust_ir_build::validate_module(&actual).is_empty());
        let expected = serde_json::to_value(&actual).unwrap();
        assert_eq!(upgraded_expected(&expected), expected);
        assert_legacy_module_image(&actual, &expected, "exact recorded drop table");
        let mut wrong = expected.clone();
        wrong["drop_glue"][0]["ty"] = json!("U64");
        refuses(&actual, &wrong);
        let mut missing = expected;
        missing.as_object_mut().unwrap().remove("drop_glue");
        refuses(&actual, &missing);
    }

    #[test]
    fn malformed_explicit_drop_glue_is_not_repaired() {
        let actual = module(17);
        for malformed in [json!(null), json!("invalid"), json!([{"unknown": true}])] {
            let mut expected = legacy(&actual);
            expected["drop_glue"] = malformed.clone();
            assert_eq!(upgraded_expected(&expected)["drop_glue"], malformed);
            refuses(&actual, &expected);
        }
    }
}
