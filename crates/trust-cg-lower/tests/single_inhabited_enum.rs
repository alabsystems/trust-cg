// Copyright 2026 Andrew Yates. Apache-2.0.
#[path = "common/single_inhabited.rs"]
mod fixture;
use trust_cg_lower::{CodegenLicensePolicy, UnlicensedBodyPolicy};
use trust_ir::{EnumTagEncoding, Ty};

#[test]
fn selected_zero_and_nonzero_lower_original_constant_and_memory_bodies() {
    for active in 0..2 {
        for memory in [false, true] {
            let module = fixture::module(active, memory);
            assert!(trust_ir_build::validate_module(&module).is_empty());
            let result = trust_cg_lower::translate_function_with_license(
                &module.functions[0],
                &module,
                &CodegenLicensePolicy::default().with_unlicensed(UnlicensedBodyPolicy::Permit),
            );
            assert!(
                result.is_ok(),
                "selected={active}, memory={memory}: {result:?}"
            );
        }
    }
}

#[test]
fn original_selected_index_and_every_inactive_proof_are_required() {
    for mutate in 0..14 {
        let mut module = fixture::module(1, false);
        match mutate {
            0 => {
                module.enums[0].layout.as_mut().unwrap().encoding =
                    EnumTagEncoding::SingleInhabited { variant: 2 }
            }
            1 => module.enums[0].variants[0].fields = vec![Ty::U64],
            2 => module.enums[0].variants[1].fields = vec![Ty::Never],
            3 => {
                module.enums[0]
                    .layout
                    .as_mut()
                    .unwrap()
                    .variant_field_offsets[0] = vec![0]
            }
            4 => module.enums[0]
                .layout
                .as_mut()
                .unwrap()
                .variant_field_offsets
                .pop()
                .map(|_| ())
                .unwrap(),
            5 => {
                module.enums[0]
                    .layout
                    .as_mut()
                    .unwrap()
                    .variant_field_offsets[1][0] = 8
            }
            6 => module.enums[0].layout.as_mut().unwrap().size = 16,
            7 => module.enums[0].layout.as_mut().unwrap().align = 16,
            8 => {
                module.enums[0].variants[0].fields =
                    vec![Ty::Never, Ty::Storage(trust_ir::StorageLayout::new(8, 8))]
            }
            9 => module.enums[0].variants[0].fields = vec![Ty::Enum(trust_ir::EnumId::new(999))],
            10 => module.enums[0].variants[0].fields = vec![Ty::Ref(Box::new(Ty::Never))],
            11 => {
                let duplicate = module.enums[0].clone();
                module.enums.push(duplicate);
            }
            12 => {
                module.enums[0].variants[0].fields =
                    vec![Ty::Never, Ty::Enum(trust_ir::EnumId::new(999))]
            }
            13 => {
                module.enums[0].variants[0].fields =
                    vec![Ty::Never, Ty::Enum(trust_ir::EnumId::new(0))]
            }
            _ => unreachable!(),
        }
        let error = trust_cg_lower::adapter::translate_type_in_module(
            &module,
            &Ty::Enum(trust_ir::EnumId::new(0)),
        )
        .expect_err("the adapter itself must refuse below typed module admission");
        assert!(
            format!("{error}").contains("producer-provided layout descriptor"),
            "mutation {mutate}: {error}"
        );
    }
}

#[test]
fn legacy_untagged_does_not_gain_multiple_variants() {
    let mut module = fixture::module(1, false);
    module.enums[0].layout.as_mut().unwrap().encoding = EnumTagEncoding::Untagged;
    assert!(
        trust_cg_lower::adapter::translate_type_in_module(
            &module,
            &Ty::Enum(trust_ir::EnumId::new(0))
        )
        .is_err()
    );
}

#[test]
fn storage_behind_a_pointer_remains_an_address_not_a_by_value_child() {
    let mut module = fixture::module(1, false);
    module.enums[0].variants[0].fields = vec![
        Ty::Never,
        Ty::PtrConst(Box::new(Ty::Storage(trust_ir::StorageLayout::new(8, 8)))),
    ];
    assert!(
        trust_cg_lower::adapter::translate_type_in_module(
            &module,
            &Ty::Enum(trust_ir::EnumId::new(0))
        )
        .is_ok()
    );
}
