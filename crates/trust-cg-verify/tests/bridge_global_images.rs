// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
//! Validate the bridge's exact allocation images through the canonical type
//! checker and object lowering. These checks confer no pointer authority.

#[path = "../../rustc-codegen-trust-cg/src/global_image.rs"]
mod global_image;

use global_image::type_image;
use trust_cg_codegen::{compiler::module_object_globals, module_merge::merge_modules};
use trust_ir::{Constant, Global, Linkage, Module, StructDef, StructId, StructRepr, Ty};

/// The session pointer size `global_image` reads from its crate root (the
/// bridge's `session_pointer_bytes`); every image here is a 64-bit target's.
fn session_pointer_bytes() -> u64 {
    8
}

fn add_image(module: &mut Module, name: &str, elements: Vec<Constant>, size: u64, align: u64) {
    let image = type_image(module, name, Constant::Aggregate(elements), size, align).unwrap();
    module.globals.push(Global {
        name: name.into(),
        ty: image.ty,
        initializer: Some(image.initializer),
        align: Some(image.align),
        mutable: false,
        linkage: Linkage::External,
        tls: None,
        section: None,
        visibility: trust_ir::Visibility::Default,
        retained: false,
    });
}

fn validate(module: &Module) {
    let errors = trust_ir_build::validate_module(module);
    assert!(errors.is_empty(), "{errors:?}");
}

#[test]
fn byte_images_preserve_exact_extent_and_allocation_alignment() {
    for size in [0, 1, 7, 8, 17, 19, 92, 257] {
        for align in [1, 2, 8, 16, 64] {
            let mut module = Module::new("bytes");
            module.types = vec![Ty::I64, Ty::Ptr, Ty::U8, Ty::U64];
            let prefix = module.types.clone();
            let bytes: Vec<u8> = (0..size).map(|i| (i * 137) as u8).collect();
            add_image(
                &mut module,
                "bytes",
                bytes.iter().map(|b| Constant::Int((*b).into())).collect(),
                size,
                align,
            );
            validate(&module);
            assert_eq!(module.types, prefix);
            assert!(module.structs.is_empty());
            assert_eq!(
                module.globals[0].ty,
                Ty::Array(trust_ir::TyId::new(2), size)
            );
            let globals = module_object_globals(&module).unwrap();
            assert_eq!(globals[0].data, bytes);
            assert_eq!(u64::from(globals[0].align), align);
            assert!(globals[0].symbol_refs.is_empty());
        }
    }
}

#[test]
fn packed_images_preserve_unaligned_relocations_addends_and_tail_bytes() {
    let mut module = Module::new("packed");
    module.types = vec![Ty::I64, Ty::Ptr];
    add_image(
        &mut module,
        "packed",
        vec![
            Constant::Int(0xaa),
            Constant::symbol_addr_with_addend("external", -19),
            Constant::symbol_addr_with_addend("packed", 1),
            Constant::Int(0xbb),
            Constant::Int(0xcc),
            Constant::symbol_addr_with_addend("function", 0),
            Constant::Int(0xdd),
        ],
        28,
        64,
    );
    validate(&module);
    assert_eq!(&module.types[..2], &[Ty::I64, Ty::Ptr]);
    let def = &module.structs[0];
    assert_eq!(def.size, Some(28));
    assert_eq!(def.align, Some(1));
    assert_eq!(def.repr, StructRepr::Packed(1));
    assert_eq!(
        def.fields
            .iter()
            .map(|f| f.offset.unwrap())
            .collect::<Vec<_>>(),
        [0, 1, 9, 17, 19, 27]
    );
    let global = module_object_globals(&module).unwrap().remove(0);
    let mut expected = vec![0; 28];
    expected[0] = 0xaa;
    expected[17] = 0xbb;
    expected[18] = 0xcc;
    expected[27] = 0xdd;
    assert_eq!(global.data, expected);
    assert_eq!(global.align, 64);
    assert_eq!(
        global
            .symbol_refs
            .iter()
            .map(|r| (r.offset, r.symbol.as_str(), r.addend))
            .collect::<Vec<_>>(),
        [(1, "external", -19), (9, "packed", 1), (19, "function", 0)]
    );
}

#[test]
fn pointer_only_and_cyclic_images_keep_storage_types_after_module_merge() {
    let mut modules = Vec::new();
    for (name, target) in [("first", "second"), ("second", "first")] {
        let mut module = Module::new(name);
        if name == "second" {
            module.types.push(Ty::U64);
        }
        add_image(&mut module, name, vec![Constant::symbol_addr(target)], 8, 8);
        validate(&module);
        modules.push(module);
    }
    let merged = merge_modules(&modules).unwrap();
    validate(&merged);
    let globals = module_object_globals(&merged).unwrap();
    for (index, global) in globals.iter().enumerate() {
        assert_eq!(global.data, [0; 8]);
        assert_eq!(global.align, 8);
        assert_eq!(global.symbol_refs.len(), 1);
        assert_eq!(
            global.symbol_refs[0].symbol,
            if index == 0 { "second" } else { "first" }
        );
    }
    assert_ne!(merged.globals[0].ty, merged.globals[1].ty);
}

#[test]
fn sparse_struct_ids_do_not_collide_and_byte_type_prefix_stays_fixed() {
    let mut module = Module::new("sparse");
    module.structs.push(StructDef {
        origin: None,
        id: StructId::new(12),
        name: "existing".into(),
        fields: vec![],
        size: Some(0),
        align: Some(1),
        repr: StructRepr::Packed(1),
    });
    add_image(
        &mut module,
        "pointer",
        vec![Constant::symbol_addr("external")],
        8,
        8,
    );
    assert_eq!(module.globals[0].ty, Ty::Struct(StructId::new(13)));
    validate(&module);
    assert_eq!(module_object_globals(&module).unwrap()[0].data, [0; 8]);
}

#[test]
fn malformed_images_are_refused_before_mutating_type_catalogs() {
    let byte = || Constant::Aggregate(vec![Constant::Int(1)]);
    for (image, size, align) in [
        (byte(), 1, 0),
        (byte(), 1, 3),
        (byte(), 1, 1_u64 << 32),
        (byte(), 0, 1),
        (byte(), 2, 1),
        (Constant::Int(1), 1, 1),
        (Constant::Aggregate(vec![Constant::Int(-1)]), 1, 1),
        (Constant::Aggregate(vec![Constant::Int(256)]), 1, 1),
        (Constant::Aggregate(vec![Constant::symbol_addr("")]), 8, 8),
        (Constant::Aggregate(vec![Constant::Aggregate(vec![])]), 0, 1),
        (
            Constant::Aggregate(vec![Constant::Bytes {
                data: vec![1],
                utf8: false,
            }]),
            1,
            1,
        ),
    ] {
        let mut module = Module::new("invalid");
        let before = serde_json::to_value(&module).unwrap();
        assert!(type_image(&mut module, "invalid", image, size, align).is_err());
        assert_eq!(serde_json::to_value(&module).unwrap(), before);
    }
    let mut module = Module::new("exhausted");
    module.structs.push(StructDef {
        origin: None,
        id: StructId::new(u32::MAX),
        name: "last".into(),
        fields: vec![],
        size: Some(0),
        align: Some(1),
        repr: StructRepr::Packed(1),
    });
    let before = serde_json::to_value(&module).unwrap();
    assert!(
        type_image(
            &mut module,
            "no_id",
            Constant::Aggregate(vec![Constant::symbol_addr("external")]),
            8,
            8
        )
        .is_err()
    );
    assert_eq!(serde_json::to_value(&module).unwrap(), before);
}

#[test]
fn actual_frontend_images_are_canonical_and_keep_allocation_alignment() {
    let fixtures =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/global_images");
    let mut paths: Vec<_> = std::fs::read_dir(fixtures)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .collect();
    paths.sort();
    assert_eq!(paths.len(), 22);
    let mut unwind = 0;
    let mut aligned = 0;
    let mut packed = 0;
    for path in paths {
        let module: Module = serde_json::from_slice(&std::fs::read(&path).unwrap()).unwrap();
        let errors = trust_ir_build::validate_module(&module);
        // The address-return controls still expose the separate legacy tagged
        // integer/reference producer. Keep those exact refusals; canonical
        // storage images do not manufacture reference validity or erase them.
        let mut expected = Vec::new();
        for function in &module.functions {
            let ty = match function.name.as_str() {
                "image_aligned" => Some("&[ty.4 x 2]"),
                "image_literal" => Some("&(u8, u8, u8, u8, u8, u8, u8)"),
                _ => None,
            };
            if let Some(ty) = ty {
                expected.push(trust_ir_build::ValidationError::ConstTypeMismatch {
                    location: format!("function '{}' bb0", function.name),
                    expected: ty.into(),
                    actual: "int".into(),
                });
            }
        }
        assert_eq!(errors, expected, "{}", path.display());
        let mut storage = module.clone();
        storage.functions.clear();
        assert!(trust_ir_build::validate_module(&storage).is_empty());
        assert!(module.proof_obligations.is_empty());
        assert!(module.proof_certificates.is_empty());
        let globals = module_object_globals(&module).unwrap();
        for global in &globals {
            if global.name == "IMAGE_PACKED" {
                packed += 1;
                assert_eq!(global.align, 1);
                assert_eq!(global.data.len(), 11);
                assert_eq!(global.data[0], 0xa5);
                assert_eq!(&global.data[9..], &[0xfe, 0xca]);
                assert_eq!(global.symbol_refs.len(), 1);
                assert_eq!(global.symbol_refs[0].offset, 1);
            }
            if global.name.starts_with("image_aligned.const.") {
                aligned += 1;
                assert_eq!(global.align, 16);
                assert_eq!(global.data.len(), 32);
                assert_eq!(&global.data[..17], &[0x5a; 17]);
            }
        }
        if module.functions.iter().any(|f| f.name == "bounds_unwind") {
            unwind += 1;
            assert_eq!(globals.len(), 3);
            let nodes: Vec<_> = module.functions[0]
                .blocks
                .iter()
                .flat_map(|b| &b.body)
                .collect();
            assert!(
                nodes
                    .iter()
                    .any(|node| matches!(node.inst, trust_ir::Inst::CondBr { .. }))
            );
            assert!(nodes.iter().any(|node| matches!(
                node.inst,
                trust_ir::Inst::Call { .. } | trust_ir::Inst::Invoke { .. }
            )));
            assert!(
                !nodes
                    .iter()
                    .any(|node| matches!(node.inst, trust_ir::Inst::Assert { .. }))
            );
        }
    }
    assert_eq!(unwind, 2);
    assert_eq!(aligned, 4);
    assert_eq!(packed, 2);
}
