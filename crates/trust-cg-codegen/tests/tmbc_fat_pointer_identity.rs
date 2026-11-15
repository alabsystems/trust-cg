// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Exercise the real nested tMBC/TrustIR transport boundary, then module merge.
//! Equal physical layouts do not authorize changing pointer meaning. These
//! tests establish neither executable vtable dispatch nor native refinement.

use trust_cg_codegen::module_merge::merge_modules;
use trust_cg_codegen::pipeline::{decode_tmbc, encode_tmbc, load_module_from_bytes};
use trust_ir::{FatPtrKind, FieldDef, Module, StructDef, StructId, Ty, TyId};
use trust_ir_build::ModuleBuilder;

fn kinds() -> [FatPtrKind; 5] {
    [
        FatPtrKind::Slice(TyId::new(0)),
        FatPtrKind::Str,
        FatPtrKind::TraitObject { trait_id: 7 },
        FatPtrKind::ContainerLen,
        FatPtrKind::ContainerVtable,
    ]
}

fn carrier_module(name: &str, kind: FatPtrKind) -> Module {
    let mut builder = ModuleBuilder::new(name);
    assert_eq!(builder.add_type(Ty::I64), TyId::new(0));
    let carrier = Ty::FatPtr(kind);
    builder.add_type(carrier.clone());
    let signature = builder.add_func_type(vec![carrier.clone()], vec![carrier.clone()]);
    let mut function = builder.function(format!("{name}_identity"), signature);
    let entry = function.create_block();
    let value = function.add_block_param(entry, carrier.clone());
    function.switch_to_block(entry);
    function.ret(vec![value]);
    function.build();
    let mut module = builder.build().expect("ModuleBuilder::build: test fixture");
    module.structs.push(StructDef {
        origin: None,
        id: StructId::new(0),
        name: "Holder".into(),
        fields: vec![FieldDef {
            name: "pointer".into(),
            ty: carrier,
            offset: None,
        }],
        size: None,
        align: None,
        repr: Default::default(),
    });
    module
}

fn inner_version(bytes: &[u8]) -> u32 {
    assert_eq!(&bytes[..4], b"tMBC");
    assert_eq!(&bytes[4..8], &1u32.to_le_bytes());
    assert_eq!(&bytes[8..16], b"TRUST_IR");
    u32::from_le_bytes(bytes[16..20].try_into().unwrap())
}

#[test]
fn all_fat_pointer_kinds_survive_real_tmbc_and_auto_detection() {
    let mut encodings = Vec::new();
    for kind in kinds() {
        let original = carrier_module("identity", kind);
        let bytes = encode_tmbc(&original).unwrap();
        let decoded = decode_tmbc(&bytes).unwrap();
        assert_eq!(decoded, original, "kind {kind:?}: full module identity");
        assert_eq!(load_module_from_bytes(&bytes).unwrap(), original);
        assert_eq!(encode_tmbc(&decoded).unwrap(), bytes);
        // Same names, layout and body shape; only the carrier meaning differs.
        assert!(
            !encodings.contains(&bytes),
            "kind {kind:?} aliased another kind"
        );
        encodings.push(bytes);
    }
}

#[test]
fn nested_payload_uses_v40_only_when_the_module_needs_container_vtable() {
    for kind in kinds() {
        let bytes = encode_tmbc(&carrier_module("version", kind)).unwrap();
        assert_eq!(
            inner_version(&bytes),
            if kind == FatPtrKind::ContainerVtable {
                40
            } else {
                38
            },
            "the outer envelope and minimum required IR payload version are distinct"
        );
        assert!(decode_tmbc(&bytes).is_ok());
    }
}

#[test]
fn container_vtable_cannot_be_smuggled_through_an_older_payload_header() {
    let original = encode_tmbc(&carrier_module("downgrade", FatPtrKind::ContainerVtable)).unwrap();
    assert_eq!(inner_version(&original), 40);
    assert!(decode_tmbc(&original).is_ok(), "positive control");
    for version in [38u32, 39] {
        let mut forged = original.clone();
        forged[16..20].copy_from_slice(&version.to_le_bytes());
        assert!(matches!(
            trust_ir::binary::deserialize_module(&forged[8..]),
            Err(trust_ir::binary::BinaryError::InvalidTag(4))
        ));
        let error = decode_tmbc(&forged).unwrap_err().to_string();
        assert!(
            error.contains("invalid tag: 4"),
            "wrong transport refusal: {error}"
        );
        assert!(load_module_from_bytes(&forged).is_err());
    }
    let mut wrong_envelope = original;
    wrong_envelope[4..8].copy_from_slice(&2u32.to_le_bytes());
    let error = decode_tmbc(&wrong_envelope).unwrap_err().to_string();
    assert!(error.contains("unsupported tMBC version: 2"), "{error}");
}

#[test]
fn v40_transport_rejects_every_truncated_prefix_and_trailing_bytes() {
    let bytes = encode_tmbc(&carrier_module("bounds", FatPtrKind::ContainerVtable)).unwrap();
    assert!(decode_tmbc(&bytes).is_ok(), "positive control");
    for end in 0..bytes.len() {
        assert!(decode_tmbc(&bytes[..end]).is_err(), "accepted prefix {end}");
    }
    let mut trailing = bytes;
    trailing.push(0);
    let error = decode_tmbc(&trailing).unwrap_err().to_string();
    assert!(
        error.contains("trailing bytes after canonical module payload"),
        "{error}"
    );
}

#[test]
fn decoded_container_vtables_merge_without_aliasing_same_layout_kinds() {
    let transport =
        |name, kind| decode_tmbc(&encode_tmbc(&carrier_module(name, kind)).unwrap()).unwrap();
    let left = transport("left", FatPtrKind::ContainerVtable);
    let right = transport("right", FatPtrKind::ContainerVtable);
    let merged = merge_modules(&[left.clone(), right]).unwrap();
    assert_eq!(
        merged.structs.len(),
        1,
        "identical named holder deduplicates"
    );
    assert_eq!(
        merged.structs[0].fields[0].ty,
        Ty::FatPtr(FatPtrKind::ContainerVtable)
    );
    assert_eq!(merged.functions.len(), 2);
    for function in &merged.functions {
        let signature = &merged.func_types[function.ty.as_usize()];
        assert_eq!(
            signature.params,
            vec![Ty::FatPtr(FatPtrKind::ContainerVtable)]
        );
        assert_eq!(signature.returns, signature.params);
        assert_eq!(function.blocks[0].params[0].1, signature.params[0]);
    }
    let encoded = encode_tmbc(&merged).unwrap();
    assert_eq!(inner_version(&encoded), 40);
    assert_eq!(decode_tmbc(&encoded).unwrap(), merged);
    for kind in kinds()
        .into_iter()
        .filter(|kind| *kind != FatPtrKind::ContainerVtable)
    {
        let conflict = transport("conflict", kind);
        let error = merge_modules(&[left.clone(), conflict]).unwrap_err();
        assert!(
            error.contains("Holder") && error.contains("DIFFERENT structure"),
            "{kind:?}: {error}"
        );
    }
}
