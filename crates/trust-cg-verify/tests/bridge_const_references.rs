// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

#[path = "../../rustc-codegen-trust-cg/src/const_references.rs"]
mod const_references;

use trust_cg_codegen::{compiler::module_object_globals, global_stub::encode_global_addr_stub};
use trust_cg_lower::adapter::AdapterError;
use trust_ir::{
    Block, BlockId, Constant, FuncId, FuncTy, Function, Global, Inst, InstrNode, Linkage, Module,
    Ty, TyId, ValueId,
};

fn fixture(pointee: Ty, data: Vec<u8>, align: u32) -> Module {
    let mut module = Module::new("reference");
    module.types = vec![Ty::U8, Ty::I128];
    module.globals.push(Global {
        name: "allocation".into(),
        ty: Ty::Array(TyId::new(0), data.len() as u64),
        mutable: false,
        initializer: Some(Constant::Bytes { data, utf8: false }),
        linkage: Linkage::Internal,
        tls: None,
        align: Some(align),
        section: None,
        visibility: trust_ir::Visibility::Default,
        retained: false,
    });
    let ty = Ty::Ref(Box::new(pointee));
    let signature = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![ty.clone()],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = Function::new(FuncId::new(0), "address", signature, BlockId::new(0));
    let mut block = Block::new(BlockId::new(0));
    block.body.push(
        InstrNode::new(Inst::Const {
            ty,
            value: Constant::Int(encode_global_addr_stub(0, 0).unwrap()),
        })
        .with_result(ValueId::new(0)),
    );
    block.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(0)],
    }));
    function.blocks.push(block);
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
    module
}

/// Six of the 22 captured frontend modules carry 8 tagged reference constants
/// that need repair. Typed admission refuses each defined function of those
/// captures before the repair, so no lowering of the original exists to
/// compare with the repaired one. Checked for every capture: `canonicalize`
/// repairs exactly the constants `validate_module` reports and the result
/// validates with its type table unchanged; `module_object_globals` is equal
/// before and after, every `ObjectGlobal` field compared (bytes, relocations
/// with addends, alignment, binding, section and flags); a capture with
/// nothing to repair is left byte-identical; every defined function lowers
/// after the repair; and the repair is idempotent. The function-side rewrite
/// of a repaired capture is checked only by validation and lowering.
#[test]
fn captured_frontend_reference_constants_validate_and_keep_exact_object_images() {
    let root =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/global_images");
    let mut paths: Vec<_> = std::fs::read_dir(root)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .collect();
    paths.sort();
    assert_eq!(paths.len(), 22);
    let mut repaired = 0;
    let mut refused = 0;
    for path in paths {
        let mut module: Module = serde_json::from_slice(&std::fs::read(&path).unwrap()).unwrap();
        let original = serde_json::to_value(&module).unwrap();
        let before = module_object_globals(&module).unwrap();
        let errors = trust_ir_build::validate_module(&module);
        let original_types = module.types.clone();
        if !errors.is_empty() {
            for function in module
                .functions
                .iter()
                .filter(|function| !function.is_declaration())
            {
                match trust_cg_lower::translate_function_with_license(
                    function,
                    &module,
                    &permit_unlicensed(),
                ) {
                    Err(AdapterError::TrustIrAdmissionRefused { error })
                        if error.contains("const type mismatch") =>
                    {
                        refused += 1;
                    }
                    Err(error) => panic!("{}: {error}", path.display()),
                    Ok(_) => panic!(
                        "{}: {} lowered before repair",
                        path.display(),
                        function.name
                    ),
                }
            }
        }
        let changes = const_references::canonicalize(&mut module);
        assert_eq!(changes, errors.len(), "{}", path.display());
        assert!(
            trust_ir_build::validate_module(&module).is_empty(),
            "{}",
            path.display()
        );
        assert_eq!(
            module_object_globals(&module).unwrap(),
            before,
            "{}",
            path.display()
        );
        assert_eq!(module.types, original_types);
        if changes == 0 {
            assert_eq!(
                serde_json::to_value(&module).unwrap(),
                original,
                "{}",
                path.display()
            );
        }
        for function in module
            .functions
            .iter()
            .filter(|function| !function.is_declaration())
        {
            trust_cg_lower::translate_function_with_license(
                function,
                &module,
                &permit_unlicensed(),
            )
            .unwrap();
        }
        let once = serde_json::to_value(&module).unwrap();
        assert_eq!(const_references::canonicalize(&mut module), 0);
        assert_eq!(serde_json::to_value(&module).unwrap(), once);
        repaired += changes;
    }
    assert_eq!(repaired, 8);
    assert_eq!(refused, 8);
}

#[test]
fn signed_unsigned_and_array_views_preserve_all_bits_and_alignment() {
    for ty in [
        Ty::I8,
        Ty::U8,
        Ty::I16,
        Ty::U16,
        Ty::I32,
        Ty::U32,
        Ty::I64,
        Ty::U64,
        Ty::I128,
        Ty::U128,
    ] {
        let size = (ty.bit_width().unwrap() / 8) as usize;
        for byte in [0, 0x5a, 0x80, 0xff] {
            let mut module = fixture(ty.clone(), vec![byte; size], size as u32);
            let before = module_object_globals(&module).unwrap();
            assert_eq!(
                const_references::canonicalize(&mut module),
                1,
                "{ty:?}/{byte}"
            );
            assert!(
                trust_ir_build::validate_module(&module).is_empty(),
                "{ty:?}/{byte}"
            );
            assert_eq!(module_object_globals(&module).unwrap(), before);
        }
    }
    for count in [0, 1, 2, 17] {
        let mut module = fixture(
            Ty::Array(TyId::new(1), count),
            vec![0x9a; count as usize * 16],
            16,
        );
        let before = module_object_globals(&module).unwrap();
        assert_eq!(const_references::canonicalize(&mut module), 1);
        assert!(trust_ir_build::validate_module(&module).is_empty());
        assert_eq!(module_object_globals(&module).unwrap(), before);
    }
}

#[test]
fn one_allocation_keeps_identity_for_multiple_references_and_bare_addresses() {
    let mut module = fixture(Ty::Tuple(vec![Ty::U8; 7]), b"literal".to_vec(), 1);
    let body = &mut module.functions[0].blocks[0].body;
    let mut duplicate = body[0].clone();
    duplicate.results = vec![ValueId::new(1)];
    body.insert(1, duplicate);
    body.insert(
        2,
        InstrNode::new(Inst::Const {
            ty: Ty::Ptr,
            value: Constant::Int(encode_global_addr_stub(0, 0).unwrap()),
        })
        .with_result(ValueId::new(2)),
    );
    let before = module_object_globals(&module).unwrap();
    assert_eq!(const_references::canonicalize(&mut module), 2);
    assert!(trust_ir_build::validate_module(&module).is_empty());
    assert_eq!(module.globals.len(), 1);
    assert_eq!(module_object_globals(&module).unwrap(), before);
    for node in &module.functions[0].blocks[0].body[..2] {
        assert!(
            matches!(&node.inst, Inst::Const { value: Constant::SymbolAddr { symbol, addend: 0 }, .. } if symbol == "allocation")
        );
    }
    assert!(matches!(
        module.functions[0].blocks[0].body[2].inst,
        Inst::Const {
            value: Constant::Int(_),
            ..
        }
    ));
}

#[test]
fn conflicting_views_and_interior_or_mutable_references_leave_module_unchanged() {
    for ty in [
        Ty::Ref(Box::new(Ty::U64)),
        Ty::RefMut(Box::new(Ty::U64)),
        Ty::PtrConst(Box::new(Ty::U64)),
        Ty::PtrMut(Box::new(Ty::U64)),
    ] {
        for offset in [0, 1] {
            let mut module = fixture(Ty::Array(TyId::new(0), 8), vec![0; 8], 8);
            module.functions[0].blocks[0].body.insert(
                1,
                InstrNode::new(Inst::Const {
                    ty: ty.clone(),
                    value: Constant::Int(encode_global_addr_stub(0, offset).unwrap()),
                })
                .with_result(ValueId::new(1)),
            );
            let before = serde_json::to_value(&module).unwrap();
            assert_eq!(const_references::canonicalize(&mut module), 0);
            assert_eq!(serde_json::to_value(&module).unwrap(), before);
        }
    }
}

#[test]
fn invalid_storage_metadata_and_other_symbol_users_prevent_retyping() {
    for mutation in 0..13 {
        let mut module = fixture(Ty::I128, vec![0x5a; 16], 16);
        match mutation {
            0 => module.globals[0].align = Some(8),
            1 => module.globals[0].mutable = true,
            2 => module.globals[0].tls = Some(trust_ir::TlsModel::GeneralDynamic),
            3 => module.globals[0].linkage = Linkage::Weak,
            4 => module.globals[0].initializer = None,
            5 => module.globals[0].ty = Ty::Array(TyId::new(1), 1),
            6 => module.globals[0].ty = Ty::Array(TyId::new(0), 15),
            7 => {
                let other = module.globals[0].clone();
                module.globals.push(other);
            }
            8 => module.functions[0].name = "allocation".into(),
            9 => module.functions[0].blocks[0].body.insert(
                1,
                InstrNode::new(Inst::Const {
                    ty: Ty::Ptr,
                    value: Constant::symbol_addr("allocation"),
                })
                .with_result(ValueId::new(1)),
            ),
            10 => {
                module.globals[0].initializer =
                    Some(Constant::Aggregate(vec![Constant::symbol_addr("external")]))
            }
            11 => module.globals[0].align = Some(3),
            _ => {
                module.globals[0].initializer = Some(Constant::Bytes {
                    data: vec![0; 15],
                    utf8: false,
                })
            }
        }
        let before = serde_json::to_value(&module).unwrap();
        assert_eq!(
            const_references::canonicalize(&mut module),
            0,
            "mutation {mutation}"
        );
        assert_eq!(serde_json::to_value(&module).unwrap(), before);
    }
}

#[test]
fn unsupported_pointee_views_do_not_change_existing_module_meaning() {
    for ty in [
        Ty::Ptr,
        Ty::Tuple(vec![Ty::U8, Ty::U64]),
        Ty::Array(TyId::new(99), 1),
    ] {
        let mut module = fixture(ty, vec![0; 16], 16);
        let before = serde_json::to_value(&module).unwrap();
        assert_eq!(const_references::canonicalize(&mut module), 0);
        assert_eq!(serde_json::to_value(&module).unwrap(), before);
    }
}

#[test]
fn bool_char_pointer_width_and_float_views_keep_their_canonical_values() {
    for (ty, bytes, align) in [
        (Ty::Bool, vec![0], 1),
        (Ty::Bool, vec![1], 1),
        (Ty::Char, (0x10ffff_u32).to_le_bytes().to_vec(), 4),
        (Ty::Isize, (-123_i64).to_le_bytes().to_vec(), 8),
        (Ty::Usize, u64::MAX.to_le_bytes().to_vec(), 8),
        (Ty::F32, (-0.0_f32).to_le_bytes().to_vec(), 4),
        (Ty::F32, f32::INFINITY.to_le_bytes().to_vec(), 4),
        (Ty::F64, (-0.0_f64).to_le_bytes().to_vec(), 8),
        (Ty::F64, f64::INFINITY.to_le_bytes().to_vec(), 8),
        (Ty::F64, 0x7ff0000000001234_u64.to_le_bytes().to_vec(), 8),
    ] {
        let mut module = fixture(ty.clone(), bytes, align);
        let before = module_object_globals(&module).unwrap();
        assert_eq!(const_references::canonicalize(&mut module), 1, "{ty:?}");
        assert!(trust_ir_build::validate_module(&module).is_empty());
        assert_eq!(module_object_globals(&module).unwrap(), before);
    }
    for (ty, bytes, align) in [
        (Ty::Bool, vec![2], 1),
        (Ty::Char, 0xd800_u32.to_le_bytes().to_vec(), 4),
        (Ty::Char, 0x110000_u32.to_le_bytes().to_vec(), 4),
    ] {
        let mut module = fixture(ty, bytes, align);
        let before = serde_json::to_value(&module).unwrap();
        assert_eq!(const_references::canonicalize(&mut module), 0);
        assert_eq!(serde_json::to_value(&module).unwrap(), before);
    }
}

#[test]
fn proof_contexts_and_unsupported_target_layouts_are_not_rewritten() {
    for mutation in 0..3 {
        let mut module = fixture(Ty::I128, vec![0; 16], 16);
        if mutation == 0 {
            module.functions[0].blocks[0].body[0].proof_context =
                Some(trust_ir::proof::ProofContext::default());
        } else {
            module.target_info = Some(trust_ir::TargetInfo {
                triple: "aarch64-unknown-linux-gnu".into(),
                pointer_size: if mutation == 1 { 4 } else { 8 },
                endianness: if mutation == 2 {
                    trust_ir::Endianness::Big
                } else {
                    trust_ir::Endianness::Little
                },
                abi: None,
                struct_passing: trust_ir::StructPassingPolicy::Unclassified,
            });
        }
        let before = serde_json::to_value(&module).unwrap();
        assert_eq!(const_references::canonicalize(&mut module), 0);
        assert_eq!(serde_json::to_value(&module).unwrap(), before);
    }
}

#[test]
fn fresh_frontend_modules_are_canonical_before_lowering() {
    let root =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/const_references");
    let mut modules = 0;
    let mut references = 0;
    let mut addresses = 0;
    for entry in std::fs::read_dir(root).unwrap() {
        let path = entry.unwrap().path();
        let mut module: Module = serde_json::from_slice(&std::fs::read(&path).unwrap()).unwrap();
        let errors = trust_ir_build::validate_module(&module);
        assert!(errors.is_empty(), "{}: {errors:?}", path.display());
        module_object_globals(&module).unwrap();
        assert!(module.proof_obligations.is_empty());
        assert!(module.proof_certificates.is_empty());
        for function in &module.functions {
            for node in function.blocks.iter().flat_map(|block| &block.body) {
                match &node.inst {
                    Inst::Const {
                        ty: Ty::Ref(_),
                        value,
                    } => {
                        assert!(matches!(value, Constant::SymbolAddr { addend: 0, .. }));
                        references += 1;
                    }
                    Inst::Const {
                        ty: Ty::Ptr,
                        value: Constant::Int(value),
                    } => {
                        assert!(
                            trust_cg_codegen::global_stub::decode_global_addr_stub(*value)
                                .is_none()
                        );
                    }
                    Inst::GlobalAddr { .. } => addresses += 1,
                    _ => {}
                }
            }
        }
        let before = serde_json::to_value(&module).unwrap();
        assert_eq!(const_references::canonicalize(&mut module), 0);
        assert_eq!(serde_json::to_value(&module).unwrap(), before);
        modules += 1;
    }
    assert_eq!(modules, 38);
    assert_eq!(references, 34);
    assert_eq!(addresses, 4);
}

#[test]
fn fresh_reference_storage_types_remain_bound_after_module_merge() {
    let root =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/const_references");
    let modules: Vec<Module> = [
        "image_aligned-O0-module1.trust-ir.json",
        "image_aligned-O0-module2.trust-ir.json",
        "image_scalars-O0-module1.trust-ir.json",
    ]
    .into_iter()
    .map(|name| serde_json::from_slice(&std::fs::read(root.join(name)).unwrap()).unwrap())
    .collect();
    let merged = trust_cg_codegen::module_merge::merge_modules(&modules).unwrap();
    assert!(trust_ir_build::validate_module(&merged).is_empty());
    assert_eq!(merged.functions.len(), 3);
    let expected: Vec<_> = modules
        .iter()
        .flat_map(|module| module_object_globals(module).unwrap())
        .collect();
    assert_eq!(module_object_globals(&merged).unwrap(), expected);
}

#[test]
fn declared_tuple_order_and_nan_payloads_preserve_the_original_image() {
    let pointee = Ty::Tuple(vec![Ty::U8, Ty::U8]);
    let mut module = fixture(pointee.clone(), vec![0x12, 0x34], 1);
    module.types.push(pointee);
    module.target_info = Some(trust_ir::TargetInfo {
        triple: "aarch64-unknown-linux-gnu".into(),
        pointer_size: 8,
        endianness: trust_ir::Endianness::Little,
        abi: None,
        struct_passing: trust_ir::StructPassingPolicy::Unclassified,
    });
    module.tuple_layouts.push(trust_ir::TupleLayoutDescriptor {
        tuple_type: TyId::new(2),
        size: 2,
        align: 1,
        field_offsets: vec![1, 0],
    });
    let images = module_object_globals(&module).unwrap();
    assert_eq!(const_references::canonicalize(&mut module), 1);
    assert!(trust_ir_build::validate_module(&module).is_empty());
    assert_eq!(module_object_globals(&module).unwrap(), images);
    assert_eq!(
        module.globals[0].initializer,
        Some(Constant::Aggregate(vec![
            Constant::Int(0x34),
            Constant::Int(0x12)
        ]))
    );
    // A padded descriptor reads its scalar fields at their stated offsets.
    // Nonzero padding cannot be reproduced by an aggregate initializer.
    for padding in [0, 0xa5] {
        let pointee = Ty::Tuple(vec![Ty::U8, Ty::U64]);
        let mut bytes = vec![padding; 16];
        bytes[..8].copy_from_slice(&123_u64.to_le_bytes());
        bytes[8] = 7;
        let mut padded = fixture(pointee.clone(), bytes, 8);
        padded.target_info = module.target_info.clone();
        padded.types.push(pointee);
        padded.tuple_layouts.push(trust_ir::TupleLayoutDescriptor {
            tuple_type: TyId::new(2),
            size: 16,
            align: 8,
            field_offsets: vec![8, 0],
        });
        let before = serde_json::to_value(&padded).unwrap();
        let images = module_object_globals(&padded).unwrap();
        assert_eq!(
            const_references::canonicalize(&mut padded),
            usize::from(padding == 0)
        );
        assert_eq!(module_object_globals(&padded).unwrap(), images);
        if padding != 0 {
            assert_eq!(serde_json::to_value(&padded).unwrap(), before);
        } else {
            assert!(trust_ir_build::validate_module(&padded).is_empty());
            assert_eq!(
                padded.globals[0].initializer,
                Some(Constant::Aggregate(vec![
                    Constant::Int(7),
                    Constant::Int(123)
                ]))
            );
        }
    }

    // Float widening/narrowing may quiet a signaling NaN. A constructor that
    // cannot reproduce the original payload must leave the allocation alone.
    let mut module = fixture(Ty::F32, 0x7f800123_u32.to_le_bytes().to_vec(), 4);
    let original = serde_json::to_value(&module).unwrap();
    let images = module_object_globals(&module).unwrap();
    let changes = const_references::canonicalize(&mut module);
    assert_eq!(module_object_globals(&module).unwrap(), images);
    if changes == 0 {
        assert_eq!(serde_json::to_value(&module).unwrap(), original);
    } else {
        assert!(trust_ir_build::validate_module(&module).is_empty());
    }
    println!("F32_PAYLOAD_REFERENCE_CONVERSION={changes}");
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
