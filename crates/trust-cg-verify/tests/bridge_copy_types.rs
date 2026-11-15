// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

#[path = "../../rustc-codegen-trust-cg/src/canonicalize_copies.rs"]
mod canonicalize_copies;
#[path = "../../rustc-codegen-trust-cg/src/pointer_casts.rs"]
mod pointer_casts;

/// The session pointer width `pointer_casts` reads from its crate root
/// (the bridge's `session_pointer_bits`); every module here is 64-bit.
fn session_pointer_bits() -> u32 {
    64
}

/// The bridge's `canonicalize_reinterpret_copies` over `function`, minting each
/// new value id past every id the function defines
/// (`Function::fresh_value_ids`), as the bridge mints them from its context.
fn canonicalize_reinterpret_copies(function: &mut Function) {
    let mut fresh = function.fresh_value_ids();
    canonicalize_copies::canonicalize_reinterpret_copies(function, None, || {
        fresh.take().expect("value id space exhausted")
    });
}
use trust_cg_verify::source_bound_frame::check_aarch64_trust_ir_output_bytes;
use trust_ir::{
    Block, BlockId, CastOp, FatPtrKind, FuncId, FuncTy, Function, Inst, InstrNode, Module, Ty,
    ValueId,
};
use trust_ir_build::{ValidationError, validate_module};

#[test]
fn alloca_address_copies_from_twenty_four_real_callers_use_typed_casts() {
    use trust_cg_verify::source_bound_frame::check_aarch64_scalar_cell_source;
    let rows: Vec<serde_json::Value> =
        serde_json::from_str(include_str!("../src/source_bound_cell_sources_before.json")).unwrap();
    assert_eq!(rows.len(), 24);
    for row in rows {
        let mut module: Module = serde_json::from_value(row["module"].clone()).unwrap();
        let lir: trust_cg_lower::Function = serde_json::from_value(row["lir"].clone()).unwrap();
        let errors = validate_module(&module);
        assert_eq!(errors.len(), 1, "{}: {errors:?}", row["case"]);
        assert!(
            matches!(&errors[0], ValidationError::OperandTypeMismatch { op, .. } if op == "copy")
        );
        assert!(check_aarch64_scalar_cell_source(&module, &lir).is_err());
        let original = module.clone();
        canonicalize_reinterpret_copies(&mut module.functions[0]);
        assert!(validate_module(&module).is_empty(), "{}", row["case"]);
        check_aarch64_scalar_cell_source(&module, &lir).unwrap();
        let mut changes = 0;
        for (before, after) in original.functions[0]
            .blocks
            .iter()
            .zip(&module.functions[0].blocks)
        {
            for (before, after) in before.body.iter().zip(&after.body) {
                if before.inst != after.inst {
                    let Inst::Copy { ty, operand } = &before.inst else {
                        panic!("only copy changes")
                    };
                    assert_eq!(
                        after.inst,
                        Inst::Cast {
                            op: CastOp::PtrToPtr,
                            src_ty: Ty::Ptr,
                            dst_ty: ty.clone(),
                            operand: *operand,
                        }
                    );
                    assert_eq!(before.results, after.results);
                    changes += 1;
                }
            }
        }
        assert_eq!(changes, 1, "{}", row["case"]);
        let normalized = serde_json::to_value(&module).unwrap();
        canonicalize_reinterpret_copies(&mut module.functions[0]);
        assert_eq!(serde_json::to_value(module).unwrap(), normalized);
    }
}

fn copy_module(source: Ty, destination: Ty) -> Module {
    let mut module = Module::new("copy_reinterpretation");
    let signature = module
        .add_func_type(FuncTy {
            params: vec![source.clone()],
            returns: vec![destination.clone()],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let entry = BlockId::new(0);
    let mut function = trust_ir::Function::new(FuncId::new(0), "copy", signature, entry);
    let mut block = Block::new(entry);
    block.params.push((ValueId::new(0), source));
    block.body.push(
        InstrNode::new(Inst::Copy {
            ty: destination,
            operand: ValueId::new(0),
        })
        .with_result(ValueId::new(1)),
    );
    block.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(1)],
    }));
    function.blocks.push(block);
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
    module
}

#[test]
fn captured_writer_replaces_five_reference_copies_with_explicit_typed_casts() {
    for input in [
        include_str!("fixtures/output_memory_writer-O0.trust-ir.json"),
        include_str!("fixtures/output_memory_writer-O1.trust-ir.json"),
    ] {
        let mut module: Module = serde_json::from_str(input).unwrap();
        let mut original_errors = validate_module(&module);
        let copy_errors = original_errors.iter().filter(|error|
            matches!(error, ValidationError::OperandTypeMismatch { op, .. } if op == "copy")).count();
        assert_eq!(
            copy_errors, 5,
            "the original five pointer Copies must fail type validation"
        );
        original_errors.retain(|error|
            !matches!(error, ValidationError::OperandTypeMismatch { op, .. } if op == "copy"));
        // The O0 capture predates certificate transport: all five discharged
        // bounds claims have missing certificate/site evidence. Preserve those
        // exact refusals. The annotation-free O1 capture is fully well-formed
        // after its five Copy type errors are repaired.
        if module.proof_obligations.is_empty() {
            assert!(original_errors.is_empty());
        } else {
            assert_eq!(module.proof_obligations.len(), 5);
            assert_eq!(original_errors.len(), 15);
            for obligation in 0..5 {
                for error in [
                    ValidationError::ProofRefUnresolved {
                        function: 0,
                        obligation,
                        missing: false,
                    },
                    ValidationError::ProofRefSiteMismatch {
                        function: 0,
                        obligation,
                    },
                    ValidationError::DischargedWithoutCertificate { obligation },
                ] {
                    assert!(original_errors.contains(&error));
                }
            }
        }
        let mut expected = module.clone();
        let mut count = 0;
        for node in expected.functions[0]
            .blocks
            .iter_mut()
            .flat_map(|b| &mut b.body)
        {
            if matches!(&node.inst, Inst::Copy { ty: Ty::Ptr, operand } if operand.index() == 1) {
                node.inst = Inst::Cast {
                    op: CastOp::PtrToPtr,
                    src_ty: Ty::RefMut(Box::new(Ty::Tuple(vec![Ty::U64; 5]))),
                    dst_ty: Ty::Ptr,
                    operand: ValueId::new(1),
                };
                count += 1;
            }
        }
        assert_eq!(count, 5);
        canonicalize_reinterpret_copies(&mut module.functions[0]);
        assert_eq!(
            serde_json::to_value(&module).unwrap(),
            serde_json::to_value(&expected).unwrap()
        );
        assert_eq!(
            validate_module(&module),
            original_errors,
            "normalization must fix the Copy errors without hiding invalid proof claims"
        );
        let (lir, _) = trust_cg_lower::translate_function_with_license(
            &module.functions[0],
            &module,
            &permit_unlicensed(),
        )
        .unwrap();
        // Independent reference words, not a claim that the Rust compile has
        // emitted or certified these bytes. Keep the diagnostic binding live.
        let code: Vec<u8> = [
            0xa9bf_7bfd_u32,
            0x9100_03fd,
            0xa900_0801,
            0xa901_1003,
            0xf900_1005,
            0xa8c1_7bfd,
            0xd65f_03c0,
        ]
        .into_iter()
        .flat_map(u32::to_le_bytes)
        .collect();
        let checked = check_aarch64_trust_ir_output_bytes(&module, 0, &lir, &code).unwrap();
        assert_eq!(checked.requirements().byte_extent, 40);
        assert!(std::ptr::eq(checked.module(), &module));
        for mutation in 0..5 {
            let mut wrong = module.clone();
            let node = wrong.functions[0]
                .blocks
                .iter_mut()
                .flat_map(|b| &mut b.body)
                .find(|n| {
                    matches!(
                        n.inst,
                        Inst::Cast {
                            op: CastOp::PtrToPtr,
                            ..
                        }
                    )
                })
                .unwrap();
            let Inst::Cast {
                op,
                src_ty,
                dst_ty,
                operand,
            } = &mut node.inst
            else {
                unreachable!()
            };
            match mutation {
                0 => *src_ty = Ty::Ptr,
                1 => *src_ty = Ty::U64,
                2 => *dst_ty = Ty::RefMut(Box::new(Ty::U64)),
                3 => *op = CastOp::Bitcast,
                _ => *operand = ValueId::new(2),
            }
            assert!(
                check_aarch64_trust_ir_output_bytes(&wrong, 0, &lir, &code).is_err(),
                "mutation {mutation}"
            );
        }
        canonicalize_reinterpret_copies(&mut module.functions[0]);
        assert_eq!(
            serde_json::to_value(&module).unwrap(),
            serde_json::to_value(&expected).unwrap()
        );
    }
}

#[test]
fn thin_reference_and_raw_pointer_addresses_keep_their_original_source_types() {
    for source in [
        Ty::Ptr,
        Ty::Ref(Box::new(Ty::U64)),
        Ty::RefMut(Box::new(Ty::U64)),
        Ty::PtrConst(Box::new(Ty::U64)),
        Ty::PtrMut(Box::new(Ty::U64)),
    ] {
        for destination in [
            Ty::Ptr,
            Ty::PtrConst(Box::new(Ty::U8)),
            Ty::PtrMut(Box::new(Ty::U8)),
        ] {
            let mut module = copy_module(source.clone(), destination.clone());
            canonicalize_reinterpret_copies(&mut module.functions[0]);
            if source == destination {
                assert!(matches!(
                    module.functions[0].blocks[0].body[0].inst,
                    Inst::Copy { .. }
                ));
            } else {
                assert_eq!(
                    module.functions[0].blocks[0].body[0].inst,
                    Inst::Cast {
                        op: CastOp::PtrToPtr,
                        src_ty: source.clone(),
                        dst_ty: destination,
                        operand: ValueId::new(0)
                    }
                );
            }
            assert!(validate_module(&module).is_empty());
        }
    }
    let mut integers = copy_module(Ty::I64, Ty::U64);
    canonicalize_reinterpret_copies(&mut integers.functions[0]);
    assert!(matches!(
        integers.functions[0].blocks[0].body[0].inst,
        Inst::Cast {
            op: CastOp::Bitcast,
            ..
        }
    ));
    assert!(validate_module(&integers).is_empty());
}

#[test]
fn copy_normalization_preserves_identical_types_and_refuses_unrelated_conversions() {
    for (source, destination) in [
        (Ty::Ptr, Ty::Ptr),
        (Ty::U64, Ty::U64),
        (Ty::RefMut(Box::new(Ty::U64)), Ty::RefMut(Box::new(Ty::U64))),
        (Ty::FatPtr(FatPtrKind::Str), Ty::Ptr),
        (Ty::Rc(Box::new(Ty::U64)), Ty::Ptr),
        (Ty::Bool, Ty::U64),
        (Ty::U32, Ty::U64),
        (Ty::U64, Ty::Ptr),
        (Ty::Ptr, Ty::FatPtr(FatPtrKind::Str)),
    ] {
        let identical = source == destination;
        let mut module = copy_module(source, destination);
        let original = serde_json::to_value(&module).unwrap();
        canonicalize_reinterpret_copies(&mut module.functions[0]);
        assert_eq!(serde_json::to_value(&module).unwrap(), original);
        assert_eq!(
            validate_module(&module).is_empty(),
            identical,
            "unchanged invalid conversions must still fail the original validator"
        );
    }
}

/// A copy between two DIFFERENT thin pointer types whose destination is a
/// reference (`Ptr` / a raw pointer / another reference into `&T` / `&mut T`)
/// is an address re-typed to the type its consumer declares
/// (`pointer_casts::can_retype_thin_address`): it becomes one `PtrToPtr` with
/// the copy's own operand and result, and the module validates. The re-type
/// states no pointee layout or dereference authority of its own.
#[test]
fn copy_into_a_reference_type_is_an_explicit_thin_retype() {
    for (source, destination) in [
        (Ty::Ptr, Ty::RefMut(Box::new(Ty::U64))),
        (Ty::PtrConst(Box::new(Ty::U64)), Ty::Ref(Box::new(Ty::U64))),
        (Ty::RefMut(Box::new(Ty::U64)), Ty::Ref(Box::new(Ty::U8))),
    ] {
        let mut module = copy_module(source.clone(), destination.clone());
        assert!(!validate_module(&module).is_empty());
        canonicalize_reinterpret_copies(&mut module.functions[0]);
        assert_eq!(
            module.functions[0].blocks[0].body[0].inst,
            Inst::Cast {
                op: CastOp::PtrToPtr,
                src_ty: source,
                dst_ty: destination,
                operand: ValueId::new(0),
            }
        );
        assert!(validate_module(&module).is_empty());
    }
}

#[test]
fn pointer_integer_casts_use_plain_pointer_carriers_and_preserve_typed_endpoints() {
    for integer in [Ty::U64, Ty::I64] {
        for pointer in [
            Ty::Ptr,
            Ty::PtrConst(Box::new(Ty::U8)),
            Ty::PtrMut(Box::new(Ty::U64)),
            Ty::Ref(Box::new(Ty::U64)),
            Ty::RefMut(Box::new(Ty::U64)),
        ] {
            for op in [CastOp::PtrToInt, CastOp::IntToPtr] {
                if op == CastOp::IntToPtr && matches!(pointer, Ty::Ref(_) | Ty::RefMut(_)) {
                    continue;
                }
                let (source, destination) = if op == CastOp::PtrToInt {
                    (pointer.clone(), integer.clone())
                } else {
                    (integer.clone(), pointer.clone())
                };
                let mut module = copy_module(source.clone(), destination.clone());
                let block = &mut module.functions[0].blocks[0];
                block.body.clear();
                let mut allocated = 0;
                pointer_casts::emit_pointer_integer_cast(
                    block,
                    op,
                    source.clone(),
                    destination.clone(),
                    ValueId::new(0),
                    ValueId::new(1),
                    || {
                        allocated += 1;
                        ValueId::new(2)
                    },
                )
                .unwrap();
                assert_eq!(allocated, usize::from(pointer != Ty::Ptr));
                let expected = if pointer == Ty::Ptr {
                    vec![(op, source, destination, 0, 1)]
                } else if op == CastOp::PtrToInt {
                    vec![
                        (CastOp::PtrToPtr, source, Ty::Ptr, 0, 2),
                        (op, Ty::Ptr, destination, 2, 1),
                    ]
                } else {
                    vec![
                        (op, source, Ty::Ptr, 0, 2),
                        (CastOp::PtrToPtr, Ty::Ptr, destination, 2, 1),
                    ]
                };
                assert_eq!(
                    block.body,
                    expected
                        .into_iter()
                        .map(
                            |(op, src_ty, dst_ty, operand, result)| InstrNode::new(Inst::Cast {
                                op,
                                src_ty,
                                dst_ty,
                                operand: ValueId::new(operand)
                            })
                            .with_result(ValueId::new(result))
                        )
                        .collect::<Vec<_>>()
                );
                block.body.push(InstrNode::new(Inst::Return {
                    values: vec![ValueId::new(1)],
                }));
                assert!(validate_module(&module).is_empty(), "{op:?} {pointer:?}");
                trust_cg_lower::translate_function_with_license(
                    &module.functions[0],
                    &module,
                    &permit_unlicensed(),
                )
                .unwrap();
            }
        }
    }
}

#[test]
fn pointer_integer_cast_refusals_leave_the_block_and_value_allocator_untouched() {
    for (op, source, destination) in [
        (CastOp::IntToPtr, Ty::U64, Ty::Ref(Box::new(Ty::U64))),
        (CastOp::IntToPtr, Ty::U64, Ty::RefMut(Box::new(Ty::U64))),
        (CastOp::IntToPtr, Ty::U32, Ty::Ptr),
        (CastOp::IntToPtr, Ty::U128, Ty::Ptr),
        (CastOp::IntToPtr, Ty::U64, Ty::FatPtr(FatPtrKind::Str)),
        (CastOp::PtrToInt, Ty::FatPtr(FatPtrKind::Str), Ty::U64),
        (CastOp::PtrToInt, Ty::Rc(Box::new(Ty::U64)), Ty::U64),
        (CastOp::PtrToInt, Ty::Ptr, Ty::U32),
        (CastOp::PtrToInt, Ty::Ptr, Ty::U128),
        (CastOp::PtrToInt, Ty::U64, Ty::U64),
        (CastOp::Bitcast, Ty::Ptr, Ty::U64),
    ] {
        let mut module = copy_module(source.clone(), destination.clone());
        let before = serde_json::to_value(&module).unwrap();
        assert!(
            pointer_casts::emit_pointer_integer_cast(
                &mut module.functions[0].blocks[0],
                op,
                source,
                destination,
                ValueId::new(0),
                ValueId::new(1),
                || panic!("invalid request allocated a value")
            )
            .is_err()
        );
        assert_eq!(serde_json::to_value(&module).unwrap(), before);
    }
}

#[test]
fn actual_frontend_pointer_casts_validate_without_inventing_pointee_layouts() {
    let fixtures =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/pointer_casts");
    for name in [
        "cast_int_to_const",
        "cast_int_to_mut",
        "cast_raw_to_int",
        "cast_raw_to_raw",
        "cast_ref_scalar",
        "cast_refmut_scalar",
        "cast_ref_ordered",
        "cast_ref_reordered",
        "cast_nominal_reinterpret",
    ] {
        for opt in 0..=1 {
            let path = fixtures.join(format!("{name}-O{opt}.trust-ir.json"));
            let mut module: Module = serde_json::from_slice(&std::fs::read(path).unwrap()).unwrap();
            assert!(validate_module(&module).is_empty(), "{name}-O{opt}");
            assert!(module.proof_obligations.is_empty());
            assert!(module.proof_certificates.is_empty());
            assert!(module.tuple_layouts.is_empty());
            let aggregate = matches!(
                name,
                "cast_ref_ordered" | "cast_ref_reordered" | "cast_nominal_reinterpret"
            );
            if aggregate {
                assert_eq!(
                    module.target_info.as_ref().unwrap().struct_passing,
                    trust_ir::StructPassingPolicy::Unclassified
                );
            }
            let mut casts = 0;
            for node in &module.functions[0].blocks[0].body {
                if let Inst::Cast {
                    op, src_ty, dst_ty, ..
                } = &node.inst
                {
                    casts += 1;
                    match op {
                        CastOp::PtrToInt => assert_eq!(src_ty, &Ty::Ptr),
                        CastOp::IntToPtr => assert_eq!(dst_ty, &Ty::Ptr),
                        CastOp::PtrToPtr => {
                            assert!(pointer_casts::can_transport_address(src_ty, dst_ty))
                        }
                        _ => panic!("unexpected cast {op:?}"),
                    }
                }
            }
            assert_eq!(
                casts,
                match name {
                    "cast_raw_to_raw" => 1,
                    "cast_int_to_const" | "cast_int_to_mut" | "cast_raw_to_int" => 2,
                    _ => 3,
                }
            );
            trust_cg_lower::translate_function_with_license(
                &module.functions[0],
                &module,
                &permit_unlicensed(),
            )
            .unwrap();
            let before = serde_json::to_value(&module).unwrap();
            canonicalize_reinterpret_copies(&mut module.functions[0]);
            assert_eq!(serde_json::to_value(&module).unwrap(), before);

            // Reintroducing the original typed-source PtrToInt defect is still
            // refused by the unmodified TrustIR validator.
            if let Some(node) = module.functions[0].blocks[0].body.iter_mut().find(|n| {
                matches!(
                    n.inst,
                    Inst::Cast {
                        op: CastOp::PtrToInt,
                        ..
                    }
                )
            }) {
                let Inst::Cast { src_ty, .. } = &mut node.inst else {
                    unreachable!()
                };
                *src_ty = Ty::PtrConst(Box::new(Ty::U64));
                assert!(!validate_module(&module).is_empty());
            }
        }
    }
}

#[test]
fn original_frontend_address_failure_requires_both_repairs() {
    let mut module: Module = serde_json::from_str(include_str!(
        "fixtures/pointer_casts/before_ref_ordered.trust-ir.json"
    ))
    .unwrap();
    let original = validate_module(&module);
    assert_eq!(original.len(), 2);
    assert!(
        original
            .iter()
            .any(|e| matches!(e, ValidationError::OperandTypeMismatch { op, .. } if op == "copy"))
    );
    canonicalize_reinterpret_copies(&mut module.functions[0]);
    assert_eq!(
        validate_module(&module).len(),
        1,
        "the original typed-source PtrToInt is still invalid"
    );
    let before = module.clone();
    let block = &mut module.functions[0].blocks[0];
    let node = block.body.remove(1);
    let Inst::Cast {
        op,
        src_ty,
        dst_ty,
        operand,
    } = node.inst
    else {
        unreachable!()
    };
    let ret = block.body.pop().unwrap();
    pointer_casts::emit_pointer_integer_cast(
        block,
        op,
        src_ty,
        dst_ty,
        operand,
        node.results[0],
        || ValueId::new(5),
    )
    .unwrap();
    block.body.push(ret);
    assert!(validate_module(&module).is_empty());
    // Every source field except this instruction sequence remains identical.
    let mut comparable = module.clone();
    comparable.functions[0].blocks[0].body = before.functions[0].blocks[0].body.clone();
    assert_eq!(
        serde_json::to_value(&comparable).unwrap(),
        serde_json::to_value(&before).unwrap()
    );
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
