//! Admission regressions for the public TrustIR compatibility adapter.
//! No solver, native execution, or proof authority is involved. The shared
//! two-I64 carrier is intentional; source metadata kinds must be checked before
//! erasure. These local checks are not full source-validity or Core proof admission.

use std::collections::{HashMap, HashSet};

use trust_cg_lower::adapter::{AdapterError, translate_type};
use trust_cg_lower::function::{Function, StackSlotInfo};
use trust_cg_lower::instructions::{Instruction, Opcode, Value};
use trust_cg_lower::types::Type;
use trust_ir::{
    Block, BlockId, FatPtrKind, FuncId, FuncTy, Function as IrFunction, Inst, InstrNode, Module,
    Ty, ValueId,
};
use trust_ir_build::{ValidationError, validate_module};

fn v(id: u32) -> ValueId {
    ValueId::new(id)
}
fn fat(kind: FatPtrKind) -> Ty {
    Ty::FatPtr(kind)
}

fn module(params: Vec<Ty>, returns: Vec<Ty>, body: Vec<InstrNode>) -> Module {
    let mut module = Module::new("pointer_metadata_contract");
    let ty = module
        .add_func_type(FuncTy {
            params: params.clone(),
            returns,
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let entry = BlockId::new(0);
    let mut function = IrFunction::new(FuncId::new(0), "pointer_metadata_contract", ty, entry);
    function.blocks.push(Block {
        id: entry,
        // Deliberately noncanonical source IDs: the LIR formals are positional.
        params: params
            .into_iter()
            .enumerate()
            .map(|(i, ty)| (v(10 + i as u32), ty))
            .collect(),
        body,
    });
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
    module
}

fn parts(kind: FatPtrKind, declared: Ty, data_ty: Ty, actual_meta: Ty) -> Module {
    let ptr_ty = fat(kind);
    module(
        vec![data_ty, actual_meta],
        vec![ptr_ty.clone()],
        vec![
            InstrNode::new(Inst::PtrFromParts {
                ptr_ty,
                metadata_ty: declared,
                data: v(10),
                metadata: v(11),
            })
            .with_result(v(12)),
            InstrNode::new(Inst::Return {
                values: vec![v(12)],
            }),
        ],
    )
}

fn extraction(actual: Ty, declared: Ty, metadata: Option<Ty>) -> Module {
    let result_ty = metadata.clone().unwrap_or(Ty::Ptr);
    let inst = match metadata {
        Some(metadata_ty) => Inst::PtrMetadata {
            ptr_ty: declared,
            metadata_ty,
            ptr: v(10),
        },
        None => Inst::PtrData {
            ptr_ty: declared,
            ptr: v(10),
        },
    };
    module(
        vec![actual],
        vec![result_ty],
        vec![
            InstrNode::new(inst).with_result(v(12)),
            InstrNode::new(Inst::Return {
                values: vec![v(12)],
            }),
        ],
    )
}

fn roundtrip(kind: FatPtrKind, metadata_ty: Ty) -> Module {
    let ptr_ty = fat(kind);
    module(
        vec![Ty::Ptr, metadata_ty.clone()],
        vec![Ty::Ptr, metadata_ty.clone()],
        vec![
            InstrNode::new(Inst::PtrFromParts {
                ptr_ty: ptr_ty.clone(),
                metadata_ty: metadata_ty.clone(),
                data: v(10),
                metadata: v(11),
            })
            .with_result(v(12)),
            InstrNode::new(Inst::PtrData {
                ptr_ty: ptr_ty.clone(),
                ptr: v(12),
            })
            .with_result(v(13)),
            InstrNode::new(Inst::PtrMetadata {
                ptr_ty,
                metadata_ty,
                ptr: v(12),
            })
            .with_result(v(14)),
            InstrNode::new(Inst::Return {
                values: vec![v(13), v(14)],
            }),
        ],
    )
}

fn routes(module: &Module) -> Vec<(&'static str, Result<Function, AdapterError>)> {
    let function = &module.functions[0];
    vec![
        (
            "function",
            trust_cg_lower::translate_function_with_license(function, module, &permit_unlicensed())
                .map(|(function, _)| function),
        ),
        (
            "function_with_names",
            trust_cg_lower::translate_function_with_names_and_license(
                function,
                module,
                &HashMap::new(),
                &permit_unlicensed(),
            )
            .map(|(function, _)| function),
        ),
        (
            "module",
            permit_translate_module(module).map(|mut functions| {
                assert_eq!(functions.len(), 1);
                functions.remove(0).0
            }),
        ),
    ]
}

fn inst(opcode: Opcode, args: &[Value], results: &[Value]) -> Instruction {
    Instruction {
        opcode,
        args: args.to_vec(),
        results: results.to_vec(),
    }
}

fn assert_roundtrip_lir(function: &Function) {
    let pair = Type::Struct(vec![Type::I64, Type::I64]);
    assert_eq!(function.signature.params, vec![Type::I64, Type::I64]);
    assert_eq!(function.signature.returns, vec![Type::I64, Type::I64]);
    assert_eq!(function.stack_slots, vec![StackSlotInfo::new(16, 8)]);
    assert_eq!(function.blocks.len(), 1);
    let entry = &function.blocks[&function.entry_block];
    assert_eq!(
        entry.params,
        vec![(Value(0), Type::I64), (Value(1), Type::I64)]
    );
    let instructions = &entry.instructions;
    assert_eq!(instructions.len(), 9);
    let result = |index: usize| match instructions[index].results.as_slice() {
        [value] => *value,
        other => panic!("instruction {index}: expected one result, got {other:?}"),
    };
    // Temporary IDs may vary, but every actual def/use and both lane choices
    // must match the independent two-word construction/extraction contract.
    let (aggregate, metadata_ptr, data_ptr, data, extracted_meta_ptr, metadata) = (
        result(0),
        result(2),
        result(4),
        result(5),
        result(6),
        result(7),
    );
    let temporaries = [
        aggregate,
        metadata_ptr,
        data_ptr,
        data,
        extracted_meta_ptr,
        metadata,
    ];
    assert_eq!(temporaries.into_iter().collect::<HashSet<_>>().len(), 6);
    assert!(
        temporaries
            .iter()
            .all(|value| ![Value(0), Value(1)].contains(value))
    );
    let store = Opcode::Store {
        ty: Type::I64,
        align: None,
    };
    let load = Opcode::Load {
        ty: Type::I64,
        align: None,
    };
    assert_eq!(
        *instructions,
        vec![
            inst(Opcode::StackAddr { slot: 0 }, &[], &[aggregate]),
            inst(store.clone(), &[Value(0), aggregate], &[]),
            inst(
                Opcode::StructGep {
                    struct_ty: pair.clone(),
                    field_index: 1
                },
                &[aggregate],
                &[metadata_ptr]
            ),
            inst(store, &[Value(1), metadata_ptr], &[]),
            inst(
                Opcode::StructGep {
                    struct_ty: pair.clone(),
                    field_index: 0
                },
                &[aggregate],
                &[data_ptr]
            ),
            inst(load.clone(), &[data_ptr], &[data]),
            inst(
                Opcode::StructGep {
                    struct_ty: pair.clone(),
                    field_index: 1
                },
                &[aggregate],
                &[extracted_meta_ptr]
            ),
            inst(load, &[extracted_meta_ptr], &[metadata]),
            inst(Opcode::Return, &[data, metadata], &[]),
        ]
    );
    assert_eq!(function.value_types.get(&aggregate), Some(&pair));
    for value in [metadata_ptr, data_ptr, data, extracted_meta_ptr, metadata] {
        assert_eq!(function.value_types.get(&value), Some(&Type::I64));
    }
}

#[derive(Clone, Copy, Debug)]
enum Cause {
    Metadata(&'static str),
    Operand(&'static str, &'static str),
    Missing(u32),
}

fn source_context(op: &str) -> &'static str {
    match op {
        "ptr_data" => "PtrData",
        "ptr_metadata" => "PtrMetadata",
        "ptr_from_parts" => "PtrFromParts",
        _ => panic!("unknown fixture operation {op}"),
    }
}

fn correct_local_diagnostic(cause: Cause, message: &str) -> bool {
    match cause {
        Cause::Metadata(op) => {
            message.contains(&format!("{} metadata type mismatch", source_context(op)))
        }
        Cause::Operand(op, role) => {
            message.contains(&format!("{} {role} type mismatch", source_context(op)))
        }
        Cause::Missing(_) => false,
    }
}

fn refusal(label: &str, module: &Module, cause: Cause, failures: &mut Vec<String>) {
    let errors = validate_module(module);
    assert!(
        errors.iter().any(|error| match (cause, error) {
            (Cause::Metadata(want), ValidationError::PointerMetadataTypeMismatch { op, .. }) =>
                op == want,
            (
                Cause::Operand(want_op, want_role),
                ValidationError::OperandTypeMismatch { op, role, .. },
            ) => op == want_op && role == want_role,
            (Cause::Missing(want), ValidationError::UseBeforeDef { value, .. }) => *value == want,
            _ => false,
        }),
        "{label}: fixture must have the intended upstream type error {cause:?}, got {errors:?}"
    );
    for (route, result) in routes(module) {
        match result {
            Err(AdapterError::UnknownValue(actual)) if matches!(cause, Cause::Missing(want) if want == actual) =>
                {}
            Err(AdapterError::UnsupportedInstruction(message))
                if correct_local_diagnostic(cause, &message) => {}
            Err(other) => failures.push(format!("{label}/{route}: wrong refusal {other:?}")),
            Ok(function) => {
                failures.push(format!("{label}/{route}: wrongly admitted {function:?}"))
            }
        }
    }
}

#[test]
fn container_pointer_metadata_valid_source_contract_and_exact_lir() {
    // Literal expectations, not values obtained from the adapter under test.
    for (kind, metadata) in [
        (FatPtrKind::ContainerVtable, Ty::Ptr),
        (FatPtrKind::ContainerLen, Ty::U64),
        (FatPtrKind::TraitObject { trait_id: 7 }, Ty::Ptr),
    ] {
        assert_eq!(fat(kind).pointer_metadata_ty(64), Some(metadata.clone()));
        assert_eq!(
            translate_type(&fat(kind)).unwrap(),
            Type::Struct(vec![Type::I64, Type::I64])
        );
        let module = roundtrip(kind, metadata);
        assert!(validate_module(&module).is_empty());
        for (route, result) in routes(&module) {
            let function = result.unwrap_or_else(|error| panic!("{route}: {error:?}"));
            assert_roundtrip_lir(&function);
        }
    }
}

#[test]
fn container_pointer_metadata_from_parts_rejects_declared_and_actual_confusion() {
    let mut failures = Vec::new();
    for (label, kind, declared, actual, cause) in [
        (
            "vtable_length_declaration",
            FatPtrKind::ContainerVtable,
            Ty::U64,
            Ty::U64,
            Cause::Metadata("ptr_from_parts"),
        ),
        (
            "vtable_integer_actual",
            FatPtrKind::ContainerVtable,
            Ty::Ptr,
            Ty::U64,
            Cause::Operand("ptr_from_parts", "metadata"),
        ),
        (
            "length_pointer_declaration",
            FatPtrKind::ContainerLen,
            Ty::Ptr,
            Ty::Ptr,
            Cause::Metadata("ptr_from_parts"),
        ),
        (
            "length_pointer_actual",
            FatPtrKind::ContainerLen,
            Ty::U64,
            Ty::Ptr,
            Cause::Operand("ptr_from_parts", "metadata"),
        ),
    ] {
        refusal(
            label,
            &parts(kind, declared, Ty::Ptr, actual),
            cause,
            &mut failures,
        );
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

#[test]
fn container_pointer_metadata_extraction_rejects_result_type_confusion() {
    let mut failures = Vec::new();
    for (kind, wrong) in [
        (FatPtrKind::ContainerVtable, Ty::U64),
        (FatPtrKind::ContainerLen, Ty::Ptr),
    ] {
        let ty = fat(kind);
        let module = extraction(ty.clone(), ty, Some(wrong));
        refusal(
            "wrong_metadata_result",
            &module,
            Cause::Metadata("ptr_metadata"),
            &mut failures,
        );
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

#[test]
fn container_pointer_metadata_from_parts_requires_actual_data_pointer() {
    let mut failures = Vec::new();
    for (kind, metadata) in [
        (FatPtrKind::ContainerVtable, Ty::Ptr),
        (FatPtrKind::ContainerLen, Ty::U64),
    ] {
        let module = parts(kind, metadata.clone(), Ty::U64, metadata);
        refusal(
            "integer_data",
            &module,
            Cause::Operand("ptr_from_parts", "data"),
            &mut failures,
        );
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

#[test]
fn container_pointer_metadata_extraction_requires_exact_actual_pointer_kind() {
    let mut failures = Vec::new();
    for (actual, declared, metadata) in [
        (
            FatPtrKind::ContainerLen,
            FatPtrKind::ContainerVtable,
            Ty::Ptr,
        ),
        (
            FatPtrKind::ContainerVtable,
            FatPtrKind::ContainerLen,
            Ty::U64,
        ),
    ] {
        let module = extraction(fat(actual), fat(declared), None);
        refusal(
            "wrong_data_kind",
            &module,
            Cause::Operand("ptr_data", "ptr"),
            &mut failures,
        );
        let module = extraction(fat(actual), fat(declared), Some(metadata));
        refusal(
            "wrong_metadata_kind",
            &module,
            Cause::Operand("ptr_metadata", "ptr"),
            &mut failures,
        );
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

#[test]
fn container_pointer_metadata_missing_operands_are_unknown_not_inferred() {
    let mut failures = Vec::new();
    for missing_data in [true, false] {
        let mut module = parts(FatPtrKind::ContainerVtable, Ty::Ptr, Ty::Ptr, Ty::Ptr);
        match &mut module.functions[0].blocks[0].body[0].inst {
            Inst::PtrFromParts { data, metadata, .. } => {
                if missing_data {
                    *data = v(99);
                } else {
                    *metadata = v(99);
                }
            }
            _ => unreachable!(),
        }
        refusal(
            "missing_parts_operand",
            &module,
            Cause::Missing(99),
            &mut failures,
        );
    }
    for metadata in [None, Some(Ty::Ptr)] {
        let ty = fat(FatPtrKind::ContainerVtable);
        let mut module = extraction(ty.clone(), ty, metadata);
        match &mut module.functions[0].blocks[0].body[0].inst {
            Inst::PtrData { ptr, .. } | Inst::PtrMetadata { ptr, .. } => *ptr = v(99),
            _ => unreachable!(),
        }
        refusal(
            "missing_extraction_operand",
            &module,
            Cause::Missing(99),
            &mut failures,
        );
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

fn thin_pointer_roundtrip(target: Ty) -> Module {
    module(
        vec![Ty::Ptr],
        vec![Ty::Ptr, Ty::Unit],
        vec![
            // A genuine Unit SSA definition, without any Undef or unsupported
            // PhantomData constant. The machine representation has no Unit lane.
            InstrNode::new(Inst::PtrMetadata {
                ptr_ty: Ty::Ptr,
                metadata_ty: Ty::Unit,
                ptr: v(10),
            })
            .with_result(v(11)),
            InstrNode::new(Inst::PtrFromParts {
                ptr_ty: target.clone(),
                metadata_ty: Ty::Unit,
                data: v(10),
                metadata: v(11),
            })
            .with_result(v(12)),
            InstrNode::new(Inst::PtrData {
                ptr_ty: target.clone(),
                ptr: v(12),
            })
            .with_result(v(13)),
            InstrNode::new(Inst::PtrMetadata {
                ptr_ty: target,
                metadata_ty: Ty::Unit,
                ptr: v(12),
            })
            .with_result(v(14)),
            InstrNode::new(Inst::Return {
                values: vec![v(13), v(14)],
            }),
        ],
    )
}

#[test]
fn container_pointer_metadata_thin_ptr_and_ref_keep_unit_ssa_but_erase_its_lir() {
    for target in [Ty::Ptr, Ty::Ref(Box::new(Ty::I64))] {
        let module = thin_pointer_roundtrip(target);
        let errors = validate_module(&module);
        assert!(errors.is_empty(), "canonical thin fixture: {errors:?}");
        for (route, result) in routes(&module) {
            let function = result.unwrap_or_else(|error| panic!("{route}: {error:?}"));
            assert_eq!(function.signature.params, vec![Type::I64]);
            assert_eq!(function.signature.returns, vec![Type::I64]);
            assert!(function.stack_slots.is_empty());
            assert_eq!(function.blocks.len(), 1);
            let entry = &function.blocks[&function.entry_block];
            assert_eq!(entry.params, vec![(Value(0), Type::I64)]);
            assert_eq!(entry.instructions.len(), 3);
            let [rebuilt] = entry.instructions[0].results.as_slice() else {
                panic!("expected one rebuilt pointer");
            };
            let [data] = entry.instructions[1].results.as_slice() else {
                panic!("expected one data pointer");
            };
            assert_eq!(
                [Value(0), *rebuilt, *data]
                    .into_iter()
                    .collect::<HashSet<_>>()
                    .len(),
                3
            );
            assert_eq!(
                entry.instructions,
                vec![
                    inst(Opcode::Copy, &[Value(0)], &[*rebuilt]),
                    inst(Opcode::Copy, &[*rebuilt], &[*data]),
                    inst(Opcode::Return, &[*data], &[]),
                ]
            );
            assert_eq!(function.value_types.get(rebuilt), Some(&Type::I64));
            assert_eq!(function.value_types.get(data), Some(&Type::I64));
            assert!(function.value_types.values().all(|ty| *ty == Type::I64));
        }
    }
}

#[test]
fn container_pointer_metadata_unit_paths_still_check_actual_and_missing_operands() {
    let mut failures = Vec::new();
    for (metadata, cause) in [
        (v(11), Cause::Operand("ptr_from_parts", "metadata")),
        (v(99), Cause::Missing(99)),
    ] {
        let module = module(
            vec![Ty::Ptr, Ty::U64],
            vec![Ty::Ptr],
            vec![
                InstrNode::new(Inst::PtrMetadata {
                    ptr_ty: Ty::Ptr,
                    metadata_ty: Ty::Unit,
                    ptr: v(10),
                })
                .with_result(v(12)),
                InstrNode::new(Inst::PtrFromParts {
                    ptr_ty: Ty::Ptr,
                    metadata_ty: Ty::Unit,
                    data: v(10),
                    metadata,
                })
                .with_result(v(13)),
                InstrNode::new(Inst::Return {
                    values: vec![v(13)],
                }),
            ],
        );
        refusal("bad_unit_metadata", &module, cause, &mut failures);
    }
    let wrong_ptr = extraction(Ty::U64, Ty::Ptr, Some(Ty::Unit));
    refusal(
        "unit_metadata_integer_pointer",
        &wrong_ptr,
        Cause::Operand("ptr_metadata", "ptr"),
        &mut failures,
    );
    let mut missing_ptr = extraction(Ty::Ptr, Ty::Ptr, Some(Ty::Unit));
    let Inst::PtrMetadata { ptr, .. } = &mut missing_ptr.functions[0].blocks[0].body[0].inst else {
        unreachable!();
    };
    *ptr = v(99);
    refusal(
        "unit_metadata_missing_pointer",
        &missing_ptr,
        Cause::Missing(99),
        &mut failures,
    );
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

#[test]
fn container_pointer_metadata_body_only_rc_cannot_bypass_ownership_refusal() {
    // No Rc function signature or parameter can reject before the body check.
    // Upstream shape validity is necessary but does not model a CG Rc ABI.
    let module = thin_pointer_roundtrip(Ty::Rc(Box::new(Ty::I64)));
    let errors = validate_module(&module);
    assert!(
        errors.is_empty(),
        "Rc source fixture must be well-typed: {errors:?}"
    );
    let mut failures = Vec::new();
    for (route, result) in routes(&module) {
        match result {
            Err(AdapterError::UnsupportedType(message))
                if message.contains("Ty::Rc") && message.contains("refcount ownership") => {}
            Err(other) => failures.push(format!("{route}: wrong Rc refusal {other:?}")),
            Ok(_) => failures.push(format!("{route}: body-only Rc was incorrectly admitted")),
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

#[test]
fn container_pointer_metadata_body_only_closure_is_not_a_pointer_kind() {
    // A real closure definition prevents a missing table from masquerading as
    // the desired pointer-operation refusal. The signature remains ordinary Ptr.
    let mut module = thin_pointer_roundtrip(Ty::Closure(trust_ir::ClosureTyId::new(0)));
    module.closure_types.push(trust_ir::ClosureTy {
        func: module.functions[0].ty,
        captures: vec![Ty::Ptr],
    });
    let errors = validate_module(&module);
    assert!(
        errors.iter().any(|error| matches!(error,
            ValidationError::PointerOpInvalid { op, .. } if op == "ptr_from_parts"
        )),
        "Closure fixture must violate pointer-operation typing: {errors:?}"
    );
    let mut failures = Vec::new();
    for (route, result) in routes(&module) {
        match result {
            Err(AdapterError::UnsupportedInstruction(message))
                if message.contains("PtrFromParts")
                    && message.contains("pointer")
                    && message.contains("Closure") => {}
            Err(other) => failures.push(format!("{route}: wrong Closure refusal {other:?}")),
            Ok(_) => failures.push(format!(
                "{route}: body-only Closure was incorrectly admitted"
            )),
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

fn pointer_arity_cases() -> Vec<(&'static str, &'static str, Module, Vec<Opcode>)> {
    let pair = Type::Struct(vec![Type::I64, Type::I64]);
    let pointer = fat(FatPtrKind::ContainerVtable);
    let load = Opcode::Load {
        ty: Type::I64,
        align: None,
    };
    let store = Opcode::Store {
        ty: Type::I64,
        align: None,
    };
    [
        (
            "fat_data",
            "ptr_data",
            vec![pointer.clone()],
            Inst::PtrData {
                ptr_ty: pointer.clone(),
                ptr: v(10),
            },
            vec![
                Opcode::StructGep {
                    struct_ty: pair.clone(),
                    field_index: 0,
                },
                load.clone(),
                Opcode::Return,
            ],
        ),
        (
            "fat_metadata",
            "ptr_metadata",
            vec![pointer.clone()],
            Inst::PtrMetadata {
                ptr_ty: pointer.clone(),
                metadata_ty: Ty::Ptr,
                ptr: v(10),
            },
            vec![
                Opcode::StructGep {
                    struct_ty: pair.clone(),
                    field_index: 1,
                },
                load,
                Opcode::Return,
            ],
        ),
        (
            "fat_parts",
            "ptr_from_parts",
            vec![Ty::Ptr, Ty::Ptr],
            Inst::PtrFromParts {
                ptr_ty: pointer,
                metadata_ty: Ty::Ptr,
                data: v(10),
                metadata: v(11),
            },
            vec![
                Opcode::StackAddr { slot: 0 },
                store.clone(),
                Opcode::StructGep {
                    struct_ty: pair,
                    field_index: 1,
                },
                store,
                Opcode::Return,
            ],
        ),
        (
            "thin_unit_metadata",
            "ptr_metadata",
            vec![Ty::Ptr],
            Inst::PtrMetadata {
                ptr_ty: Ty::Ptr,
                metadata_ty: Ty::Unit,
                ptr: v(10),
            },
            vec![Opcode::Return],
        ),
    ]
    .into_iter()
    .map(|(label, op, params, operation, expected)| {
        // The pointer result is deliberately unused, including in the return.
        // Removing it cannot manufacture an unrelated undefined return value.
        let module = module(
            params,
            vec![],
            vec![
                InstrNode::new(operation).with_result(v(12)),
                InstrNode::new(Inst::Return { values: vec![] }),
            ],
        );
        (label, op, module, expected)
    })
    .collect()
}

#[test]
fn container_pointer_metadata_single_result_dead_operations_are_valid() {
    for (label, _, module, expected) in pointer_arity_cases() {
        assert_eq!(module.functions[0].blocks[0].body[0].results, vec![v(12)]);
        let errors = validate_module(&module);
        assert!(
            errors.is_empty(),
            "{label}: canonical source errors {errors:?}"
        );
        for (route, result) in routes(&module) {
            let function = result.unwrap_or_else(|error| panic!("{label}/{route}: {error:?}"));
            assert!(function.signature.returns.is_empty());
            assert_eq!(function.blocks.len(), 1);
            let instructions = &function.blocks[&function.entry_block].instructions;
            assert_eq!(
                instructions
                    .iter()
                    .map(|instruction| instruction.opcode.clone())
                    .collect::<Vec<_>>(),
                expected,
                "{label}/{route}: exact dead-operation lowering"
            );
            let returned = instructions.last().expect("ordinary return");
            assert!(returned.args.is_empty() && returned.results.is_empty());
        }
    }
}

#[test]
fn container_pointer_metadata_zero_and_two_results_are_rejected_including_unit() {
    let mut failures = Vec::new();
    for (label, op, canonical, _) in pointer_arity_cases() {
        let canonical_errors = validate_module(&canonical);
        assert!(
            canonical_errors.is_empty(),
            "{label}: canonical source errors {canonical_errors:?}"
        );
        for actual in [0usize, 2] {
            let mut malformed = canonical.clone();
            malformed.functions[0].blocks[0].body[0].results =
                (0..actual).map(|index| v(12 + index as u32)).collect();
            let errors = validate_module(&malformed);
            assert!(
                matches!(errors.as_slice(),
                    [ValidationError::InstrResultArityMismatch {
                        block: 0, op: found_op, expected: 1, actual: found_actual,
                    }] if found_op == op && *found_actual == actual
                ),
                "{label}/{actual}: expected only the exact arity defect, got {errors:?}"
            );
            let expected = format!(
                "{} result arity mismatch: got {actual}, expected 1",
                source_context(op)
            );
            for (route, result) in routes(&malformed) {
                match result {
                    Err(AdapterError::UnsupportedInstruction(message)) if message == expected => {}
                    Err(other) => {
                        failures.push(format!("{label}/{actual}/{route}: wrong refusal {other:?}"))
                    }
                    Ok(_) => failures.push(format!(
                        "{label}/{actual}/{route}: malformed result arity admitted"
                    )),
                }
            }
        }
    }
    // Every malformed public route is attempted, even if an earlier one was
    // admitted or gave an unrelated error. Panics do not count as refusal.
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}

/// `translate_module` under [`permit_unlicensed`].
fn permit_translate_module(
    module: &trust_ir::Module,
) -> Result<
    Vec<(trust_cg_lower::Function, trust_cg_lower::ProofContext)>,
    trust_cg_lower::AdapterError,
> {
    trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        module,
        trust_cg_lower::GuardCarrierArch::default(),
        trust_cg_lower::TlsDialect::default(),
        &permit_unlicensed(),
    )
}
