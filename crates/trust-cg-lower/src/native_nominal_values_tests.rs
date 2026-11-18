// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Actual semantic transport and adapter controls. Fixture ABI records are
//! untrusted input; explicit test-only body permission grants no proof grade.

use super::*;
use crate::instructions::Opcode;
use crate::{
    CodegenLicensePolicy, GuardCarrierArch, ObjectAccessModel, ObjectSymbolPolicy,
    UnlicensedBodyPolicy,
};
use trust_ir::{Block, CallingConv};

use crate::native_scalar_c_abi::test_fixture as scalar_fixture;

fn native() -> NativeAbiContext {
    NativeAbiContext::aarch64("aarch64-apple-darwin".into()).unwrap()
}

fn fixture() -> Module {
    let mut module = scalar_fixture::fixture(
        "aarch64-apple-darwin",
        vec![Ty::U64],
        vec![Ty::U64],
        Some(Ty::U64),
        false,
    );
    let abi = module.func_types[0].abi.as_mut().unwrap();
    abi.convention = "Rust".into();
    abi.lowered_convention = CallingConv::Rust;
    abi.source_abi = "Rust".into();
    module.functions[0].calling_conv = CallingConv::Rust;
    let mut entry = Block::new(BlockId::new(0));
    entry.params = vec![(ValueId::new(0), Ty::U64)];
    entry.body = vec![InstrNode::new(Inst::Return {
        values: vec![ValueId::new(0)],
    })];
    module.functions[0].blocks = vec![entry];
    module.functions[1].calling_conv = CallingConv::Rust;
    module.functions[1].ty = module.functions[0].ty;
    let target = module.functions[0].id;
    let signature = module.functions[0].ty;
    module.functions[1].blocks[0].body = vec![
        InstrNode::new(Inst::Const {
            ty: Ty::FnItem(target),
            value: Constant::FnItem(target),
        })
        .with_result(ValueId::new(10)),
        InstrNode::new(Inst::Copy {
            ty: Ty::FnItem(target),
            operand: ValueId::new(10),
        })
        .with_result(ValueId::new(11)),
        InstrNode::new(Inst::CallIndirect {
            callee: ValueId::new(11),
            sig: signature,
            args: vec![ValueId::new(0)],
            calling_conv: CallingConv::Rust,
        })
        .with_result(ValueId::new(1)),
        InstrNode::new(Inst::Return {
            values: vec![ValueId::new(1)],
        }),
    ];
    module
}

fn lower(module: &Module) -> Vec<(crate::Function, crate::ProofContext)> {
    let policy = CodegenLicensePolicy::default().with_unlicensed(UnlicensedBodyPolicy::Permit);
    let admitted = crate::admit_module(module, &policy, &[]).unwrap();
    crate::translate_admitted_module_for_native_scalar_c_abi(
        &admitted,
        GuardCarrierArch::AArch64,
        ObjectAccessModel::macho_dyld(),
        ObjectSymbolPolicy::default(),
        &native(),
    )
    .unwrap()
    .0
}

#[test]
fn a_nominal_box_pointee_keeps_its_separate_checked_pointer_protocol() {
    use trust_ir::box_validity::{
        BoxDerefSite, BoxFactSession, BoxPointee, BoxValidityFact, PremiseRoot,
    };
    let mut module = fixture();
    let target = module.functions[0].id;
    // Box rule 2 requires an actual nonzero region. The nominal field has no
    // bytes; the word gives this pointee its independently checked region.
    let pointee = module.add_struct(trust_ir::StructDef {
        id: trust_ir::StructId::new(0),
        name: "NominalBoxPointee".into(),
        fields: vec![
            trust_ir::FieldDef {
                name: "nominal".into(),
                ty: Ty::FnItem(target),
                offset: Some(0),
            },
            trust_ir::FieldDef {
                name: "word".into(),
                ty: Ty::U64,
                offset: Some(0),
            },
        ],
        size: Some(8),
        align: Some(8),
        repr: trust_ir::StructRepr::C,
        origin: None,
    });
    let pointer = module
        .add_func_type(trust_ir::FuncTy::unrecorded(
            vec![Ty::Ptr],
            vec![Ty::Ptr],
            false,
        ))
        .unwrap();
    let caller = &mut module.functions[1];
    caller.ty = pointer;
    caller.blocks[0].params = vec![(ValueId::new(0), Ty::Ptr)];
    caller.blocks[0].body = vec![
        InstrNode::new(Inst::BoxDeref {
            ptr_ty: Ty::Ptr,
            pointee: BoxPointee::Sized {
                ty: Ty::Struct(pointee),
            },
            operand: ValueId::new(0),
            fact: Box::new(BoxValidityFact::premise(
                BoxDerefSite {
                    item: [4; 16],
                    ordinal: 0,
                },
                BoxFactSession::PROOF_SNAPSHOT,
                PremiseRoot::ParamByValue,
            )),
        })
        .with_result(ValueId::new(1)),
        InstrNode::new(Inst::Return {
            values: vec![ValueId::new(1)],
        }),
    ];
    let errors = trust_ir_build::validate_module(&module);
    assert!(errors.is_empty(), "{errors:#?}");
    let mut zero_sized = module.clone();
    let Inst::BoxDeref { pointee, .. } = &mut zero_sized.functions[1].blocks[0].body[0].inst else {
        unreachable!();
    };
    *pointee = BoxPointee::Sized {
        ty: Ty::FnItem(target),
    };
    assert!(
        trust_ir_build::validate_module(&zero_sized)
            .iter()
            .any(|error| matches!(
                error,
                trust_ir_build::ValidationError::BoxDerefPointeeOutOfScope { .. }
            ))
    );
    let before = module.clone();
    assert!(ModuleValues::native(&module, &native()).unwrap().is_empty());
    let default = CodegenLicensePolicy::default().with_unlicensed(UnlicensedBodyPolicy::Permit);
    assert!(crate::admit_module(&module, &default, &[]).is_err());
    let disclosure = crate::box_deref::BoxDerefDisclosure::default();
    let diagnostic = default.with_named_premise_box_floor(&disclosure);
    let admitted = crate::admit_module(&module, &diagnostic, &[]).unwrap();
    crate::translate_admitted_module_for_native_scalar_c_abi(
        &admitted,
        GuardCarrierArch::AArch64,
        ObjectAccessModel::macho_dyld(),
        ObjectSymbolPolicy::default(),
        &native(),
    )
    .unwrap();
    assert!(!disclosure.records().is_empty());
    assert_eq!(module, before);
}

#[test]
fn nominal_identity_is_held_without_allocating_a_machine_value() {
    let module = fixture();
    let caller = &module.functions[1];
    let values = ModuleValues::native(&module, &native()).unwrap();
    assert_eq!(
        values.target(caller.id, ValueId::new(10)),
        Some(module.functions[0].id)
    );
    assert_eq!(
        values.target(caller.id, ValueId::new(11)),
        Some(module.functions[0].id)
    );
    let node = &caller.blocks[0].body[0];
    assert_eq!(
        values.action(caller, caller.entry, 0, node).unwrap(),
        Some(Action::Value {
            target: module.functions[0].id
        })
    );
    assert!(
        values
            .action(caller, caller.entry, 0, &node.clone())
            .is_err(),
        "an equal detached node is not the actual source operation"
    );
    let before = module.clone();
    let lowered = lower(&module);
    assert_eq!(
        module, before,
        "source typing, targets and evidence stay exact"
    );
    let instructions = &lowered[1].0.blocks.values().next().unwrap().instructions;
    assert_eq!(instructions.len(), 2);
    assert!(
        matches!(&instructions[0].opcode, Opcode::Call { name, .. } if name == "foreign_scalar")
    );
    assert!(matches!(instructions[1].opcode, Opcode::Return));
    // Compare actual complete instruction values with the canonical direct
    // call. Singleton constants/copies add no integer, address, Copy or slot.
    let mut direct = fixture();
    direct.functions[1].blocks[0].body = vec![
        InstrNode::new(Inst::Call {
            callee: direct.functions[0].id,
            args: vec![ValueId::new(0)],
        })
        .with_result(ValueId::new(1)),
        InstrNode::new(Inst::Return {
            values: vec![ValueId::new(1)],
        }),
    ];
    let direct = lower(&direct);
    assert_eq!(
        instructions,
        &direct[1].0.blocks.values().next().unwrap().instructions
    );
}

#[test]
fn only_reification_materializes_the_actual_function_address() {
    let mut module = fixture();
    let signature = module.functions[0].ty;
    let entry = &mut module.functions[1].blocks[0];
    entry.body.insert(
        2,
        InstrNode::new(Inst::Cast {
            op: CastOp::ReifyFnPointer,
            src_ty: Ty::FnItem(FuncId::new(0)),
            dst_ty: Ty::Func(signature),
            operand: ValueId::new(11),
        })
        .with_result(ValueId::new(12)),
    );
    if let Inst::CallIndirect { callee, .. } = &mut entry.body[3].inst {
        *callee = ValueId::new(12);
    }
    let before = module.clone();
    let lowered = lower(&module);
    assert_eq!(module, before);
    let instructions = &lowered[1].0.blocks.values().next().unwrap().instructions;
    let addresses = instructions
        .iter()
        .filter(|instruction| {
            matches!(
        &instruction.opcode,
        Opcode::FunctionAddr { name, .. } | Opcode::GlobalRef { name } | Opcode::ExternRef { name }
            if name == "foreign_scalar")
        })
        .count();
    assert_eq!(addresses, 1);
    assert!(
        instructions
            .iter()
            .any(|instruction| matches!(instruction.opcode, Opcode::CallIndirect))
    );
}

#[test]
fn targets_types_definitions_dominance_and_abi_edges_fail_closed() {
    for poison in 0..9 {
        let mut module = fixture();
        match poison {
            0 => {
                if let Inst::Const { value, .. } = &mut module.functions[1].blocks[0].body[0].inst {
                    *value = Constant::FnItem(FuncId::new(1));
                }
            }
            1 => module.functions.push(module.functions[0].clone()),
            2 => {
                if let Inst::Copy { ty, .. } = &mut module.functions[1].blocks[0].body[1].inst {
                    *ty = Ty::Unit;
                }
            }
            3 => module.functions[1].blocks[0].body.swap(0, 1),
            4 => module.functions[1].blocks[0].body[1].results = vec![ValueId::new(10)],
            5 => {
                if let Inst::CallIndirect { calling_conv, .. } =
                    &mut module.functions[1].blocks[0].body[2].inst
                {
                    *calling_conv = CallingConv::C;
                }
            }
            6 => {
                if let Inst::CallIndirect { sig, .. } =
                    &mut module.functions[1].blocks[0].body[2].inst
                {
                    *sig = FuncTyId::new(1);
                }
            }
            7 => {
                if let Inst::CallIndirect { args, .. } =
                    &mut module.functions[1].blocks[0].body[2].inst
                {
                    args.clear();
                }
            }
            8 => module.functions[1].blocks[0].body[0]
                .proofs
                .push(trust_ir::ProofAnnotation::Pure),
            _ => unreachable!(),
        }
        assert!(
            ModuleValues::native(&module, &native()).is_err(),
            "poison {poison}"
        );
    }
}

fn private_slot() -> Module {
    let mut module = fixture();
    let entry = &mut module.functions[1].blocks[0];
    entry.body.splice(
        2..2,
        [
            InstrNode::new(Inst::Alloca {
                ty: Ty::FnItem(FuncId::new(0)),
                count: None,
                align: Some(1),
            })
            .with_result(ValueId::new(20)),
            InstrNode::new(Inst::Store {
                ty: Ty::FnItem(FuncId::new(0)),
                ptr: ValueId::new(20),
                value: ValueId::new(11),
                volatile: false,
                align: Some(1),
            }),
            InstrNode::new(Inst::Load {
                ty: Ty::FnItem(FuncId::new(0)),
                ptr: ValueId::new(20),
                volatile: false,
                align: Some(1),
            })
            .with_result(ValueId::new(12)),
        ],
    );
    let Inst::CallIndirect { callee, .. } = &mut entry.body[5].inst else {
        unreachable!()
    };
    *callee = ValueId::new(12);
    module
}

#[test]
fn closed_initialized_private_nominal_object_needs_no_machine_address_or_slot() {
    let module = private_slot();
    let before = module.clone();
    let caller = &module.functions[1];
    let values = ModuleValues::native(&module, &native()).unwrap();
    assert!(values.is_semantic_value(caller.id, ValueId::new(20)));
    assert_eq!(
        values.target(caller.id, ValueId::new(12)),
        Some(FuncId::new(0))
    );
    for instruction in [2, 3] {
        assert_eq!(
            values
                .action(
                    caller,
                    caller.entry,
                    instruction,
                    &caller.blocks[0].body[instruction]
                )
                .unwrap(),
            Some(Action::PrivateMemory)
        );
    }
    let projected = lower(&module);
    let canonical = lower(&fixture());
    assert_eq!(
        projected[1].0.blocks.values().next().unwrap().instructions,
        canonical[1].0.blocks.values().next().unwrap().instructions
    );
    assert_eq!(
        module, before,
        "actual source provenance, stores and initialization subjects remain held"
    );
}

#[test]
fn private_nominal_memory_requires_complete_provenance_lifetime_initialization_and_nonvolatile_uses()
 {
    for poison in 0..13 {
        let mut module = private_slot();
        let entry = &mut module.functions[1].blocks[0];
        match poison {
            0 => entry.body.swap(3, 4),
            1 => {
                entry.body.remove(3);
            }
            2 => {
                if let Inst::Store { volatile, .. } = &mut entry.body[3].inst {
                    *volatile = true;
                }
            }
            3 => {
                if let Inst::Load { volatile, .. } = &mut entry.body[4].inst {
                    *volatile = true;
                }
            }
            4 => {
                if let Inst::Load { align, .. } = &mut entry.body[4].inst {
                    *align = Some(2);
                }
            }
            5 => {
                if let Inst::Alloca { count, .. } = &mut entry.body[2].inst {
                    *count = Some(ValueId::new(0));
                }
            }
            6 => {
                if let Inst::Alloca { align, .. } = &mut entry.body[2].inst {
                    *align = Some(2);
                }
            }
            7 => {
                if let Inst::Store { ty, .. } = &mut entry.body[3].inst {
                    *ty = Ty::FnItem(FuncId::new(1));
                }
            }
            8 => entry.body.insert(
                3,
                InstrNode::new(Inst::Copy {
                    ty: Ty::Ptr,
                    operand: ValueId::new(20),
                })
                .with_result(ValueId::new(21)),
            ),
            9 => {
                entry.body[1].inst = Inst::Undef {
                    ty: Ty::FnItem(FuncId::new(0)),
                }
            }
            10 => {
                if let Inst::Store { value, .. } = &mut entry.body[3].inst {
                    *value = ValueId::new(12);
                }
            }
            11 => entry.body[2].proofs.push(trust_ir::ProofAnnotation::Pure),
            12 => {
                let rest = entry.body.split_off(4);
                entry.body.push(InstrNode::new(Inst::Br {
                    target: BlockId::new(1),
                    args: vec![],
                }));
                let mut next = Block::new(BlockId::new(1));
                next.body = rest;
                module.functions[1].blocks.push(next);
            }
            _ => unreachable!(),
        }
        let before = module.clone();
        assert!(
            ModuleValues::native(&module, &native()).is_err(),
            "private memory poison {poison}"
        );
        assert_eq!(module, before);
    }
}

#[test]
fn zero_byte_memory_and_poison_are_not_validated_by_singleton_size() {
    for poison in 0..3 {
        let mut module = fixture();
        let entry = &mut module.functions[1].blocks[0];
        match poison {
            0 => {
                entry.body[0].inst = Inst::Undef {
                    ty: Ty::FnItem(FuncId::new(0)),
                }
            }
            1 => {
                entry.body.insert(
                    0,
                    InstrNode::new(Inst::NullPtr).with_result(ValueId::new(20)),
                );
                entry.body[1].inst = Inst::Load {
                    ty: Ty::FnItem(FuncId::new(0)),
                    ptr: ValueId::new(20),
                    volatile: false,
                    align: Some(1),
                };
            }
            2 => {
                entry.body.insert(
                    2,
                    InstrNode::new(Inst::NullPtr).with_result(ValueId::new(20)),
                );
                entry.body.insert(
                    3,
                    InstrNode::new(Inst::Store {
                        ty: Ty::FnItem(FuncId::new(0)),
                        ptr: ValueId::new(20),
                        value: ValueId::new(11),
                        volatile: false,
                        align: Some(1),
                    }),
                );
            }
            _ => unreachable!(),
        }
        let before = module.clone();
        assert!(
            ModuleValues::native(&module, &native()).is_err(),
            "poison/memory {poison}"
        );
        assert_eq!(
            module, before,
            "the original memory/poison operation remains an obligation"
        );
    }
}
