// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

use super::*;
use trust_cg_lower::function::{BasicBlock, Signature, StackSlotInfo};
use trust_cg_lower::instructions::{Block, Instruction};

fn defined_store_model() -> (Module, Function, trust_ir::FuncId, Vec<Function>) {
    let (mut module, mut lir) = model();
    let caller_block = module.functions[0].blocks[0].clone();
    let callee = module
        .functions
        .iter_mut()
        .find(|f| f.blocks.is_empty())
        .unwrap();
    let id = callee.id;
    callee.linkage = Linkage::Internal;
    let mut block = caller_block;
    block.id = trust_ir::BlockId(0);
    block.params = vec![
        (ValueId(101), Ty::PtrMut(Box::new(Ty::F32))),
        (ValueId(102), Ty::F32),
    ];
    let mut store = block.body[1].clone();
    store.inst = Inst::Store {
        ty: Ty::F32,
        ptr: ValueId(101),
        value: ValueId(102),
        volatile: false,
        align: None,
    };
    let mut ret = block.body.last().unwrap().clone();
    ret.inst = Inst::Return { values: vec![] };
    block.body = vec![store, ret];
    callee.entry = block.id;
    callee.blocks = vec![block];
    for block in lir.blocks.values_mut() {
        for instruction in &mut block.instructions {
            if let L::Call { name, binding } = &mut instruction.opcode
                && name == &callee.name
            {
                *binding = DirectCallBinding::ExactModuleFunction {
                    function: id.index(),
                };
            }
        }
    }
    let mut lowered = Function::new(
        callee.name.clone(),
        Signature {
            params: vec![Type::I64, Type::F32],
            returns: vec![],
        },
    );
    lowered.blocks.insert(
        lowered.entry_block,
        BasicBlock {
            params: vec![(LV(0), Type::I64), (LV(1), Type::F32)],
            instructions: vec![
                Instruction {
                    opcode: L::Store {
                        ty: Type::F32,
                        align: None,
                    },
                    args: vec![LV(1), LV(0)],
                    results: vec![],
                },
                Instruction {
                    opcode: L::Return,
                    args: vec![],
                    results: vec![],
                },
            ],
            ..BasicBlock::default()
        },
    );
    (module, lir, id, vec![lowered])
}

#[test]
fn exact_defined_store_callee_retains_source_footprint_and_whole_world() {
    let (module, lir, id, callees) = defined_store_model();
    assert!(trust_ir_build::validate_module(&module).is_empty());
    let checked = check_with_callees(&module, &lir, &callees).unwrap();
    assert!(std::ptr::eq(checked.callees().as_ptr(), callees.as_ptr()));
    assert!(
        check(&module, &lir).is_err(),
        "identity without callee body"
    );
    assert_eq!(
        checked.contract().events[1],
        Event::DefinedStoreCall {
            function: id.index(),
            symbol: module
                .functions
                .iter()
                .find(|f| f.id == id)
                .unwrap()
                .name
                .clone(),
            argument: Bits::Parameter(1),
            align: None,
        }
    );
    // The complete checked logical store is consumed by the subsequent load
    // and public output, rather than just recording an unused effect label.
    assert!(matches!(
        &checked.contract().events[2],
        Event::Store {
            value: Bits::Parameter(1),
            ..
        }
    ));
}

#[test]
fn retained_callee_value_address_order_and_extra_effect_mutations_refuse() {
    let (module, lir, _, callees) = defined_store_model();
    for mutation in 0..10 {
        let mut bad = callees.clone();
        let callee = &mut bad[0];
        let b = callee.blocks.get_mut(&callee.entry_block).unwrap();
        match mutation {
            0 => b.instructions[0].args[0] = LV(0),
            1 => b.instructions[0].args[1] = LV(1),
            2 => b.instructions.swap(0, 1),
            3 => {
                let store = b.instructions[0].clone();
                b.instructions.insert(0, store);
            }
            4 => b.instructions[1].args.push(LV(1)),
            5 => {
                b.instructions[0].opcode = L::Store {
                    ty: Type::F32,
                    align: Some(4),
                }
            }
            6 => callee.name.push_str("_wrong"),
            7 => {
                callee.value_types.insert(LV(1), Type::I64);
            }
            8 => {
                // Well-typed different stored value, not merely a bad type.
                b.instructions[0].args[0] = LV(2);
                b.instructions.insert(
                    0,
                    Instruction {
                        opcode: L::Fconst {
                            ty: Type::F32,
                            imm: 0.0,
                        },
                        args: vec![],
                        results: vec![LV(2)],
                    },
                );
                callee.value_types.insert(LV(2), Type::F32);
            }
            _ => {
                // Well-typed address displaced four bytes outside the cell.
                b.instructions[0].args[1] = LV(3);
                b.instructions.insert(
                    0,
                    Instruction {
                        opcode: L::Iadd,
                        args: vec![LV(0), LV(2)],
                        results: vec![LV(3)],
                    },
                );
                b.instructions.insert(
                    0,
                    Instruction {
                        opcode: L::Iconst {
                            ty: Type::I64,
                            imm: 4,
                        },
                        args: vec![],
                        results: vec![LV(2)],
                    },
                );
                callee.value_types.insert(LV(2), Type::I64);
                callee.value_types.insert(LV(3), Type::I64);
            }
        }
        assert!(
            matches!(
                check_with_callees(&module, &lir, &bad),
                Err(Error::Lowering(_))
            ),
            "callee mutation {mutation}"
        );
    }
    let duplicate = vec![callees[0].clone(), callees[0].clone()];
    assert!(matches!(
        check_with_callees(&module, &lir, &duplicate),
        Err(Error::Lowering(_))
    ));
}

#[test]
fn ordinary_adapter_caller_consumes_independently_checked_callee_store() {
    let (mut module, _, id, _) = defined_store_model();
    // This ordinary consumer has two exact calls to the same setter with
    // different actuals. Keep opaque imports on the original compatibility
    // tests; strict lowering must not erase their pending identity carriers.
    for node in &mut module.functions[0].blocks[0].body {
        if let Inst::Call { callee, args } = &mut node.inst
            && *callee != id
        {
            *callee = id;
            args[1] = ValueId(1);
        }
    }
    module.functions.retain(|f| !f.blocks.is_empty());
    let license = trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit);
    let (lowered, validation) =
        trust_cg_lower::translate_module_strict_for_arch_with_tls_and_validation_with_license(
            &module,
            trust_cg_lower::GuardCarrierArch::AArch64,
            trust_cg_lower::TlsDialect::ElfLocalExec,
            &license,
        )
        .unwrap();
    validation
        .replay_strict_call_bindings_exhaustive(&lowered)
        .unwrap();
    let callee_name = &module.functions.iter().find(|f| f.id == id).unwrap().name;
    let callees: Vec<_> = lowered
        .iter()
        .filter(|(f, _)| &f.name == callee_name)
        .map(|(f, _)| f.clone())
        .collect();
    let caller = &lowered
        .iter()
        .find(|(f, _)| f.name == module.functions[0].name)
        .unwrap()
        .0;
    let checked = check_with_callees(&module, caller, &callees).unwrap();
    assert!(matches!(
        &checked.contract().events[2],
        Event::Store {
            value: Bits::Parameter(1),
            ..
        }
    ));
    assert!(matches!(
        &checked.contract().events[4],
        Event::Store {
            value: Bits::Parameter(0),
            ..
        }
    ));
}

#[test]
fn defined_store_source_and_call_binding_mutations_refuse() {
    let (module, lir, id, callees) = defined_store_model();
    for mutation in 0..6 {
        let mut bad = module.clone();
        let callee = bad.functions.iter_mut().find(|f| f.id == id).unwrap();
        match mutation {
            0 => callee.linkage = Linkage::External,
            1 => {
                if let Inst::Store { volatile, .. } = &mut callee.blocks[0].body[0].inst {
                    *volatile = true;
                }
            }
            2 => {
                if let Inst::Store { align, .. } = &mut callee.blocks[0].body[0].inst {
                    *align = Some(8);
                }
            }
            3 => {
                if let Inst::Store { ptr, .. } = &mut callee.blocks[0].body[0].inst {
                    *ptr = ValueId(102);
                }
            }
            4 => {
                let extra = callee.blocks[0].body[0].clone();
                callee.blocks[0].body.insert(0, extra);
            }
            _ => {
                callee.blocks[0].body[1].inst = Inst::Return {
                    values: vec![ValueId(102)],
                }
            }
        }
        assert!(
            check_with_callees(&bad, &lir, &callees).is_err(),
            "source mutation {mutation}"
        );
    }
    for binding in [
        DirectCallBinding::Interposable,
        DirectCallBinding::ExactModuleFunction {
            function: id.index() + 1,
        },
    ] {
        let mut bad = lir.clone();
        for block in bad.blocks.values_mut() {
            for instruction in &mut block.instructions {
                if let L::Call {
                    binding: actual, ..
                } = &mut instruction.opcode
                    && actual.is_exact_module()
                {
                    *actual = binding;
                }
            }
        }
        assert!(matches!(
            check_with_callees(&module, &bad, &callees),
            Err(Error::Lowering(_))
        ));
    }
    let mut wrong_argument = lir.clone();
    for block in wrong_argument.blocks.values_mut() {
        for instruction in &mut block.instructions {
            if matches!(
                instruction.opcode,
                L::Call {
                    binding: DirectCallBinding::ExactModuleFunction { .. },
                    ..
                }
            ) {
                instruction.args[1] = LV(0);
            }
        }
    }
    assert!(matches!(
        check_with_callees(&module, &wrong_argument, &callees),
        Err(Error::Mismatch)
    ));
}

#[test]
fn public_store_between_defined_call_and_load_revokes_known_cell() {
    let (mut module, mut lir, _, callees) = defined_store_model();
    let body = &mut module.functions[0].blocks[0].body;
    let mut store = body[1].clone();
    store.inst = Inst::Store {
        ty: Ty::F32,
        ptr: ValueId(3),
        value: ValueId(1),
        volatile: false,
        align: None,
    };
    body.insert(4, store);
    let block = lir.blocks.get_mut(&lir.entry_block).unwrap();
    let mut store = block.instructions[1].clone();
    store.args = vec![LV(0), LV(2)];
    block.instructions.insert(4, store);
    assert!(trust_ir_build::validate_module(&module).is_empty());
    let checked = check_with_callees(&module, &lir, &callees).unwrap();
    assert!(matches!(&checked.contract().events[3], Event::Store {
        value: Bits::Read { world: 3, address }, ..
    } if *address == cell()));
}

/// A hand-built two-callback/public-output model. The ordinary module/declaration
/// shell is an existing fixture; no new capture archive or production policy is
/// introduced. Source and LIR instructions are constructed independently.
fn model() -> (Module, Function) {
    #[derive(serde::Deserialize)]
    struct Existing {
        case: String,
        module: Module,
    }
    let old: Vec<Existing> =
        serde_json::from_str(include_str!("source_bound_cell_sources.json")).unwrap();
    let mut m = old
        .into_iter()
        .find(|c| c.case == "aliased_f32_read-O0")
        .unwrap()
        .module;
    m.target_info.as_mut().unwrap().struct_passing = trust_ir::StructPassingPolicy::NativeC;
    let caller_ty = m.functions[0].ty;
    m.func_types[caller_ty.index() as usize].params =
        vec![Ty::F32, Ty::F32, Ty::PtrMut(Box::new(Ty::F32))];
    let write = m
        .functions
        .iter()
        .find(|f| f.blocks.is_empty())
        .unwrap()
        .clone();
    let mut tag = write.clone();
    tag.name = "opaque_tag".into();
    tag.id = trust_ir::FuncId(99);
    let mut tag_ty = m.func_types[write.ty.index() as usize].clone();
    tag_ty.params[1] = Ty::U32;
    tag.ty = trust_ir::FuncTyId(m.func_types.len() as u32);
    m.func_types.push(tag_ty);
    m.functions.push(tag.clone());
    let mut block = m.functions[0].blocks[0].clone();
    block.id = trust_ir::BlockId(0);
    block.params = vec![
        (ValueId(1), Ty::F32),
        (ValueId(2), Ty::F32),
        (ValueId(3), Ty::PtrMut(Box::new(Ty::F32))),
    ];
    fn node(inst: Inst, results: &[u32]) -> trust_ir::InstrNode {
        trust_ir::InstrNode {
            inst,
            results: results.iter().copied().map(ValueId).collect(),
            proofs: vec![],
            span: None,
            proof_context: None,
            scope: None,
        }
    }
    block.body = vec![
        node(
            Inst::Alloca {
                ty: Ty::F32,
                count: None,
                align: None,
            },
            &[4],
        ),
        node(
            Inst::Store {
                ty: Ty::F32,
                ptr: ValueId(4),
                value: ValueId(1),
                volatile: false,
                align: None,
            },
            &[],
        ),
        node(
            Inst::Cast {
                op: CastOp::PtrToPtr,
                src_ty: Ty::Ptr,
                dst_ty: Ty::PtrMut(Box::new(Ty::F32)),
                operand: ValueId(4),
            },
            &[5],
        ),
        node(
            Inst::Call {
                callee: write.id,
                args: vec![ValueId(5), ValueId(2)],
            },
            &[],
        ),
        node(
            Inst::Load {
                ty: Ty::F32,
                ptr: ValueId(4),
                volatile: false,
                align: None,
            },
            &[6],
        ),
        node(
            Inst::Store {
                ty: Ty::F32,
                ptr: ValueId(3),
                value: ValueId(6),
                volatile: false,
                align: None,
            },
            &[],
        ),
        node(
            Inst::Const {
                ty: Ty::U32,
                value: Constant::Int(7),
            },
            &[7],
        ),
        node(
            Inst::Call {
                callee: tag.id,
                args: vec![ValueId(5), ValueId(7)],
            },
            &[],
        ),
        node(
            Inst::Load {
                ty: Ty::F32,
                ptr: ValueId(4),
                volatile: false,
                align: None,
            },
            &[8],
        ),
        node(
            Inst::Store {
                ty: Ty::F32,
                ptr: ValueId(3),
                value: ValueId(8),
                volatile: false,
                align: None,
            },
            &[],
        ),
        node(
            Inst::Load {
                ty: Ty::F32,
                ptr: ValueId(4),
                volatile: false,
                align: None,
            },
            &[9],
        ),
        node(
            Inst::Return {
                values: vec![ValueId(9)],
            },
            &[],
        ),
    ];
    m.functions[0].name = "trace_model".into();
    m.functions[0].entry = block.id;
    m.functions[0].blocks = vec![block];
    let mut lir = Function::new(
        "trace_model",
        Signature {
            params: vec![Type::F32, Type::F32, Type::I64],
            returns: vec![Type::F32],
        },
    );
    lir.stack_slots.push(StackSlotInfo::new(4, 4));
    lir.entry_block = Block(0);
    lir.block_order = vec![Block(0)];
    fn inst(opcode: L, args: &[u32], results: &[u32]) -> Instruction {
        Instruction {
            opcode,
            args: args.iter().copied().map(LV).collect(),
            results: results.iter().copied().map(LV).collect(),
        }
    }
    let b = BasicBlock {
        params: vec![(LV(0), Type::F32), (LV(1), Type::F32), (LV(2), Type::I64)],
        instructions: vec![
            inst(L::StackAddr { slot: 0 }, &[], &[3]),
            inst(
                L::Store {
                    ty: Type::F32,
                    align: None,
                },
                &[0, 3],
                &[],
            ),
            inst(L::Copy, &[3], &[4]),
            inst(
                L::Call {
                    name: write.name,
                    binding: DirectCallBinding::Interposable,
                },
                &[4, 1],
                &[],
            ),
            inst(
                L::Load {
                    ty: Type::F32,
                    align: None,
                },
                &[3],
                &[5],
            ),
            inst(
                L::Store {
                    ty: Type::F32,
                    align: None,
                },
                &[5, 2],
                &[],
            ),
            inst(
                L::Iconst {
                    ty: Type::I32,
                    imm: 7,
                },
                &[],
                &[6],
            ),
            inst(
                L::Call {
                    name: tag.name,
                    binding: DirectCallBinding::Interposable,
                },
                &[4, 6],
                &[],
            ),
            inst(
                L::Load {
                    ty: Type::F32,
                    align: None,
                },
                &[3],
                &[7],
            ),
            inst(
                L::Store {
                    ty: Type::F32,
                    align: None,
                },
                &[7, 2],
                &[],
            ),
            inst(
                L::Load {
                    ty: Type::F32,
                    align: None,
                },
                &[3],
                &[8],
            ),
            inst(L::Return, &[8], &[]),
        ],
        ..Default::default()
    };
    lir.blocks.insert(Block(0), b);
    assert!(trust_ir_build::validate_module(&m).is_empty());
    (m, lir)
}
#[test]
fn opaque_calls_and_public_stores_each_advance_the_memory_world() {
    let (m, l) = model();
    let c = check(&m, &l).unwrap();
    assert!(std::ptr::eq(c.module(), &m));
    assert!(std::ptr::eq(c.lir(), &l));
    assert!(std::ptr::eq(c.original(), &m.functions[0]));
    let t = c.contract();
    assert_eq!(t.events.len(), 5);
    assert_eq!(t.float_parameters, 2);
    assert_eq!(
        t.returned,
        Bits::Read {
            world: 5,
            address: cell()
        }
    );
    for (index, world) in [(2, 2), (4, 4)] {
        assert_eq!(
            t.events[index],
            Event::Store {
                address: Address {
                    base: Base::Parameter(2),
                    offset: 0
                },
                value: Bits::Read {
                    world,
                    address: cell()
                },
                align: None
            }
        );
    }
    assert_eq!(
        t.events[3],
        Event::Call {
            symbol: "opaque_tag".into(),
            argument: Argument::Tag(7)
        }
    );
}

fn byte_gep_model() -> (Module, Function) {
    let (mut module, mut lir) = model();
    let source = &mut module.functions[0].blocks[0].body;
    let store = source
        .iter_mut()
        .find(|node| {
            matches!(
                node.inst,
                Inst::Store {
                    ptr: ValueId(3),
                    ..
                }
            )
        })
        .unwrap();
    let Inst::Store { ptr, .. } = &mut store.inst else {
        unreachable!()
    };
    *ptr = ValueId(51);
    let at = source
        .iter()
        .position(|node| {
            matches!(
                node.inst,
                Inst::Store {
                    ptr: ValueId(51),
                    ..
                }
            )
        })
        .unwrap();
    source.splice(
        at..at,
        [
            trust_ir::InstrNode::new(Inst::Cast {
                op: CastOp::PtrToPtr,
                src_ty: Ty::PtrMut(Box::new(Ty::F32)),
                dst_ty: Ty::Ptr,
                operand: ValueId(3),
            })
            .with_result(ValueId(49)),
            trust_ir::InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(4),
            })
            .with_result(ValueId(50)),
            trust_ir::InstrNode::new(Inst::GEP {
                pointee_ty: Ty::U8,
                base: ValueId(49),
                indices: vec![ValueId(50)],
                inbounds: true,
            })
            .with_result(ValueId(51)),
        ],
    );
    let target = &mut lir.blocks.get_mut(&Block(0)).unwrap().instructions;
    let at = target
        .iter()
        .position(|inst| matches!(inst.opcode, L::Store { .. }) && inst.args[1] == LV(2))
        .unwrap();
    target[at].args[1] = LV(51);
    target.splice(
        at..at,
        [
            trust_cg_lower::instructions::Instruction {
                opcode: L::Iconst {
                    ty: Type::I64,
                    imm: 4,
                },
                args: vec![],
                results: vec![LV(50)],
            },
            trust_cg_lower::instructions::Instruction {
                opcode: L::ArrayGep { elem_ty: Type::I8 },
                args: vec![LV(2), LV(50)],
                results: vec![LV(51)],
            },
        ],
    );
    assert!(trust_ir_build::validate_module(&module).is_empty());
    (module, lir)
}

#[test]
fn byte_gep_source_and_lir_match_the_independently_expected_offset() {
    let (module, lir) = byte_gep_model();
    let checked = check(&module, &lir).unwrap();
    let Event::Store { address, .. } = &checked.contract().events[2] else {
        panic!("public store")
    };
    assert_eq!(address.base, Base::Parameter(2));
    assert_eq!(address.offset, 4);
}

#[test]
fn byte_gep_operand_and_role_changes_refuse_independently() {
    let (module, lir) = byte_gep_model();
    for mutation in 0..5 {
        let mut changed = module.clone();
        for node in &mut changed.functions[0].blocks[0].body {
            match (&mut node.inst, mutation) {
                (Inst::Const { value, .. }, 0 | 1) if node.results == [ValueId(50)] => {
                    *value = Constant::Int(if mutation == 0 { 8 } else { -4 });
                }
                (Inst::GEP { pointee_ty, .. }, 2) => *pointee_ty = Ty::U16,
                (Inst::GEP { inbounds, .. }, 3) => *inbounds = false,
                (Inst::GEP { indices, .. }, 4) => indices.push(ValueId(50)),
                _ => {}
            }
        }
        assert!(check(&changed, &lir).is_err(), "source mutation {mutation}");
    }
    for mutation in 0..2 {
        let mut changed = lir.clone();
        for inst in &mut changed.blocks.get_mut(&Block(0)).unwrap().instructions {
            match (&mut inst.opcode, mutation) {
                (L::Iconst { imm, .. }, 0) if inst.results == [LV(50)] => *imm = 8,
                (L::ArrayGep { elem_ty }, 1) => *elem_ty = Type::I16,
                _ => {}
            }
        }
        assert!(check(&module, &changed).is_err(), "LIR mutation {mutation}");
    }
}
#[test]
fn source_and_lir_effect_changes_are_rejected_separately() {
    let (m, l) = model();
    let mut bad = m.clone();
    if let Inst::Call { args, .. } = &mut bad.functions[0].blocks[0].body[3].inst {
        args[1] = ValueId(1);
    } else {
        panic!("fixture call")
    }
    assert!(matches!(check(&bad, &l), Err(Error::Mismatch)));
    let mut bad = m.clone();
    if let Inst::Store { ptr, .. } = &mut bad.functions[0].blocks[0].body[5].inst {
        *ptr = ValueId(4);
    } else {
        panic!("fixture store")
    }
    assert!(matches!(check(&bad, &l), Err(Error::Mismatch)));
    let mut bad = l.clone();
    bad.blocks.get_mut(&Block(0)).unwrap().instructions[10].args[0] = LV(2);
    assert!(matches!(check(&m, &bad), Err(Error::Mismatch)));
    let mut bad = l.clone();
    bad.pure_callees.insert("opaque_tag".into());
    assert!(matches!(check(&m, &bad), Err(Error::Lowering(_))));
    let mut bad = m.clone();
    bad.functions
        .iter_mut()
        .find(|f| f.name == "opaque_tag")
        .unwrap()
        .attrs
        .readonly = true;
    assert!(matches!(check(&bad, &l), Err(Error::Source(_))));
}
#[test]
fn allocation_precedes_public_memory_observations_and_effects() {
    let (m, l) = model();
    for load in [false, true] {
        let mut bad = m.clone();
        let mut prefix = bad.functions[0].blocks[0].body[if load { 4 } else { 5 }].clone();
        if load {
            if let Inst::Load { ptr, .. } = &mut prefix.inst {
                *ptr = ValueId(3);
            } else {
                panic!("fixture load")
            }
            prefix.results = vec![ValueId(100)];
        } else if let Inst::Store { value, .. } = &mut prefix.inst {
            *value = ValueId(1);
        } else {
            panic!("fixture store")
        }
        bad.functions[0].blocks[0].body.insert(0, prefix);
        assert!(trust_ir_build::validate_module(&bad).is_empty());
        assert!(matches!(check(&bad, &l), Err(Error::Source(_))));

        let mut bad = l.clone();
        let block = bad.blocks.get_mut(&Block(0)).unwrap();
        let mut prefix = block.instructions[if load { 4 } else { 5 }].clone();
        if load {
            prefix.args = vec![LV(2)];
            prefix.results = vec![LV(100)];
        } else {
            prefix.args = vec![LV(0), LV(2)];
        }
        block.instructions.insert(0, prefix);
        assert!(matches!(check(&m, &bad), Err(Error::Lowering(_))));
    }
}

#[test]
fn public_output_aliases_are_not_simplified_out_of_later_reads() {
    let (mut m, mut l) = model();
    for (index, value) in [(5, ValueId(1)), (9, ValueId(2))] {
        if let Inst::Store { value: stored, .. } = &mut m.functions[0].blocks[0].body[index].inst {
            *stored = value;
        } else {
            panic!("fixture public store")
        }
    }
    for (index, value) in [(5, LV(0)), (9, LV(1))] {
        l.blocks.get_mut(&Block(0)).unwrap().instructions[index].args[0] = value;
    }
    let c = check(&m, &l).unwrap();
    fn address(p: &Address, public: u64) -> u64 {
        let base = match p.base {
            Base::Cell => 0x1000,
            Base::Parameter(2) => public,
            _ => panic!("fixture parameter"),
        };
        base.wrapping_add(p.offset)
    }
    fn bits(b: &Bits, worlds: &[HashMap<u64, u32>], public: u64) -> u32 {
        match b {
            Bits::Parameter(0) => 11,
            Bits::Parameter(1) => 22,
            Bits::Parameter(_) => panic!("fixture float"),
            Bits::Read { world, address: p } => worlds[*world][&address(p, public)],
        }
    }
    for (public, expected) in [(0x1000, 22), (0x2000, 44)] {
        let mut worlds = vec![HashMap::new()];
        for event in &c.contract().events {
            let mut next = worlds.last().unwrap().clone();
            match event {
                Event::Store {
                    address: p, value, ..
                } => {
                    let v = bits(value, &worlds, public);
                    next.insert(address(p, public), v);
                }
                Event::Call {
                    argument: Argument::Float(_),
                    ..
                } => {
                    next.insert(public, 77);
                    next.insert(0x1000, 33);
                }
                Event::Call {
                    argument: Argument::Tag(7),
                    ..
                } => {
                    next.insert(public, 88);
                    next.insert(0x1000, 44);
                }
                _ => panic!("fixture call"),
            }
            worlds.push(next);
        }
        assert_eq!(bits(&c.contract().returned, &worlds, public), expected);
    }
}
