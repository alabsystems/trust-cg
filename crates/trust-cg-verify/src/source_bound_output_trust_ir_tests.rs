// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

use super::*;
use crate::source_bound_frame::{check_aarch64_output_bytes, source_bound_frame};

use trust_cg_lower::instructions::{Opcode, Value};
use trust_ir::{Block, BlockId, FuncId, FuncTy, InstrNode, ParamAttrs};

fn v(index: u32) -> ValueId {
    ValueId::new(index)
}

fn fixture() -> Module {
    let mut module = Module::new("output_contract_fixture");
    let mut params = vec![Ty::RefMut(Box::new(Ty::Tuple(vec![Ty::U64; 5])))];
    params.extend(vec![Ty::U64; 5]);
    let signature = module
        .add_func_type(FuncTy {
            params: params.clone(),
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let entry = BlockId::new(9);
    let mut function = trust_ir::Function::new(FuncId::new(21), "output_writer", signature, entry);
    let mut block = Block::new(entry);
    block.params = params
        .into_iter()
        .enumerate()
        .map(|(i, ty)| (v(i as u32), ty))
        .collect();
    for index in 0..5 {
        block.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(i128::from(index * 8)),
            })
            .with_result(v(6 + index * 2)),
        );
        block.body.push(
            InstrNode::new(Inst::GEP {
                pointee_ty: Ty::I8,
                base: v(0),
                indices: vec![v(6 + index * 2)],
                inbounds: false,
            })
            .with_result(v(7 + index * 2)),
        );
        block.body.push(InstrNode::new(Inst::Store {
            ty: Ty::U64,
            ptr: v(7 + index * 2),
            value: v(index + 1),
            volatile: false,
            align: Some(8),
        }));
    }
    block
        .body
        .push(InstrNode::new(Inst::Return { values: vec![] }));
    function.blocks.push(block);
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
    module
}

fn code(paired: bool) -> Vec<u8> {
    let mut words: Vec<u32> = vec![0xa9bf_7bfd, 0x9100_03fd];
    if paired {
        words.extend([0xa900_0801, 0xa901_1003, 0xf900_1005]);
    } else {
        words.extend([
            0xf900_0001,
            0xf900_0402,
            0xf900_0803,
            0xf900_0c04,
            0xf900_1005,
        ]);
    }
    words.extend([0xa8c1_7bfd, 0xd65f_03c0]);
    words.into_iter().flat_map(u32::to_le_bytes).collect()
}

fn lower(module: &Module) -> Function {
    trust_cg_lower::translate_function_with_license(
        &module.functions[0],
        module,
        &permit_unlicensed(),
    )
    .unwrap()
    .0
}

#[test]
fn typed_output_original_source_binds_real_adapter_and_bytes_without_frame_authority() {
    let module = fixture();
    let lir = lower(&module);
    assert_eq!(lir.param_pointee_types.len(), 1);
    for paired in [false, true] {
        let code = code(paired);
        let checked = check_aarch64_trust_ir_output_bytes(&module, 0, &lir, &code).unwrap();
        assert!(std::ptr::eq(checked.module(), &module));
        assert!(std::ptr::eq(checked.source(), &module.functions[0]));
        assert!(std::ptr::eq(checked.lir(), &lir));
        assert!(std::ptr::eq(checked.code(), code.as_slice()));
        assert_eq!(
            checked.requirements(),
            OutputMemoryRequirements {
                parameter_index: 0,
                byte_extent: 40,
                alignment: 8,
            }
        );
        assert!(check_aarch64_output_bytes(&lir, &code).is_err());
        let (_, machine) = super::super::tests::fixture(paired);
        assert!(source_bound_frame(&lir, &machine).is_err());
        let query =
            crate::ay_bridge::generate_smt2_query_raw(checked.obligation(), &Default::default());
        println!(
            "OUTPUT_TYPED_QUERY={}",
            serde_json::to_string(&query).unwrap()
        );
    }
}

#[test]
fn typed_output_source_mutations_refuse_even_when_claims_describe_writable_memory() {
    let original = fixture();
    let lir = lower(&original);
    let code = code(true);
    let inner = Box::new(Ty::Tuple(vec![Ty::U64; 5]));
    for pointer in [
        Ty::Ref(inner.clone()),
        Ty::PtrConst(inner.clone()),
        Ty::PtrMut(inner.clone()),
        Ty::Rc(inner),
        Ty::I64,
    ] {
        let mut wrong = original.clone();
        wrong.func_types[0].params[0] = pointer.clone();
        wrong.functions[0].blocks[0].params[0].1 = pointer;
        wrong.functions[0].attrs.params = vec![ParamAttrs {
            dereferenceable: Some(40),
            nonnull: true,
            align: Some(8),
            noalias: true,
            ..Default::default()
        }];
        assert!(check_aarch64_trust_ir_output_bytes(&wrong, 0, &lir, &code).is_err());
    }
    for mutation in 0..21 {
        let mut wrong = original.clone();
        let function = &mut wrong.functions[0];
        match mutation {
            0 => function.name.push_str("_different"),
            1 => function.blocks[0].params[0].1 = Ty::Ptr,
            2 => function.blocks[0].params[1].0 = v(0),
            3 => function.blocks[0].body[0].results = vec![v(0)],
            4 => function.blocks[0].body[2].results = vec![v(77)],
            5 => {
                function.blocks[0].body[2].inst = Inst::Store {
                    ty: Ty::U64,
                    ptr: v(7),
                    value: v(2),
                    volatile: false,
                    align: Some(8),
                }
            }
            6 => {
                function.blocks[0].body[0].inst = Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(40),
                }
            }
            7 => {
                function.blocks[0].body[2].inst = Inst::Store {
                    ty: Ty::U64,
                    ptr: v(7),
                    value: v(1),
                    volatile: true,
                    align: Some(8),
                }
            }
            8 => function.blocks[0].body.swap(2, 5),
            9 => {
                function.blocks[0].body.pop();
            }
            10 => function.blocks.push(Block::new(BlockId::new(100))),
            11 => function.attrs.readonly = true,
            12 => function.attrs.readnone = true,
            13 => function.attrs.naked = true,
            14 => {
                function.attrs.params = vec![ParamAttrs {
                    sret: true,
                    ..Default::default()
                }]
            }
            15 => wrong.func_types[0].is_vararg = true,
            16 => {
                let ty = Ty::RefMut(Box::new(Ty::Tuple(vec![Ty::U64; 4])));
                wrong.func_types[0].params[0] = ty.clone();
                function.blocks[0].params[0].1 = ty;
            }
            17 => {
                function.blocks[0].body[0].inst = Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(-1),
                }
            }
            18 => {
                function.blocks[0].body[1].inst = Inst::GEP {
                    pointee_ty: Ty::I8,
                    base: v(1),
                    indices: vec![v(6)],
                    inbounds: false,
                }
            }
            19 => {
                function.blocks[0].body[0].inst = Inst::Const {
                    ty: Ty::U64,
                    value: Constant::Int(-1),
                }
            }
            _ => {
                function.blocks[0].body[2].inst = Inst::Store {
                    ty: Ty::U64,
                    ptr: v(7),
                    value: v(0),
                    volatile: false,
                    align: Some(8),
                }
            }
        }
        assert!(
            check_aarch64_trust_ir_output_bytes(&wrong, 0, &lir, &code).is_err(),
            "mutation={mutation}"
        );
    }
    assert!(check_aarch64_trust_ir_output_bytes(&original, 1, &lir, &code).is_err());
}

#[test]
fn typed_output_metadata_and_lowering_cannot_substitute_for_original_source() {
    let module = fixture();
    let lir = lower(&module);
    let code = code(false);
    for mutation in 0..7 {
        let mut wrong = lir.clone();
        match mutation {
            0 => wrong.param_pointee_types.clear(),
            1 => wrong.param_pointee_types[0].param_index = 1,
            2 => wrong.param_pointee_types[0].pointee_ty = Type::Struct(vec![Type::I64; 4]),
            3 => wrong
                .param_pointee_types
                .push(wrong.param_pointee_types[0].clone()),
            4 => wrong.signature.params.pop().map(|_| ()).unwrap(),
            5 => {
                let store = wrong
                    .blocks
                    .values_mut()
                    .flat_map(|b| &mut b.instructions)
                    .find(|i| matches!(i.opcode, Opcode::Store { .. }))
                    .unwrap();
                store.args[0] = Value(5);
            }
            _ => wrong.signature.returns.push(Type::I64),
        }
        assert!(
            check_aarch64_trust_ir_output_bytes(&module, 0, &wrong, &code).is_err(),
            "mutation={mutation}"
        );
    }
    for index in 0..code.len() * 8 {
        let mut wrong = code.clone();
        wrong[index / 8] ^= 1 << (index % 8);
        assert!(
            check_aarch64_trust_ir_output_bytes(&module, 0, &lir, &wrong).is_err(),
            "byte bit={index}"
        );
    }
}

#[test]
fn typed_output_array_extent_and_unconditional_source_chain_are_checked() {
    let mut module = fixture();
    let element = module
        .add_type(Ty::U64)
        .expect("Module::add_type: test fixture");
    let ty = Ty::RefMut(Box::new(Ty::Array(element, 5)));
    module.func_types[0].params[0] = ty.clone();
    module.functions[0].blocks[0].params[0].1 = ty;
    let tail = module.functions[0].blocks[0].body.split_off(9);
    module.functions[0].blocks[0]
        .body
        .push(InstrNode::new(Inst::Br {
            target: BlockId::new(12),
            args: vec![],
        }));
    module.functions[0].blocks.push(Block {
        id: BlockId::new(12),
        params: vec![],
        body: tail,
    });
    let lir = lower(&module);
    let code = code(true);
    let checked = check_aarch64_trust_ir_output_bytes(&module, 0, &lir, &code).unwrap();
    assert_eq!(checked.requirements().byte_extent, 40);
    let mut wrong = module.clone();
    wrong.types[element.index() as usize] = Ty::U32;
    assert!(check_aarch64_trust_ir_output_bytes(&wrong, 0, &lir, &code).is_err());
    let mut wrong = module.clone();
    wrong.functions[0].blocks[1].body.pop();
    wrong.functions[0].blocks[1]
        .body
        .push(InstrNode::new(Inst::Br {
            target: BlockId::new(9),
            args: vec![],
        }));
    assert!(check_aarch64_trust_ir_output_bytes(&wrong, 0, &lir, &code).is_err());
}

#[test]
fn typed_output_tracks_nonfirst_parameter_and_literal_store_values() {
    let mut module = fixture();
    module.func_types[0].params.swap(0, 2);
    module.functions[0].blocks[0].params.swap(0, 2);
    let lir = lower(&module);
    let words: [u32; 9] = [
        0xa9bf_7bfd,
        0x9100_03fd,
        0xf900_0041,
        0xf900_0440,
        0xf900_0843,
        0xf900_0c44,
        0xf900_1045,
        0xa8c1_7bfd,
        0xd65f_03c0,
    ];
    let code: Vec<_> = words.into_iter().flat_map(u32::to_le_bytes).collect();
    let checked = check_aarch64_trust_ir_output_bytes(&module, 0, &lir, &code).unwrap();
    assert_eq!(checked.requirements().parameter_index, 2);

    let mut module = fixture();
    module.functions[0].blocks[0].body.insert(
        14,
        InstrNode::new(Inst::Const {
            ty: Ty::U64,
            value: Constant::Int(i128::from(u64::MAX)),
        })
        .with_result(v(91)),
    );
    if let Inst::Store { value, .. } = &mut module.functions[0].blocks[0].body[15].inst {
        *value = v(91);
    } else {
        panic!("fixture final store");
    }
    let lir = lower(&module);
    let mut code = self::code(false);
    code.splice(8..8, 0x9280_0005_u32.to_le_bytes()); // MOVN X5,#0.
    check_aarch64_trust_ir_output_bytes(&module, 0, &lir, &code).unwrap();
}

#[test]
fn typed_output_captured_rust_source_binds_without_erasing_metadata_or_bounds_guards() {
    // Exact retained modules from the genuine Trust development frontend.
    // O1, O2 and O3 captures are byte-identical. Target words are independent
    // reference streams, not bytes emitted by the still-refused Rust compile.
    let module: Module = serde_json::from_str(include_str!(
        "../tests/fixtures/output_memory_writer-O1.trust-ir.json"
    ))
    .unwrap();
    let lir = lower(&module);
    for paired in [false, true] {
        let code = code(paired);
        let checked = check_aarch64_trust_ir_output_bytes(&module, 0, &lir, &code)
            .unwrap_or_else(|error| panic!("{error}: {lir:#?}"));
        assert_eq!(checked.requirements().byte_extent, 40);
        assert_eq!(lir.param_pointee_types.len(), 1);
        assert!(check_aarch64_output_bytes(&lir, &code).is_err());
        let query =
            crate::ay_bridge::generate_smt2_query_raw(checked.obligation(), &Default::default());
        println!(
            "OUTPUT_CAPTURED_QUERY={}",
            serde_json::to_string(&query).unwrap()
        );
    }
    let guarded: Module = serde_json::from_str(include_str!(
        "../tests/fixtures/output_memory_writer-O0.trust-ir.json"
    ))
    .unwrap();
    let lir = lower(&guarded);
    assert_eq!(lir.blocks.len(), 6);
    assert_eq!(
        lir.blocks
            .values()
            .flat_map(|b| &b.instructions)
            .filter(|i| matches!(i.opcode, Opcode::GuardBoundsCheck { .. }))
            .count(),
        5
    );
    for paired in [false, true] {
        let code = code(paired);
        let checked = check_aarch64_trust_ir_output_bytes(&guarded, 0, &lir, &code)
            .unwrap_or_else(|error| panic!("{error}: {lir:#?}"));
        assert_eq!(checked.requirements().byte_extent, 40);
        assert!(std::ptr::eq(checked.module(), &guarded));
        assert!(std::ptr::eq(checked.lir(), &lir));
        assert!(check_aarch64_output_bytes(&lir, &code).is_err());
        let query =
            crate::ay_bridge::generate_smt2_query_raw(checked.obligation(), &Default::default());
        println!(
            "OUTPUT_GUARDED_QUERY={}",
            serde_json::to_string(&query).unwrap()
        );
    }
}

#[path = "source_bound_output_bounds_tests.rs"]
mod bounds_tests;

#[path = "source_bound_output_abi_tests.rs"]
mod abi_tests;

#[test]
fn typed_output_actual_captured_writer_binds_actual_frameless_bytes() {
    let module: Module = serde_json::from_str(include_str!(
        "../tests/fixtures/output_memory_writer-layout-O1.trust-ir.json"
    ))
    .unwrap();
    assert!(trust_ir_build::validate_module(&module).is_empty());
    let lir = lower(&module);
    let code = include_bytes!("../tests/fixtures/output_memory_writer-frameless-O1.aarch64.bin");
    let checked = check_aarch64_trust_ir_output_bytes(&module, 0, &lir, code).unwrap();
    assert_eq!(checked.frame(), Aarch64OutputFrame::Frameless);
    assert_eq!(checked.requirements().byte_extent, 40);
    assert_eq!(checked.requirements().alignment, 8);
    println!(
        "FRAMELESS_TYPED_OUTPUT_QUERY={}",
        serde_json::to_string(&crate::ay_bridge::generate_smt2_query_raw(
            checked.obligation(),
            &Default::default()
        ))
        .unwrap()
    );
    let mut changed = module.clone();
    for block in &mut changed.functions[0].blocks {
        if let Some(node) = block
            .body
            .iter_mut()
            .find(|node| matches!(node.inst, Inst::Store { .. }))
        {
            let Inst::Store { volatile, .. } = &mut node.inst else {
                unreachable!()
            };
            *volatile = true;
            break;
        }
    }
    assert!(check_aarch64_trust_ir_output_bytes(&changed, 0, &lir, code).is_err());
    let mut wrong_lir = lir.clone();
    wrong_lir.param_pointee_types.clear();
    assert!(check_aarch64_trust_ir_output_bytes(&module, 0, &wrong_lir, code).is_err());
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
