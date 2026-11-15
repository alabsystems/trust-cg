// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Genuine source functions; no supplied lowering verdict or numeric validator.

use trust_ir::{
    Block, BlockId, Constant, Endianness, FuncId, FuncTy, Function, Inst, InstrNode, Module,
    StructPassingPolicy, SwitchCase, TargetInfo, Ty, ValueId,
};

pub(super) fn source(ty: Ty, case: Constant) -> Module {
    let mut module = Module::new("switch_case_source_contract");
    module.target_info = Some(TargetInfo {
        triple: "aarch64-unknown-linux-gnu".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: StructPassingPolicy::NativeC,
    });
    let signature = module
        .add_func_type(FuncTy::unrecorded(vec![ty.clone()], vec![Ty::I32], false))
        .expect("Module::add_func_type: test fixture");
    let mut function = Function::new(FuncId::new(60_002), "dispatch", signature, BlockId::new(7));
    let mut entry = Block::new(BlockId::new(7));
    entry.params.push((ValueId::new(0), ty));
    entry.body.push(InstrNode::new(Inst::Switch {
        value: ValueId::new(0),
        default: BlockId::new(9),
        default_args: vec![],
        cases: vec![SwitchCase {
            value: case,
            target: BlockId::new(8),
            args: vec![],
        }],
        exhaustive_enum_unreachable: false,
    }));
    function.blocks.push(entry);
    for (id, answer) in [(8, 10), (9, 20)] {
        let mut block = Block::new(BlockId::new(id));
        let result = ValueId::new(id);
        block.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(answer),
            })
            .with_result(result),
        );
        block.body.push(InstrNode::new(Inst::Return {
            values: vec![result],
        }));
        function.blocks.push(block);
    }
    module.functions.push(function);
    module
}

pub(super) fn set_case(function: &mut Function, case: Constant) {
    let Inst::Switch { cases, .. } = &mut function.blocks[0].body[0].inst else {
        panic!("actual retained Switch");
    };
    cases[0].value = case;
}

pub(super) fn wasm_source(module: &Module) -> Module {
    let mut retargeted = module.clone();
    retargeted.target_info = Some(trust_cg_codegen::wasm::wasm32_target_info());
    retargeted
}

pub(super) fn source_answer(module: &Module, ty: &Ty, input: i128) -> i128 {
    let returned = trust_ir::Interpreter::with_module(module)
        .execute_func(
            module.functions[0].id,
            [trust_ir::InterpretValue::int(ty.clone(), input).unwrap()],
        )
        .expect("independent reference execution of a valid source switch");
    assert_eq!(returned.returns.len(), 1);
    returned.returns[0].as_int().unwrap().as_signed()
}
