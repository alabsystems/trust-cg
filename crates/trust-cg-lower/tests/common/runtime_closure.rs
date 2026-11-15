// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use trust_ir::{
    Block, BlockId, ClosureTy, FuncId, FuncTy, Function, Inst, InstrNode, Module, Ty, ValueId,
};

/// A valid unused runtime closure whose physical target takes its three live
/// captures before the apparent arguments. The scalar twin differs only by
/// omission of the constructor, not by a different signature/type table.
pub fn runtime_closure_module(construct: bool) -> Module {
    let mut module = Module::new("runtime_closure");
    let host = module
        .add_func_type(FuncTy {
            params: vec![Ty::I64],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .unwrap();
    let apparent = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .unwrap();
    let physical = module
        .add_func_type(FuncTy {
            params: vec![Ty::I64; 3],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .unwrap();
    let closure = module
        .add_closure_type(ClosureTy {
            func: apparent,
            captures: vec![Ty::I64; 3],
        })
        .unwrap();
    let mut function = Function::new(FuncId::new(0), "host", host, BlockId::new(0));
    let mut block = Block::new(BlockId::new(0));
    block.params = vec![(ValueId::new(0), Ty::I64)];
    if construct {
        block.body.push(
            InstrNode::new(Inst::MakeClosure {
                ty: closure,
                func: FuncId::new(1),
                captures: vec![ValueId::new(0); 3],
            })
            .with_result(ValueId::new(1)),
        );
    }
    block.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(0)],
    }));
    function.blocks.push(block);
    module.try_add_function(function).unwrap();
    let mut target = Function::new(FuncId::new(1), "target", physical, BlockId::new(0));
    let mut block = Block::new(BlockId::new(0));
    block.params = (0..3).map(|index| (ValueId::new(index), Ty::I64)).collect();
    block.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(0)],
    }));
    target.blocks.push(block);
    module.try_add_function(target).unwrap();
    module
}
