// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
//! Shared exact IR fixture for object-local function calls and pointer slots.

use trust_ir::value::GlobalId;
use trust_ir::{
    Block, BlockId, Constant, FuncId, FuncTy, Function, Global, Inst, InstrNode, Linkage, Module,
    Ty, ValueId, Visibility,
};

pub fn local_binding_module(
    tag: &str,
    helper_linkage: Linkage,
    helper_visibility: Visibility,
    slot_linkage: Linkage,
    offset: i128,
) -> Module {
    let mut module = Module::new(format!("x86_64_elf_local_binding_{tag}"));
    let unary = module
        .add_func_type(FuncTy {
            params: vec![Ty::U64],
            returns: vec![Ty::U64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let nullary = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::U64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let global = |name: String, ty: Ty, initializer: Constant, linkage: Linkage| Global {
        name,
        ty,
        mutable: true,
        initializer: Some(initializer),
        linkage,
        tls: None,
        align: Some(8),
        section: None,
        visibility: Visibility::Default,
        retained: false,
    };
    module.globals.push(global(
        format!("{tag}_count"),
        Ty::U64,
        Constant::Int(0),
        Linkage::Internal,
    ));
    module.globals.push(global(
        format!("{tag}_slot"),
        Ty::Ptr,
        Constant::SymbolAddr {
            symbol: "helper".into(),
            addend: 0,
        },
        slot_linkage,
    ));
    let counter = GlobalId::new(0);
    let slot = GlobalId::new(1);
    let helper = FuncId::new(0);
    let value = ValueId::new;
    let node = |inst: Inst, result: u32| InstrNode::new(inst).with_result(value(result));
    let ret = |result: u32| {
        InstrNode::new(Inst::Return {
            values: vec![value(result)],
        })
    };
    let constant = |literal: i128, result: u32| {
        node(
            Inst::Const {
                ty: Ty::U64,
                value: Constant::Int(literal),
            },
            result,
        )
    };
    let add = |lhs: u32, rhs: u32, result: u32| {
        node(
            Inst::BinOp {
                op: trust_ir::BinOp::Add,
                ty: Ty::U64,
                lhs: value(lhs),
                rhs: value(rhs),
            },
            result,
        )
    };
    let load_count = |address: u32, result: u32| {
        [
            node(Inst::GlobalAddr { global: counter }, address),
            node(
                Inst::Load {
                    ty: Ty::U64,
                    ptr: value(address),
                    volatile: false,
                    align: Some(8),
                },
                result,
            ),
        ]
    };
    let mut define = |name: String, sig, params: Vec<(ValueId, Ty)>, body: Vec<InstrNode>| {
        let id = FuncId::new(module.functions.len() as u32);
        let mut function = Function::new(id, name, sig, BlockId::new(0));
        let mut block = Block::new(BlockId::new(0));
        block.params = params;
        block.body = body;
        function.blocks.push(block);
        module.functions.push(function);
        id
    };
    let x = || vec![(value(0), Ty::U64)];

    let mut helper_body = load_count(1, 2).to_vec();
    helper_body.extend([
        constant(1, 3),
        add(2, 3, 4),
        InstrNode::new(Inst::Store {
            ty: Ty::U64,
            ptr: value(1),
            value: value(4),
            volatile: false,
            align: Some(8),
        }),
        constant(offset, 5),
        add(0, 5, 6),
        ret(6),
    ]);
    assert_eq!(define("helper".into(), unary, x(), helper_body), helper);
    define(
        format!("{tag}_direct"),
        unary,
        x(),
        vec![
            node(
                Inst::Call {
                    callee: helper,
                    args: vec![value(0)],
                },
                1,
            ),
            ret(1),
        ],
    );
    define(
        format!("{tag}_via_global"),
        unary,
        x(),
        vec![
            node(Inst::GlobalAddr { global: slot }, 1),
            node(
                Inst::Load {
                    ty: Ty::Ptr,
                    ptr: value(1),
                    volatile: false,
                    align: Some(8),
                },
                2,
            ),
            node(
                Inst::CallIndirect {
                    callee: value(2),
                    sig: unary,
                    args: vec![value(0)],
                    calling_conv: trust_ir::CallingConv::C,
                },
                3,
            ),
            ret(3),
        ],
    );
    let mut calls = load_count(0, 1).to_vec();
    calls.push(ret(1));
    define(format!("{tag}_calls"), nullary, vec![], calls);
    module.functions[helper.index() as usize].linkage = helper_linkage;
    module.functions[helper.index() as usize].visibility = helper_visibility;
    module
}
