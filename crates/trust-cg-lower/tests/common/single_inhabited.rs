// Copyright 2026 Andrew Yates. Apache-2.0.
#![allow(dead_code)]
use trust_ir::{
    Block, BlockId, CastOp, Constant, EnumDef, EnumId, EnumLayoutDescriptor, EnumTagEncoding,
    EnumVariant, FuncId, FuncTy, Function, Inst, InstrNode, Module, Ty, ValueId,
};

pub fn definition(active: u32) -> EnumDef {
    assert!(active < 2);
    let mut variants = vec![
        EnumVariant {
            name: "Zero".into(),
            fields: vec![Ty::Never],
            field_names: vec![],
        },
        EnumVariant {
            name: "One".into(),
            fields: vec![Ty::Never],
            field_names: vec![],
        },
    ];
    variants[active as usize].fields = vec![Ty::U64];
    let mut offsets = vec![vec![], vec![]];
    offsets[active as usize] = vec![0];
    let mut def = EnumDef::new(EnumId::new(0), "Selected", variants);
    def.discriminants = vec![Some(11), Some(29)];
    def.layout = Some(EnumLayoutDescriptor {
        encoding: EnumTagEncoding::SingleInhabited { variant: active },
        size: 8,
        align: 8,
        variant_field_offsets: offsets,
    });
    def
}

pub fn expected(active: u32) -> u64 {
    if active == 0 { 18 } else { 36 }
}

pub fn module(active: u32, memory: bool) -> Module {
    let mut module = Module::new("single_inhabited");
    module.enums.push(definition(active));
    let signature = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::U64],
            abi: None,
            is_vararg: false,
        })
        .unwrap();
    let ty = Ty::Enum(EnumId::new(0));
    let disc = if active == 0 { 11 } else { 29 };
    let mut body = vec![
        InstrNode::new(Inst::Const {
            ty: ty.clone(),
            value: Constant::Aggregate(vec![Constant::Int(disc), Constant::Int(7)]),
        })
        .with_result(ValueId::new(0)),
    ];
    let value = if memory {
        body.extend([
            InstrNode::new(Inst::Alloca {
                ty: ty.clone(),
                count: None,
                align: Some(8),
            })
            .with_result(ValueId::new(1)),
            InstrNode::new(Inst::Store {
                ty: ty.clone(),
                ptr: ValueId::new(1),
                value: ValueId::new(0),
                volatile: false,
                align: Some(8),
            }),
            InstrNode::new(Inst::Load {
                ty: ty.clone(),
                ptr: ValueId::new(1),
                volatile: false,
                align: Some(8),
            })
            .with_result(ValueId::new(2)),
        ]);
        ValueId::new(2)
    } else {
        ValueId::new(0)
    };
    body.extend([
        InstrNode::new(Inst::ExtractField {
            ty: Ty::U64,
            aggregate: value,
            field: 1,
        })
        .with_result(ValueId::new(3)),
        InstrNode::new(Inst::ExtractField {
            ty: Ty::U8,
            aggregate: value,
            field: 0,
        })
        .with_result(ValueId::new(4)),
        InstrNode::new(Inst::Cast {
            op: CastOp::ZExt,
            src_ty: Ty::U8,
            dst_ty: Ty::U64,
            operand: ValueId::new(4),
        })
        .with_result(ValueId::new(5)),
        InstrNode::new(Inst::BinOp {
            op: trust_ir::BinOp::Add,
            ty: Ty::U64,
            lhs: ValueId::new(3),
            rhs: ValueId::new(5),
        })
        .with_result(ValueId::new(6)),
        InstrNode::new(Inst::Return {
            values: vec![ValueId::new(6)],
        }),
    ]);
    let mut function = Function::new(FuncId::new(0), "run", signature, BlockId::new(0));
    function.blocks = vec![Block {
        id: BlockId::new(0),
        params: vec![],
        body,
    }];
    module.try_add_function(function).unwrap();
    module
}
