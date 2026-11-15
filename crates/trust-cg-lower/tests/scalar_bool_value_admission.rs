// Copyright 2026 Andrew Yates | Apache-2.0
//! The adapter admits no scalar-`bool` operation that trust-ir leaves
//! undefined and whose machine `B1` would not hold exactly 0 or 1.
//!
//! The machine `B1` is a clean 32-bit bool: every selector consumer and the
//! ABI read the whole register (an LLVM callee of a `bool` argument reads
//! `edi` whole). Two trust-ir shapes the validator refuses reached it dirty
//! through lanes that run no validation (the AOT `Compiler::compile`, the
//! trust-cg CLI's JSON input): measured on x86-64 with every register filled
//! with 0xA5 bytes, `not bool` returned EAX=0xFFFFFFFE for `true`, and
//! `bitcast u8 -> bool` of a loaded byte passed 0xA5A5A501. trust-ir states
//! both as invalid: `UnOpNotOnScalarBool` (WS2.21), and
//! `CastLayoutUnsupported` (`BoolLaneReinterpret`) for a reinterpretation into
//! a bool; its interpreter has no scalar `Bool` arm for either. The adapter now
//! refuses both, and each refusal below is checked against the validator.

use trust_cg_lower::adapter::{AdapterError, translate_function_with_license};
use trust_cg_lower::function::Function as LirFunction;
use trust_cg_lower::instructions::Opcode;
use trust_cg_lower::types::Type;
use trust_ir::{
    BinOp, Block, BlockId, CastOp, Constant, FuncId, FuncTy, Function, ICmpOp, Inst, InstrNode,
    Module, Ty, UnOp, ValueId,
};
use trust_ir_build::validate::{ValidationError, validate_module};

fn v(n: u32) -> ValueId {
    ValueId::new(n)
}

/// `fn f(p0: param) -> ret { body; return %10 }`.
fn module_with(param: Ty, ret: Ty, body: Vec<InstrNode>) -> Module {
    let mut module = Module::new("scalar_bool_value_admission");
    let ft = module
        .add_func_type(FuncTy {
            params: vec![param.clone()],
            returns: vec![ret],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = Function::new(FuncId::new(0), "f", ft, BlockId::new(0));
    let mut body = body;
    body.push(InstrNode::new(Inst::Return {
        values: vec![v(10)],
    }));
    function.blocks = vec![Block {
        id: BlockId::new(0),
        params: vec![(v(0), param)],
        body,
    }];
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
    module
}

fn translate(module: &Module) -> Result<LirFunction, AdapterError> {
    translate_function_with_license(&module.functions[0], module, &permit_unlicensed())
        .map(|(lir, _)| lir)
}

fn not(ty: Ty) -> Module {
    module_with(
        ty.clone(),
        ty.clone(),
        vec![
            InstrNode::new(Inst::UnOp {
                op: UnOp::Not,
                ty,
                operand: v(0),
            })
            .with_result(v(10)),
        ],
    )
}

fn bitcast(src_ty: Ty, dst_ty: Ty) -> Module {
    module_with(
        src_ty.clone(),
        dst_ty.clone(),
        vec![
            InstrNode::new(Inst::Cast {
                op: CastOp::Bitcast,
                src_ty,
                dst_ty,
                operand: v(0),
            })
            .with_result(v(10)),
        ],
    )
}

fn lir_opcodes(lir: &LirFunction) -> Vec<Opcode> {
    lir.blocks
        .values()
        .flat_map(|block| &block.instructions)
        .map(|inst| inst.opcode.clone())
        .collect()
}

#[test]
fn scalar_bool_not_is_refused_as_trust_ir_refuses_it() {
    let module = not(Ty::Bool);
    assert!(
        validate_module(&module)
            .iter()
            .any(|error| matches!(error, ValidationError::UnOpNotOnScalarBool { .. })),
        "trust-ir's validator states `not bool` invalid: {:?}",
        validate_module(&module)
    );
    let error = translate(&module).expect_err("the adapter must refuse `not bool`");
    assert!(
        matches!(&error, AdapterError::UnsupportedInstruction(message)
            if message.contains("UnOp::Not") && message.contains("Bool")),
        "{error:?}"
    );

    // Integer NOT still lowers to `Bnot`, and a bool negation spelled the way
    // trust-ir defines it still lowers.
    for ty in [Ty::U8, Ty::I32, Ty::U64] {
        let lir = translate(&not(ty.clone()))
            .unwrap_or_else(|error| panic!("`not {ty:?}` must lower: {error:?}"));
        assert!(lir_opcodes(&lir).contains(&Opcode::Bnot), "{ty:?}");
    }
    let eq_false = module_with(
        Ty::Bool,
        Ty::Bool,
        vec![
            InstrNode::new(Inst::Const {
                ty: Ty::Bool,
                value: Constant::Bool(false),
            })
            .with_result(v(9)),
            InstrNode::new(Inst::ICmp {
                op: ICmpOp::Eq,
                ty: Ty::Bool,
                lhs: v(0),
                rhs: v(9),
            })
            .with_result(v(10)),
        ],
    );
    let xor_true = module_with(
        Ty::Bool,
        Ty::Bool,
        vec![
            InstrNode::new(Inst::Const {
                ty: Ty::Bool,
                value: Constant::Bool(true),
            })
            .with_result(v(9)),
            InstrNode::new(Inst::BinOp {
                op: BinOp::BXor,
                ty: Ty::Bool,
                lhs: v(0),
                rhs: v(9),
            })
            .with_result(v(10)),
        ],
    );
    for (name, module) in [("icmp eq b, false", eq_false), ("bxor b, true", xor_true)] {
        let lir = translate(&module).unwrap_or_else(|error| panic!("{name}: {error:?}"));
        assert!(
            !lir_opcodes(&lir).contains(&Opcode::Bnot),
            "{name}: no bitwise NOT of a B1"
        );
    }
}

#[test]
fn bitcast_into_bool_is_refused_as_trust_ir_refuses_it() {
    for src_ty in [Ty::U8, Ty::I8] {
        let module = bitcast(src_ty.clone(), Ty::Bool);
        assert!(
            validate_module(&module)
                .iter()
                .any(|error| matches!(error, ValidationError::CastLayoutUnsupported { .. })),
            "{src_ty:?}: trust-ir's validator states the reinterpretation invalid: {:?}",
            validate_module(&module)
        );
        let error = translate(&module)
            .expect_err("the adapter must refuse a bitcast into bool from a byte");
        assert!(
            matches!(&error, AdapterError::UnsupportedInstruction(message)
                if message.contains("Bitcast") && message.contains("dst_ty=Bool")),
            "{src_ty:?}: {error:?}"
        );
    }

    // The identity cast is not a reinterpretation.
    let lir = translate(&bitcast(Ty::Bool, Ty::Bool)).expect("`bitcast bool -> bool` lowers");
    assert!(lir_opcodes(&lir).contains(&Opcode::Bitcast { to_ty: Type::B1 }));
    // A `bool` SOURCE keeps its 0/1 value in the byte carrier; the rustc
    // bridge lowers `b as u8` to exactly this cast.
    let lir = translate(&bitcast(Ty::Bool, Ty::U8)).expect("`bitcast bool -> u8` lowers");
    assert!(lir_opcodes(&lir).contains(&Opcode::Bitcast { to_ty: Type::I8 }));
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes (or fails by name) because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
