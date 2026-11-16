// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
//! Diagnostic interpretation must preserve an unsupported nominal boundary.
use trust_cg_codegen::interpreter::{InterpreterError, InterpreterValue, interpret};
use trust_ir::*;

fn returning(id: u32, name: &str, signature: u32, ty: Ty, value: Constant) -> Function {
    let mut f = Function::new(
        FuncId::new(id),
        name,
        FuncTyId::new(signature),
        BlockId::new(0),
    );
    let mut b = Block::new(BlockId::new(0));
    let mut c = InstrNode::new(Inst::Const { ty, value });
    c.results.push(ValueId::new(0));
    b.body = vec![
        c,
        InstrNode::new(Inst::Return {
            values: vec![ValueId::new(0)],
        }),
    ];
    f.blocks.push(b);
    f
}

#[test]
fn distinct_valid_nominal_items_cannot_both_be_diagnostic_undef_success() {
    let mut m = Module::new("nominal_items");
    m.func_types = vec![
        FuncTy::unrecorded(vec![], vec![], false),
        FuncTy::unrecorded(vec![], vec![Ty::FnItem(FuncId::new(0))], false),
        FuncTy::unrecorded(vec![], vec![Ty::FnItem(FuncId::new(1))], false),
    ];
    m.functions = vec![
        Function::new(
            FuncId::new(0),
            "target_a",
            FuncTyId::new(0),
            BlockId::new(0),
        ),
        Function::new(
            FuncId::new(1),
            "target_b",
            FuncTyId::new(0),
            BlockId::new(0),
        ),
        returning(
            2,
            "return_a",
            1,
            Ty::FnItem(FuncId::new(0)),
            Constant::FnItem(FuncId::new(0)),
        ),
        returning(
            3,
            "return_b",
            2,
            Ty::FnItem(FuncId::new(1)),
            Constant::FnItem(FuncId::new(1)),
        ),
    ];
    for (caller, target, name) in [(2, 0, "return_a"), (3, 1, "return_b")] {
        let actual = trust_ir::Interpreter::with_module(&m)
            .execute_func(FuncId::new(caller), vec![])
            .unwrap();
        assert!(
            matches!(actual.returns.as_slice(), [InterpretValue { kind: InterpretValueKind::FnItem(id), .. }] if *id == FuncId::new(target))
        );
        assert!(
            matches!(interpret(&m, name, &[]), Err(InterpreterError::Unsupported(reason)) if reason.contains("FnItem"))
        );
    }
}

#[test]
fn ordinary_diagnostic_scalar_interpretation_remains_executable() {
    let mut m = Module::new("ordinary_scalar");
    m.func_types
        .push(FuncTy::unrecorded(vec![], vec![Ty::I64], false));
    m.functions
        .push(returning(0, "scalar", 0, Ty::I64, Constant::Int(123)));
    assert!(matches!(
        interpret(&m, "scalar", &[]).unwrap().as_slice(),
        [InterpreterValue::Int(123)]
    ));
    // Even an unused type records unsupported nominal semantics in this module.
    m.types.push(Ty::FnItem(FuncId::new(0)));
    assert!(
        matches!(interpret(&m, "scalar", &[]), Err(InterpreterError::Unsupported(reason)) if reason.contains("FnItem"))
    );
}
