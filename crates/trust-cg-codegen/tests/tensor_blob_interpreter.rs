// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0
//! Unsupported tensor inputs must not become scalar values or erased tables.
use trust_cg_codegen::interpreter::{InterpreterError, InterpreterValue, interpret};
use trust_ir::{Constant, Inst, Ty};
use trust_ir_build::ModuleBuilder;

fn scalar() -> trust_ir::Module {
    let mut builder = ModuleBuilder::new("scalar_blob_control");
    let signature = builder.add_func_type(vec![], vec![Ty::I64]);
    let mut function = builder.function("answer", signature);
    let entry = function.create_block();
    function.switch_to_block(entry);
    let value = function.iconst(Ty::I64, 42);
    function.ret(vec![value]);
    function.build();
    builder.build().unwrap()
}
fn refused(module: &trust_ir::Module, name: &str) {
    match interpret(module, "answer", &[]) {
        Err(InterpreterError::Unsupported(reason)) => assert!(reason.contains(name), "{reason}"),
        other => panic!("unsupported tensor input must refuse: {other:?}"),
    }
}
#[test]
fn tensor_weight_tables_and_nested_constants_refuse_before_scalar_interpretation() {
    let plain = scalar();
    let result = interpret(&plain, "answer", &[]).unwrap();
    assert!(matches!(result.as_slice(), [InterpreterValue::Int(42)]));
    let mut table = plain.clone();
    table
        .blobs
        .push(trust_ir::blob::Blob::new(vec![1, 2, 3, 4]));
    refused(&table, "Module::blobs");
    let blob = Constant::TensorBlob {
        digest: trust_ir::blob::BlobDigest::of(&[1, 2, 3, 4]),
        dims: vec![1],
    };
    for value in [
        blob.clone(),
        Constant::Aggregate(vec![Constant::Int(0), blob.clone()]),
        Constant::Record(vec![("weight".into(), blob)]),
    ] {
        // This deliberately malformed scalar spelling exercises the simplified
        // interpreter's own defense; it must not return an Undef placeholder.
        let mut module = plain.clone();
        module.functions[0].blocks[0].body[0].inst = Inst::Const { ty: Ty::I64, value };
        refused(&module, "Constant::TensorBlob");
    }
}
