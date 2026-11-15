// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Source-signature controls for the production unreachable terminator.
//! These exercise canonical admission and module-to-LIR lowering, not native
//! execution or a MIR/source-refinement proof. I32/I64 cases are word-type
//! coverage, not qualification of a 32-bit target.

use super::lower_unreachable_terminator;
use trust_cg_lower::adapter::{AdapterError, validate_codegen_prerequisites};
use trust_cg_lower::instructions::Opcode;
use trust_ir::{
    Block, BlockId, Constant, Endianness, FuncId, FuncTy, Function, Inst, InstrNode, Module,
    StructPassingPolicy, TargetInfo, Ty, ValueId,
};

fn fixture(name: &str, signature: FuncTy) -> Module {
    let mut module = Module::new(name);
    // The explicit source target descriptor supplies the aggregate convention
    // the shared floor requires. No object is emitted or executed by this test.
    module.target_info = Some(TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: Some("aapcs64".into()),
        struct_passing: StructPassingPolicy::NativeC,
    });
    let id = module
        .add_func_type(signature.clone())
        .expect("Module::add_func_type: test fixture");
    let mut function = Function::new(FuncId::new(0), name, id, BlockId::new(0));
    let mut block = Block::new(BlockId::new(0));
    block.params = signature
        .params
        .into_iter()
        .enumerate()
        .map(|(index, ty)| (ValueId::new(41 + index as u32), ty))
        .collect();
    lower_unreachable_terminator(&mut block).unwrap();
    function.blocks.push(block);
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
    module
}

fn signature(params: Vec<Ty>, returns: Vec<Ty>) -> FuncTy {
    FuncTy {
        params,
        returns,
        // Keep the fixture's legacy ABI state explicit. These controls never
        // invent a rustc FnAbi descriptor from source type/size heuristics.
        abi: None,
        is_vararg: false,
    }
}

#[test]
fn original_void_scalar_pointer_pair_aggregate_and_hidden_buffer_signatures_keep_one_trap() {
    let cases = [
        ("void", signature(vec![], vec![])),
        ("boolean", signature(vec![], vec![Ty::Bool])),
        ("signed_word32", signature(vec![], vec![Ty::I32])),
        ("unsigned_word32", signature(vec![], vec![Ty::U32])),
        ("signed_word64", signature(vec![], vec![Ty::I64])),
        ("unsigned_word64", signature(vec![], vec![Ty::U64])),
        ("float32", signature(vec![], vec![Ty::F32])),
        ("float64", signature(vec![], vec![Ty::F64])),
        ("address", signature(vec![], vec![Ty::Ptr])),
        (
            "raw_const_address",
            signature(vec![], vec![Ty::PtrConst(Box::new(Ty::U8))]),
        ),
        (
            "raw_mut_address",
            signature(vec![], vec![Ty::PtrMut(Box::new(Ty::U8))]),
        ),
        (
            "shared_reference",
            signature(vec![], vec![Ty::Ref(Box::new(Ty::U64))]),
        ),
        (
            "mutable_reference",
            signature(vec![], vec![Ty::RefMut(Box::new(Ty::U64))]),
        ),
        ("pair_return", signature(vec![], vec![Ty::I64, Ty::F64])),
        (
            "memory_aggregate_return",
            signature(vec![], vec![Ty::Tuple(vec![Ty::I64; 5])]),
        ),
        // This is the original pre-lowered void + leading buffer parameter
        // style, not a newly inferred or manufactured sret classification.
        ("hidden_buffer_void", signature(vec![Ty::Ptr], vec![])),
    ];
    assert_eq!(cases.len(), 16);
    let mut executed = Vec::new();
    for (name, original) in cases {
        let module = fixture(name, original.clone());
        assert_eq!(module.func_types.len(), 1);
        assert_eq!(module.func_types[0], original, "{name}: source ABI/type");
        let function = &module.functions[0];
        let block = &function.blocks[0];
        assert_eq!(function.blocks.len(), 1);
        assert_eq!(
            block
                .params
                .iter()
                .map(|(_, ty)| ty.clone())
                .collect::<Vec<_>>(),
            original.params
        );
        assert_eq!(
            block.body.len(),
            1,
            "{name}: no synthetic return preparation"
        );
        let node = &block.body[0];
        assert_eq!(node.inst, Inst::Unreachable);
        assert!(node.results.is_empty());
        assert!(node.proofs.is_empty());

        let source_bytes = serde_json::to_vec(&module).unwrap();
        validate_codegen_prerequisites(&module)
            .unwrap_or_else(|error| panic!("{name}: original source admission: {error:?}"));
        let lowered = permit_translate_module(&module)
            .unwrap_or_else(|error| panic!("{name}: actual module-to-LIR route: {error:?}"));
        assert_eq!(
            lowered.len(),
            1,
            "{name}: every original function translated"
        );
        let lir = &lowered[0].0;
        assert_eq!(lir.name, name);
        assert_eq!(lir.blocks.len(), 1);
        assert!(
            lir.stack_slots.is_empty(),
            "{name}: no fabricated return home"
        );
        let entry = &lir.blocks[&lir.entry_block];
        assert_eq!(entry.params.len(), original.params.len());
        assert_eq!(entry.instructions.len(), 1, "{name}: only the real trap");
        let trap = &entry.instructions[0];
        assert!(matches!(trap.opcode, Opcode::Trap));
        assert!(trap.args.is_empty());
        assert!(trap.results.is_empty());
        assert_eq!(
            serde_json::to_vec(&module).unwrap(),
            source_bytes,
            "{name}: complete source module remains unchanged"
        );
        executed.push(name);
    }
    assert_eq!(executed.len(), 16);
    assert_eq!(
        executed
            .iter()
            .copied()
            .collect::<std::collections::HashSet<_>>()
            .len(),
        16
    );
    assert!(executed.contains(&"memory_aggregate_return"));
    assert!(executed.contains(&"hidden_buffer_void"));
}

#[test]
fn real_returns_still_refuse_wrong_arity_against_the_original_full_signature() {
    let cases = [
        (
            "missing_word",
            signature(vec![], vec![Ty::I64]),
            vec![],
            0,
            1,
        ),
        (
            "missing_pair",
            signature(vec![Ty::I64], vec![Ty::I64, Ty::F64]),
            vec![ValueId::new(41)],
            1,
            2,
        ),
        (
            "extra_void",
            signature(vec![Ty::I64], vec![]),
            vec![ValueId::new(41)],
            1,
            0,
        ),
    ];
    let mut executed = 0;
    for (name, original, values, got, expected) in cases {
        let mut module = fixture(name, original.clone());
        module.functions[0].blocks[0].body[0].inst = Inst::Return { values };
        assert_eq!(module.func_types[0], original);
        // Compatibility prerequisites intentionally tolerate some structural
        // findings; the actual return-lowering gate must still refuse arity.
        let error = permit_translate_module(&module).unwrap_err();
        assert!(
            matches!(&error, AdapterError::UnsupportedInstruction(detail)
            if detail == &format!("Inst::Return arity mismatch: got {got}, expected {expected} from current function signature")),
            "{name}: {error:?}"
        );
        executed += 1;
    }
    assert_eq!(executed, 3);
}

#[test]
fn malformed_constants_before_unreachable_still_fail_the_canonical_typed_floor() {
    let cases = [
        ("invalid_boolean", Ty::Bool, Constant::Int(0)),
        ("out_of_range_byte", Ty::I8, Constant::Int(128)),
        (
            "invented_reference",
            Ty::Ref(Box::new(Ty::U8)),
            Constant::Int(0),
        ),
    ];
    let mut executed = 0;
    for (name, ty, value) in cases {
        let mut module = fixture(name, signature(vec![], vec![]));
        module.functions[0].blocks[0].body.insert(
            0,
            InstrNode::new(Inst::Const { ty, value }).with_result(ValueId::new(7)),
        );
        let error = validate_codegen_prerequisites(&module).unwrap_err();
        assert!(
            matches!(&error, AdapterError::TrustIrAdmissionRefused { error }
            if error.contains("const type mismatch") && error.contains("got int")),
            "{name}: {error:?}"
        );
        let lowered_error = permit_translate_module(&module).unwrap_err();
        assert!(
            matches!(&lowered_error, AdapterError::TrustIrAdmissionRefused { error }
            if error.contains("const type mismatch") && error.contains("got int")),
            "{name}: module route bypassed the typed floor: {lowered_error:?}"
        );
        executed += 1;
    }
    assert_eq!(executed, 3);
}

/// These fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Their translations state `Permit` explicitly, so
/// none passes, and no refusal is the license's, by accident.
fn permit_translate_module(
    module: &Module,
) -> Result<Vec<(trust_cg_lower::Function, trust_cg_lower::ProofContext)>, AdapterError> {
    trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        module,
        trust_cg_lower::GuardCarrierArch::default(),
        trust_cg_lower::TlsDialect::default(),
        &trust_cg_lower::CodegenLicensePolicy::default()
            .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit),
    )
}
