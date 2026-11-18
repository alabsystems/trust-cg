// Copyright 2026 Andrew Yates | Apache-2.0
//! Concrete pending-query controls. The test-only unlicensed lowering helper
//! supplies diagnostic LIR data, never a body license or native entry.

use super::tests::{evaluate, expand};
use super::*;
use crate::smt::EvalEnv;
use trust_ir::{
    Block, BlockId, CallingConv, FuncId, FuncTy, Function as CoreFunction, Inst, InstrNode,
    TargetInfo, Ty, ValueId,
};

fn module() -> Module {
    let mut m = Module::new("ordinary_void_memory");
    m.target_info = Some(TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: Some("darwinpcs".into()),
        struct_passing: Default::default(),
    });
    let signature = m
        .add_func_type(FuncTy {
            params: vec![Ty::Ptr, Ty::Ptr],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .unwrap();
    let mut f = CoreFunction::new(FuncId::new(0), "void_copy", signature, BlockId::new(0));
    f.calling_conv = CallingConv::C;
    let mut block = Block::new(f.entry);
    block.params = vec![(ValueId::new(0), Ty::Ptr), (ValueId::new(1), Ty::Ptr)];
    let mut load = InstrNode::new(Inst::Load {
        ty: Ty::U64,
        ptr: ValueId::new(0),
        volatile: false,
        align: Some(8),
    });
    load.results.push(ValueId::new(2));
    block.body = vec![
        load,
        InstrNode::new(Inst::Store {
            ty: Ty::U64,
            ptr: ValueId::new(1),
            value: ValueId::new(2),
            volatile: false,
            align: Some(8),
        }),
        InstrNode::new(Inst::Return { values: vec![] }),
    ];
    f.blocks.push(block);
    m.functions.push(f);
    m
}
fn lowering(module: &Module) -> Function {
    trust_cg_lower::translate_function_with_license(
        &module.functions[0],
        module,
        &crate::license_test_support::permit_unlicensed(),
    )
    .unwrap()
    .0
}
fn fixture() -> (E, EvalEnv) {
    let memory = encode_store_le(
        &E::const_array(SmtSort::BitVec(64), E::bv_const(0xa5, 8)),
        &E::bv_const(0x1000, 64),
        &E::bv_const(0x0807_0605_0403_0201, 64),
        8,
    );
    let mut environment = EvalEnv::default();
    environment.insert("abi_x0".into(), 0x1000);
    environment.insert("abi_x1".into(), 0x2000);
    environment.insert("observe".into(), 0x2000);
    (memory, environment)
}

#[test]
fn void_normal_return_is_boolean_and_complete_bytes_and_demands_still_agree() {
    let m = module();
    let lir = lowering(&m);
    assert!(
        bind_scalar_memory_source(&m, 0, &lir).is_err(),
        "void is not a scalar status result"
    );
    let queries = bind_void_memory_source(&m, 0, &lir).unwrap();
    assert_eq!(
        (queries.source_reads().len(), queries.source_writes().len()),
        (1, 1)
    );
    let (memory, mut environment) = fixture();
    let substitutions = expand(queries.inner.encoding_definitions(), &memory);
    for observer in [
        0x0fff, 0x1000, 0x1007, 0x1008, 0x1fff, 0x2000, 0x2007, 0x2008,
    ] {
        environment.insert("observe".into(), observer);
        for q in std::iter::once(queries.normal_return_obligation())
            .chain(std::iter::once(queries.memory_obligation()))
            .chain(queries.read_obligations())
            .chain(queries.write_obligations())
        {
            assert!(
                q.preconditions
                    .iter()
                    .all(|p| evaluate(p, &substitutions, &environment).as_bool())
            );
            assert_eq!(
                evaluate(&q.trust_ir_expr, &substitutions, &environment),
                evaluate(&q.aarch64_expr, &substitutions, &environment)
            );
        }
    }
    let normal = queries.normal_return_obligation();
    assert!(evaluate(&normal.trust_ir_expr, &substitutions, &environment).as_bool());
    assert!(evaluate(&normal.aarch64_expr, &substitutions, &environment).as_bool());
}

#[test]
fn changed_store_value_is_falsified_by_final_memory_even_with_same_void_return() {
    let m = module();
    let mut lir = lowering(&m);
    let first = lir
        .blocks
        .get_mut(&lir.entry_block)
        .unwrap()
        .instructions
        .first_mut()
        .unwrap();
    first.opcode = Opcode::Iconst {
        ty: LirType::I64,
        imm: 99,
    };
    first.args.clear();
    let queries = bind_void_memory_source(&m, 0, &lir).unwrap();
    let (memory, environment) = fixture();
    let substitutions = expand(queries.inner.encoding_definitions(), &memory);
    let normal = queries.normal_return_obligation();
    assert_eq!(
        evaluate(&normal.trust_ir_expr, &substitutions, &environment),
        evaluate(&normal.aarch64_expr, &substitutions, &environment)
    );
    let memory = queries.memory_obligation();
    assert_ne!(
        evaluate(&memory.trust_ir_expr, &substitutions, &environment),
        evaluate(&memory.aarch64_expr, &substitutions, &environment)
    );
}

#[test]
fn pointer_bits_keep_void_and_the_actual_pointer_store_type() {
    let mut m = module();
    if let Inst::Load { ty, .. } = &mut m.functions[0].blocks[0].body[0].inst {
        *ty = Ty::Ptr;
    }
    if let Inst::Store { ty, .. } = &mut m.functions[0].blocks[0].body[1].inst {
        *ty = Ty::Ptr;
    }
    let lir = lowering(&m);
    let queries = bind_void_memory_source(&m, 0, &lir).unwrap();
    let (memory, environment) = fixture();
    let substitutions = expand(queries.inner.encoding_definitions(), &memory);
    assert_eq!(queries.source_reads()[0].codec, ScalarMemoryCodec::Pointer);
    for q in [
        queries.normal_return_obligation(),
        queries.memory_obligation(),
    ] {
        assert_eq!(
            evaluate(&q.trust_ir_expr, &substitutions, &environment),
            evaluate(&q.aarch64_expr, &substitutions, &environment)
        );
    }
    assert!(bind_scalar_memory_source(&m, 0, &lir).is_err());
}

#[test]
fn wrong_return_signature_and_hidden_lir_return_value_refuse_before_query_execution() {
    let mut m = module();
    let mut lir = lowering(&m);
    m.func_types[0].returns = vec![Ty::U64];
    assert!(bind_void_memory_source(&m, 0, &lir).is_err());
    m.func_types[0].returns.clear();
    let returning = lir
        .blocks
        .get_mut(&lir.entry_block)
        .unwrap()
        .instructions
        .last_mut()
        .unwrap();
    returning.args.push(trust_cg_lower::instructions::Value(2));
    assert!(bind_void_memory_source(&m, 0, &lir).is_err());
    assert!(bind_scalar_memory_source(&m, 0, &lir).is_err());
}
