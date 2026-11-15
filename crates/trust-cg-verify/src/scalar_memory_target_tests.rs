// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Ordinary ORIGINAL Core → MachIR/final-word finite controls. Concrete
//! equation expansion is not solver replay, permission or native authority.

use super::scalar_memory_tests::{Substitutions, evaluate, expand_equations};
use super::*;
use crate::smt::EvalEnv;
use crate::source_bound_frame::bind_scalar_memory_source;
use trust_cg_ir::regs::{W2, X0, X1, X2, X3, X30, XZR};
use trust_cg_ir::{AArch64Opcode as M, MachInst, MachOperand as O, PReg, Signature, Type};
use trust_ir::{
    BinOp, Block, BlockId, CallingConv, Constant, Endianness, FuncId, FuncTy, Function, Inst,
    InstrNode, Module, TargetInfo, Ty, ValueId,
};

fn v(i: u32) -> ValueId {
    ValueId::new(i)
}
fn node(inst: Inst, result: Option<u32>) -> InstrNode {
    let mut node = InstrNode::new(inst);
    node.results.extend(result.map(v));
    node
}

fn original() -> Module {
    let mut module = Module::new("ordinary_scalar_target_consumer");
    module.target_info = Some(TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    });
    let signature = module
        .add_func_type(FuncTy {
            params: vec![Ty::Ptr; 2],
            returns: vec![Ty::U64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = Function::new(
        FuncId::new(0),
        "ordinary_scalar_target_consumer",
        signature,
        BlockId::new(0),
    );
    function.calling_conv = CallingConv::C;
    let mut block = Block::new(BlockId::new(0));
    block.params = vec![(v(0), Ty::Ptr), (v(1), Ty::Ptr)];
    block.body = vec![
        node(
            Inst::Const {
                ty: Ty::U64,
                value: Constant::Int(1),
            },
            Some(2),
        ),
        node(
            Inst::Load {
                ty: Ty::U64,
                ptr: v(0),
                volatile: false,
                align: Some(8),
            },
            Some(3),
        ),
        node(
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::U64,
                lhs: v(3),
                rhs: v(2),
            },
            Some(4),
        ),
        node(
            Inst::Store {
                ty: Ty::U64,
                ptr: v(1),
                value: v(4),
                volatile: false,
                align: Some(8),
            },
            None,
        ),
        node(
            Inst::Load {
                ty: Ty::U64,
                ptr: v(0),
                volatile: false,
                align: Some(8),
            },
            Some(5),
        ),
        node(Inst::Return { values: vec![v(5)] }, None),
    ];
    function.blocks.push(block);
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
    module
}

fn p(reg: PReg) -> O {
    O::PReg(reg)
}
fn machine(module: &Module, body: Vec<MachInst>) -> MachFunction {
    let mut machine = MachFunction::new(
        module.functions[0].name.clone(),
        Signature::new(vec![Type::I64; 2], vec![Type::I64]),
    );
    let mut ret = MachInst::new(M::Ret, vec![p(X30)]);
    ret.implicit_uses = &[X0];
    for inst in body.into_iter().chain([ret]) {
        let id = machine.push_inst(inst);
        machine.append_inst(machine.entry, id);
    }
    machine
}
fn body(narrow: bool) -> Vec<MachInst> {
    vec![
        MachInst::new(M::LdrRI, vec![p(X2), p(X0), O::Imm(0)]),
        MachInst::new(M::AddRI, vec![p(X2), p(X2), O::Imm(1)]),
        MachInst::new(
            M::StrRI,
            vec![p(if narrow { W2 } else { X2 }), p(X1), O::Imm(0)],
        ),
        MachInst::new(M::LdrRI, vec![p(X0), p(X0), O::Imm(0)]),
    ]
}
fn words(narrow: bool) -> Vec<u32> {
    // Captured architectural fields, independently decoded; no encoder hints.
    vec![
        0xf9400002,
        0x91000442,
        if narrow { 0xb9000022 } else { 0xf9000022 },
        0xf9400000,
        0xd65f03c0,
    ]
}
fn bytes(words: &[u32]) -> Vec<u8> {
    words.iter().flat_map(|w| w.to_le_bytes()).collect()
}

const PARENT: u64 = 0x1000;
const OUTPUT: u64 = 0x2000;
const ORIGINAL: u64 = 0x0807_0605_0403_0201;
fn fixture(output: u64) -> (E, EvalEnv) {
    let mut memory = E::const_array(SmtSort::BitVec(64), E::bv_const(0xa5, 8));
    memory = encode_store_le(
        &memory,
        &E::bv_const(PARENT, 64),
        &E::bv_const(ORIGINAL, 64),
        8,
    );
    if output != PARENT {
        memory = encode_store_le(
            &memory,
            &E::bv_const(output, 64),
            &E::bv_const(0xe8e7_e6e5_e4e3_e2e1, 64),
            8,
        );
    }
    let mut env = EvalEnv::default();
    env.insert("abi_x0".into(), PARENT);
    env.insert("abi_x1".into(), output);
    env.insert("observe".into(), output);
    (memory, env)
}
fn substitutions(queries: &ScalarMemoryTargetQueries<'_>, memory: &E) -> Substitutions {
    let mut equations = queries.source().original_encoding_definitions().to_vec();
    equations.extend_from_slice(queries.encoding_definitions());
    expand_equations(&equations, memory)
}
fn holds(query: &ProofObligation, defs: &Substitutions, env: &EvalEnv) -> bool {
    assert!(
        query
            .preconditions
            .iter()
            .all(|p| evaluate(p, defs, env).as_bool()),
        "original geometry and complete semantic equations"
    );
    evaluate(&query.trust_ir_expr, defs, env) == evaluate(&query.aarch64_expr, defs, env)
}
fn all<'a>(queries: &'a ScalarMemoryTargetQueries<'_>) -> Vec<&'a ProofObligation> {
    queries
        .return_obligations()
        .iter()
        .chain(queries.memory_obligations())
        .chain(queries.read_obligations())
        .chain(queries.write_obligations())
        .collect()
}

#[test]
fn scalar_target_ordinary_consumer_closes_both_endpoints_and_keeps_only_original_premises() {
    let module = original();
    let lir = trust_cg_lower::translate_function_with_license(
        &module.functions[0],
        &module,
        &crate::license_test_support::permit_unlicensed(),
    )
    .unwrap()
    .0;
    let source = bind_scalar_memory_source(&module, 0, &lir).unwrap();
    let machine = machine(&module, body(false));
    let bytes = bytes(&words(false));
    for queries in [
        bind_scalar_memory_machine(&source, &machine).unwrap(),
        bind_scalar_memory_bytes(&source, &bytes).unwrap(),
    ] {
        assert!(std::ptr::eq(queries.source(), &source));
        assert_eq!(queries.reads().len(), 2);
        assert_eq!(queries.writes().len(), 1);
        assert_eq!(queries.return_obligations().len(), 1);
        assert_eq!(queries.memory_obligations().len(), 1);
        let expected_premises = source
            .source_geometry()
            .iter()
            .chain(source.original_encoding_definitions())
            .chain(queries.encoding_definitions())
            .cloned()
            .collect::<Vec<_>>();
        for q in all(&queries) {
            assert_eq!(q.preconditions, expected_premises);
            assert_eq!(q.inputs.iter().filter(|(n, _)| n == "observe").count(), 1);
            assert!(q.inputs.contains(&("entry_x2".into(), 64)));
            assert!(!q.inputs.iter().any(|(n, _)| n == "abi_x2"));
        }
        for output in [PARENT, OUTPUT] {
            let (memory, mut env) = fixture(output);
            let defs = substitutions(&queries, &memory);
            for observe in [
                PARENT - 1,
                PARENT,
                PARENT + 7,
                PARENT + 8,
                output - 1,
                output,
                output + 3,
                output + 4,
                output + 7,
                output + 8,
                0x7000,
            ] {
                env.insert("observe".into(), observe);
                assert!(all(&queries).into_iter().all(|q| holds(q, &defs, &env)));
            }
        }
    }
    let mut wrong_identity = machine.clone();
    wrong_identity.name.push_str("_different");
    assert!(matches!(
        bind_scalar_memory_machine(&source, &wrong_identity),
        Err(ReadOnlyTargetError::Machine(_))
    ));
    let mut wrong_signature = machine.clone();
    wrong_signature.signature = Signature::new(vec![Type::I64; 3], vec![Type::I64]);
    assert!(matches!(
        bind_scalar_memory_machine(&source, &wrong_signature),
        Err(ReadOnlyTargetError::Machine(_))
    ));
}

#[test]
fn scalar_target_stale_alias_load_is_falsified_despite_equal_final_memory() {
    let module = original();
    let lir = trust_cg_lower::translate_function_with_license(
        &module.functions[0],
        &module,
        &crate::license_test_support::permit_unlicensed(),
    )
    .unwrap()
    .0;
    let source = bind_scalar_memory_source(&module, 0, &lir).unwrap();
    let mut stale_body = body(false);
    stale_body.swap(2, 3);
    let target = machine(&module, stale_body);
    let mut stale_words = words(false);
    stale_words.swap(2, 3);
    let bytes = bytes(&stale_words);
    let (memory, env) = fixture(PARENT);
    for queries in [
        bind_scalar_memory_machine(&source, &target).unwrap(),
        bind_scalar_memory_bytes(&source, &bytes).unwrap(),
    ] {
        let defs = substitutions(&queries, &memory);
        assert!(!holds(&queries.return_obligations()[0], &defs, &env));
        assert!(
            queries
                .memory_obligations()
                .iter()
                .all(|q| holds(q, &defs, &env))
        );
    }
}

#[test]
fn scalar_target_narrow_store_preserves_neighbours_but_cannot_hide_missing_source_bytes() {
    let module = original();
    let lir = trust_cg_lower::translate_function_with_license(
        &module.functions[0],
        &module,
        &crate::license_test_support::permit_unlicensed(),
    )
    .unwrap()
    .0;
    let source = bind_scalar_memory_source(&module, 0, &lir).unwrap();
    let target = machine(&module, body(true));
    let bytes = bytes(&words(true));
    let (memory, mut env) = fixture(OUTPUT);
    for queries in [
        bind_scalar_memory_machine(&source, &target).unwrap(),
        bind_scalar_memory_bytes(&source, &bytes).unwrap(),
    ] {
        assert_eq!(queries.writes()[0].byte_width, 4);
        let defs = substitutions(&queries, &memory);
        assert!(
            queries
                .return_obligations()
                .iter()
                .all(|q| holds(q, &defs, &env))
        );
        env.insert("observe".into(), OUTPUT + 7);
        assert!(!holds(&queries.memory_obligations()[0], &defs, &env));
        for observe in [OUTPUT - 1, OUTPUT + 8] {
            env.insert("observe".into(), observe);
            assert!(holds(&queries.memory_obligations()[0], &defs, &env));
        }
    }
}

#[test]
fn scalar_target_dead_read_and_write_restore_keep_separate_demands() {
    let module = original();
    let lir = trust_cg_lower::translate_function_with_license(
        &module.functions[0],
        &module,
        &crate::license_test_support::permit_unlicensed(),
    )
    .unwrap()
    .0;
    let source = bind_scalar_memory_source(&module, 0, &lir).unwrap();
    let mut extra_body = body(false);
    extra_body.extend([
        MachInst::new(M::LdrRI, vec![p(X3), p(X1), O::Imm(8)]),
        MachInst::new(M::StrRI, vec![p(XZR), p(X1), O::Imm(8)]),
        MachInst::new(M::StrRI, vec![p(X3), p(X1), O::Imm(8)]),
    ]);
    let target = machine(&module, extra_body);
    let mut extra_words = words(false);
    extra_words.splice(4..4, [0xf9400423, 0xf900043f, 0xf9000423]);
    let bytes = bytes(&extra_words);
    let (memory, mut env) = fixture(OUTPUT);
    env.insert("observe".into(), OUTPUT + 8);
    for queries in [
        bind_scalar_memory_machine(&source, &target).unwrap(),
        bind_scalar_memory_bytes(&source, &bytes).unwrap(),
    ] {
        assert_eq!(queries.reads().len(), 3);
        assert_eq!(queries.writes().len(), 3);
        let defs = substitutions(&queries, &memory);
        assert!(
            queries
                .return_obligations()
                .iter()
                .chain(queries.memory_obligations())
                .all(|q| holds(q, &defs, &env))
        );
        assert!(!holds(&queries.read_obligations()[2], &defs, &env));
        assert!(!holds(&queries.write_obligations()[1], &defs, &env));
        assert!(!holds(&queries.write_obligations()[2], &defs, &env));
    }
}

#[test]
fn immutable_memory_versions_fork_and_snapshot_by_one_pointer_handle() {
    assert_eq!(
        std::mem::size_of::<Option<Arc<Term>>>(),
        std::mem::size_of::<usize>()
    );
    assert!(std::mem::size_of::<Option<Arc<Term>>>() < std::mem::size_of::<Option<Term>>());
    let steps = [
        Step::Branch {
            condition: E::BoolConst(true),
            taken: 3,
        },
        Step::Scalar {
            destination: Some(0),
            value: E::bv_const(0, 64),
            flags: None,
        },
        Step::Return,
        Step::Scalar {
            destination: Some(0),
            value: E::bv_const(1, 64),
            flags: None,
        },
        Step::Return,
    ];
    let observation = observe_profile_at(
        &steps,
        &[("abi_x0".into(), 64)],
        1,
        Some(Stage::Machine),
        &mut 0,
    )
    .unwrap();
    assert_eq!(
        observation.memories.len(),
        2,
        "both paths, even constant-untaken"
    );
    assert!(
        Arc::ptr_eq(&observation.memories[0], &observation.memories[1]),
        "unchanged memory shares the exact version, not another cloned term"
    );
    println!(
        "A64_TARGET_MEMORY_VERSION_STORAGE optional_handle_bytes={} optional_term_bytes={} shared_return_snapshots=2 physical_rss_measurement=none",
        std::mem::size_of::<Option<Arc<Term>>>(),
        std::mem::size_of::<Option<Term>>()
    );
}
