// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Concrete controls for unresolved original-Core/LIR queries. Evaluating a
//! finite array fixture is NOT independent proof replay or caller-memory,
//! frame, machine, native execution or publication authority.

use super::*;
use crate::memory_proofs::encode_store_le;
use crate::smt::{EvalResult, SmtSort};
use std::convert::Infallible;
use trust_cg_lower::adapter::ProofContext as LoweringProofContext;
use trust_cg_lower::instructions::{Block as LirBlock, Instruction, Value as LirValue};
use trust_ir::{
    BinOp, Block as CoreBlock, BlockId, BodyGate, Constant, FuncId, FuncTy, ICmpOp, Inst,
    InstrNode, ProofAnnotation, TargetInfo, Ty, ValueId,
};

const YES: u64 = 1 << 32;
const NO: u64 = 0;
const BAD: u64 = (17 << 32) | 4;

fn v(id: u32) -> ValueId {
    ValueId::new(id)
}
fn n(inst: Inst, result: Option<u32>) -> InstrNode {
    let mut node = InstrNode::new(inst);
    node.results.extend(result.map(v));
    node
}
fn literal(id: u32, ty: Ty, value: u64) -> InstrNode {
    n(
        Inst::Const {
            ty,
            value: Constant::Int(i128::from(value)),
        },
        Some(id),
    )
}
fn gep(id: u32, base: u32) -> InstrNode {
    n(
        Inst::GEP {
            pointee_ty: Ty::U8,
            base: v(base),
            indices: vec![v(4)],
            inbounds: false,
        },
        Some(id),
    )
}
fn load(id: u32, ty: Ty, address: u32) -> InstrNode {
    n(
        Inst::Load {
            ty,
            ptr: v(address),
            volatile: false,
            align: Some(8),
        },
        Some(id),
    )
}
fn binary(id: u32, op: BinOp, a: u32, b: u32) -> InstrNode {
    n(
        Inst::BinOp {
            op,
            ty: Ty::I64,
            lhs: v(a),
            rhs: v(b),
        },
        Some(id),
    )
}
fn compare(id: u32, op: ICmpOp, a: u32, b: u32) -> InstrNode {
    n(
        Inst::ICmp {
            op,
            ty: Ty::I64,
            lhs: v(a),
            rhs: v(b),
        },
        Some(id),
    )
}
fn branch(condition: u32, yes: u32, no: u32) -> InstrNode {
    n(
        Inst::CondBr {
            cond: v(condition),
            then_target: BlockId::new(yes),
            then_args: vec![],
            else_target: BlockId::new(no),
            else_args: vec![],
        },
        None,
    )
}

// ctx+8 yields a POINTER, not an independently trusted pool capability.
// Entry reads the parent tag before the pool read; both status forks are real.
fn fixture(arity: usize) -> Module {
    let mut module = Module::new("read_only_queries");
    module.target_info = Some(TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    });
    let signature = module
        .add_func_type(FuncTy {
            params: vec![Ty::Ptr; arity],
            returns: vec![Ty::U64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = trust_ir::Function::new(
        FuncId::new(7),
        "read_only_predicate",
        signature,
        BlockId::new(0),
    );
    let mut entry = CoreBlock::new(BlockId::new(0));
    entry.params = (0..arity).map(|id| (v(id as u32), Ty::Ptr)).collect();
    entry.body = vec![
        literal(4, Ty::I64, 8),
        gep(5, 0),
        load(6, Ty::Ptr, 5),
        load(7, Ty::I64, 1),
        literal(8, Ty::I64, 7),
        literal(9, Ty::I64, 3),
        n(
            Inst::Const {
                ty: Ty::Bool,
                value: Constant::Bool(false),
            },
            Some(10),
        ),
        binary(11, BinOp::And, 7, 8),
        compare(12, ICmpOp::Eq, 11, 9),
        branch(12, 1, 4),
    ];
    let mut body = CoreBlock::new(BlockId::new(1));
    body.body = vec![
        gep(13, 6),
        load(14, Ty::I64, 13),
        binary(15, BinOp::AShr, 7, 9),
        binary(16, BinOp::AShr, 14, 9),
        binary(17, BinOp::And, 14, 8),
        compare(18, ICmpOp::Eq, 17, 9),
        compare(19, ICmpOp::Slt, 15, 16),
        n(
            Inst::Select {
                ty: Ty::Bool,
                cond: v(18),
                then_val: v(19),
                else_val: v(10),
            },
            Some(20),
        ),
        branch(20, 2, 3),
    ];
    function.blocks = vec![entry, body];
    for (block, result, status) in [(2, 21, YES), (3, 22, NO), (4, 23, BAD)] {
        let mut exit = CoreBlock::new(BlockId::new(block));
        exit.body = vec![
            literal(result, Ty::U64, status),
            n(
                Inst::Return {
                    values: vec![v(result)],
                },
                None,
            ),
        ];
        function.blocks.push(exit);
    }
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
    module
}

fn lower(module: &Module) -> (Function, LoweringProofContext) {
    trust_cg_lower::translate_function_with_license(
        &module.functions[0],
        module,
        &crate::license_test_support::permit_unlicensed(),
    )
    .expect("real original-Core adapter")
}
fn coded(value: i64) -> u64 {
    (value as u64).wrapping_shl(3) | 3
}
struct Sample {
    memory: E,
    env: HashMap<String, u64>,
    expected: u64,
}
fn sample(ctx: u64, parent: u64, pool: u64, a: u64, b: u64) -> Sample {
    let mut memory = E::const_array(SmtSort::BitVec(64), E::bv_const(0, 8));
    for (address, value) in [(ctx + 8, pool), (parent, a), (pool + 8, b)] {
        memory = encode_store_le(
            &memory,
            &E::bv_const(address, 64),
            &E::bv_const(value, 64),
            8,
        );
    }
    let expected = if a & 7 != 3 {
        BAD
    } else if b & 7 == 3 && (a as i64 >> 3) < (b as i64 >> 3) {
        YES
    } else {
        NO
    };
    Sample {
        memory,
        env: [
            ("abi_x0".into(), ctx),
            ("abi_x1".into(), parent),
            ("abi_x2".into(), 1024),
            ("abi_x3".into(), 2048),
        ]
        .into(),
        expected,
    }
}

pub(super) fn instantiate_memory(expr: &E, memory: &E) -> E {
    expr.try_rewrite_dag(&mut |node| -> Result<Option<E>, Infallible> {
        Ok(match node {
            E::UF {
                name,
                args,
                ret_sort,
            } if name == "entry_memory" && args.is_empty() && *ret_sort == memory_sort() => {
                Some(memory.clone())
            }
            _ => None,
        })
    })
    .unwrap()
    .unwrap_or_else(|| expr.clone())
}
fn eval(expr: &E, sample: &Sample) -> EvalResult {
    evaluate_memory(expr, &sample.memory, &sample.env)
}
pub(super) fn evaluate_memory(expr: &E, memory: &E, env: &HashMap<String, u64>) -> EvalResult {
    instantiate_memory(expr, memory)
        .try_eval(env)
        .expect("fully instantiated query")
}
fn endpoints(obligation: &ProofObligation, sample: &Sample) -> (EvalResult, EvalResult) {
    assert!(
        obligation
            .preconditions
            .iter()
            .all(|p| eval(p, sample).as_bool()),
        "source geometry must hold for a counterexample"
    );
    (
        eval(&obligation.trust_ir_expr, sample),
        eval(&obligation.aarch64_expr, sample),
    )
}
fn agrees(queries: &ReadOnlySourceQueries<'_>, sample: &Sample) {
    assert_eq!(
        endpoints(queries.return_obligation(), sample),
        (
            EvalResult::Bv(sample.expected),
            EvalResult::Bv(sample.expected)
        )
    );
    for obligation in queries.load_obligations() {
        assert_eq!(
            endpoints(obligation, sample),
            (EvalResult::Bool(true), EvalResult::Bool(true))
        );
    }
}
fn counterexample(queries: &ReadOnlySourceQueries<'_>, sample: &Sample) {
    let (source, target) = endpoints(queries.return_obligation(), sample);
    assert_eq!(source, EvalResult::Bv(sample.expected));
    assert!(
        source != target
            || queries.load_obligations().iter().any(|o| {
                let (source, target) = endpoints(o, sample);
                source != target
            }),
        "mutation retained no concrete return or guarded-load counterexample"
    );
}
#[track_caller]
fn find(
    lir: &Function,
    predicate: impl Fn(&Opcode) -> bool,
    occurrence: usize,
) -> (LirBlock, usize) {
    let mut blocks: Vec<_> = lir.blocks.keys().copied().collect();
    blocks.sort_unstable();
    blocks
        .into_iter()
        .flat_map(|block| {
            lir.blocks[&block]
                .instructions
                .iter()
                .enumerate()
                .filter_map(|(i, n)| predicate(&n.opcode).then_some((block, i)))
                .collect::<Vec<_>>()
        })
        .nth(occurrence)
        .unwrap_or_else(|| {
            panic!("missing actual adapter operation occurrence {occurrence}; LIR={lir:#?}")
        })
}
fn fresh(lir: &Function) -> LirValue {
    LirValue(
        lir.blocks
            .values()
            .flat_map(|b| {
                b.params.iter().map(|(v, _)| v.0).chain(
                    b.instructions
                        .iter()
                        .flat_map(|n| n.results.iter().map(|v| v.0)),
                )
            })
            .max()
            .unwrap()
            + 1,
    )
}
fn source_refuses(module: &Module, lir: &Function) {
    match bind_read_only_source(module, 0, lir) {
        Err(ReadOnlySourceError::Source(_)) => {}
        Err(error) => panic!("original source must refuse before the lowering: {error}"),
        Ok(_) => panic!("malformed or unsupported original source admitted"),
    }
}

#[test]
fn real_adapter_queries_keep_exact_inputs_arbitrary_byte_memory_and_full_status() {
    for arity in [2, 4] {
        let module = fixture(arity);
        let (lir, proof_context) = lower(&module);
        let queries = bind_read_only_source(&module, 0, &lir).expect("pending source/LIR queries");
        assert!(std::ptr::eq(queries.module(), &module));
        assert!(std::ptr::eq(queries.source(), &module.functions[0]));
        assert!(std::ptr::eq(queries.lir(), &lir));
        assert!(
            proof_context.function_proofs.is_empty()
                && proof_context.value_proofs.is_empty()
                && proof_context.synthesized_discharged.is_empty()
        );
        assert!(!crate::source_bound_frame::source_admits_frame_owner(&lir));
        assert_eq!(queries.return_obligation().inputs.len(), arity);
        assert_eq!(queries.read_requirements().len(), 3);
        assert_eq!(queries.lowering_reads().len(), 3);
        assert_eq!(queries.load_obligations().len(), 3);
        assert_eq!(
            queries.read_requirements()[0].value_type,
            ReadOnlyType::Pointer
        );
        assert!(
            queries
                .read_requirements()
                .iter()
                .all(|r| r.byte_width == 8 && r.alignment == 8)
        );
        for (a, b) in [
            (coded(-17), coded(2)),
            (coded(4), coded(-9)),
            (0, coded(5)),
            (coded(-1), 0),
        ] {
            agrees(&queries, &sample(64, 256, 512, a, b));
        }
        let query = crate::ay_bridge::generate_smt2_query_raw(
            queries.return_obligation(),
            &Default::default(),
        );
        assert!(query.contains("(declare-fun entry_memory () (Array (_ BitVec 64) (_ BitVec 8)))"));
        assert!(query.contains("select"));
    }
}

#[test]
fn read_aliases_and_short_circuit_demands_are_conditional_not_storage_authority() {
    let module = fixture(4);
    let (lir, _proof_context) = lower(&module);
    let queries = bind_read_only_source(&module, 0, &lir).unwrap();
    agrees(&queries, &sample(128, 128, 512, coded(-5), coded(1)));
    let invalid_tag = sample(64, 256, 0, 0, coded(2));
    agrees(&queries, &invalid_tag);
    assert_eq!(
        queries
            .read_requirements()
            .iter()
            .filter(|r| eval(&r.guard, &invalid_tag).as_bool())
            .count(),
        2
    );
    // Exact overlapping LOAD addresses: ctx+8 is also the parent word. A single
    // array makes both see the same pointer bits, whose tag disables the pool.
    let mut alias = sample(64, 72, 512, 512, coded(2));
    alias.expected = BAD;
    agrees(&queries, &alias);
    assert_eq!(
        eval(&queries.read_requirements()[0].address, &alias),
        eval(&queries.read_requirements()[1].address, &alias)
    );
    // Construction does not discharge even the explicit geometric premises.
    let unaligned = sample(65, 256, 512, coded(1), coded(2));
    assert!(
        queries
            .return_obligation()
            .preconditions
            .iter()
            .any(|p| !eval(p, &unaligned).as_bool())
    );
    let mut wrap = sample(64, 256, 512, coded(1), coded(2));
    wrap.env.insert("abi_x0".into(), u64::MAX - 7);
    assert!(
        queries
            .return_obligation()
            .preconditions
            .iter()
            .any(|p| !eval(p, &wrap).as_bool())
    );
}

#[test]
fn supported_target_mutations_retain_concrete_return_or_guarded_load_counterexamples() {
    let module = fixture(4);
    let (original, _proof_context) = lower(&module);
    for mutation in 0..7 {
        eprintln!(
            "READ_ONLY_TARGET_MUTATION={mutation}: {}",
            [
                "wrong load base",
                "wrong byte offset",
                "extra dead read",
                "hoisted conditional pool read",
                "inverted branch",
                "changed full-width status",
                "inverted Bool select",
            ][mutation]
        );
        let mut lir = original.clone();
        let mut input = sample(64, 256, 512, coded(-2), coded(7));
        match mutation {
            0 => {
                let (b, i) = find(&lir, |op| matches!(op, Opcode::Load { .. }), 1);
                let ctx = lir.blocks[&lir.entry_block].params[0].0;
                lir.blocks.get_mut(&b).unwrap().instructions[i].args[0] = ctx;
            }
            1 => {
                let (b, i) = find(&lir, |op| matches!(op, Opcode::Iconst { imm: 8, .. }), 0);
                lir.blocks.get_mut(&b).unwrap().instructions[i].opcode = Opcode::Iconst {
                    ty: LirType::I64,
                    imm: 16,
                };
            }
            2 => {
                let extra = Instruction {
                    opcode: Opcode::Load {
                        ty: LirType::I64,
                        align: Some(8),
                    },
                    args: vec![lir.blocks[&lir.entry_block].params[0].0],
                    results: vec![fresh(&lir)],
                };
                let entry = lir.blocks.get_mut(&lir.entry_block).unwrap();
                entry
                    .instructions
                    .insert(entry.instructions.len() - 1, extra);
            }
            3 => {
                let (b, load_i) = find(&lir, |op| matches!(op, Opcode::Load { .. }), 2);
                let address = lir.blocks[&b].instructions[load_i].args[0];
                // Follow this actual LOAD's byte-stride ArrayGep address
                // definition rather than assuming an opcode occurrence is
                // its producer. Preserve both original producer operands.
                let gep_i = lir.blocks[&b].instructions[..load_i]
                    .iter()
                    .position(|node| node.results.as_slice() == [address])
                    .expect("mutation3: actual pool LOAD address definition");
                assert_eq!(
                    lir.blocks[&b].instructions[gep_i].opcode,
                    Opcode::ArrayGep {
                        elem_ty: LirType::I8
                    },
                    "mutation3: actual byte-stride GEP producer"
                );
                let block = lir.blocks.get_mut(&b).unwrap();
                let load = block.instructions.remove(load_i);
                let gep = block.instructions.remove(gep_i);
                let entry = lir.blocks.get_mut(&lir.entry_block).unwrap();
                let at = entry.instructions.len() - 1;
                entry.instructions.splice(at..at, [gep, load]);
                input = sample(64, 256, 0, 0, coded(7));
            }
            4 => {
                let (b, i) = find(&lir, |op| matches!(op, Opcode::Brif { .. }), 0);
                if let Opcode::Brif {
                    then_dest,
                    else_dest,
                    ..
                } = &mut lir.blocks.get_mut(&b).unwrap().instructions[i].opcode
                {
                    std::mem::swap(then_dest, else_dest);
                }
            }
            5 => {
                let (b, i) = find(
                    &lir,
                    |op| matches!(op, Opcode::Iconst { imm, .. } if *imm as u64 == YES),
                    0,
                );
                lir.blocks.get_mut(&b).unwrap().instructions[i].opcode = Opcode::Iconst {
                    ty: LirType::I64,
                    imm: 0,
                };
            }
            6 => {
                let (b, i) = find(&lir, |op| matches!(op, Opcode::Select { .. }), 0);
                let cond = match &lir.blocks[&b].instructions[i].opcode {
                    Opcode::Select { cond: IntCC::Equal } => IntCC::NotEqual,
                    Opcode::Select {
                        cond: IntCC::NotEqual,
                    } => IntCC::Equal,
                    _ => unreachable!(),
                };
                lir.blocks.get_mut(&b).unwrap().instructions[i].opcode = Opcode::Select { cond };
            }
            _ => unreachable!(),
        }
        let queries = bind_read_only_source(&module, 0, &lir)
            .unwrap_or_else(|e| panic!("supported semantic mutation {mutation} refused: {e}"));
        counterexample(&queries, &input);
        if matches!(mutation, 2 | 3) {
            assert_eq!(
                endpoints(queries.return_obligation(), &input),
                (
                    EvalResult::Bv(input.expected),
                    EvalResult::Bv(input.expected)
                ),
                "dead/hoisted read must be caught by demands, not returned status"
            );
        }
    }
}

#[test]
fn lowering_width_hint_effect_and_identity_refusals_never_relabel_the_source() {
    let module = fixture(4);
    let (original, _proof_context) = lower(&module);
    for mutation in 0..9 {
        let mut lir = original.clone();
        let (b, i) = find(&lir, |op| matches!(op, Opcode::Load { .. }), 0);
        match mutation {
            0 => {
                lir.blocks.get_mut(&b).unwrap().instructions[i].opcode = Opcode::Load {
                    ty: LirType::I32,
                    align: Some(4),
                }
            }
            1 => {
                let (b, i) = find(&lir, |op| matches!(op, Opcode::Icmp { .. }), 0);
                lir.value_types
                    .insert(lir.blocks[&b].instructions[i].results[0], LirType::I64);
            }
            2 => {
                lir.value_types
                    .insert(lir.blocks[&b].instructions[i].results[0], LirType::B1);
            }
            3 => {
                lir.blocks.get_mut(&b).unwrap().instructions[i].opcode = Opcode::VolatileLoad {
                    ty: LirType::I64,
                    align: Some(8),
                }
            }
            4 => {
                lir.blocks.get_mut(&b).unwrap().instructions[i].opcode = Opcode::Store {
                    ty: LirType::I64,
                    align: Some(8),
                }
            }
            5 => {
                lir.blocks.get_mut(&b).unwrap().instructions[i].opcode = Opcode::Load {
                    ty: LirType::I64,
                    align: Some(3),
                }
            }
            6 => {
                lir.value_types.insert(LirValue(u32::MAX), LirType::I64);
            }
            7 => lir.name.push_str("_wrong"),
            8 => {
                let (b, i) = find(&lir, |op| matches!(op, Opcode::Brif { .. }), 0);
                let id = lir.blocks[&lir.entry_block].params[0].0;
                let node = &mut lir.blocks.get_mut(&b).unwrap().instructions[i];
                if let Opcode::Brif { cond, .. } = &mut node.opcode {
                    *cond = id;
                }
                node.args[0] = id;
            }
            _ => unreachable!(),
        }
        match bind_read_only_source(&module, 0, &lir) {
            Err(ReadOnlySourceError::Lowering(_)) => {}
            Err(e) => panic!("target mutation {mutation} must remain a lowering refusal: {e}"),
            Ok(_) => panic!("target shape mutation {mutation} admitted"),
        }
    }
}

#[test]
fn original_types_ssa_effects_and_proof_metadata_refuse_even_on_untaken_paths() {
    let original = fixture(4);
    let (lir, _proof_context) = lower(&original);
    for mutation in 0..19 {
        let mut module = original.clone();
        let function = &mut module.functions[0];
        match mutation {
            0 => function.blocks[0].body[0].results[0] = v(0),
            1 => {
                function.blocks[0].body[7].inst = Inst::BinOp {
                    op: BinOp::And,
                    ty: Ty::I64,
                    lhs: v(15),
                    rhs: v(8),
                }
            }
            2 => {
                function.blocks[0].body[7].inst = Inst::BinOp {
                    op: BinOp::And,
                    ty: Ty::U64,
                    lhs: v(7),
                    rhs: v(8),
                }
            }
            3 => function.blocks[0].body[9] = branch(7, 1, 4),
            4 => function.blocks[0].body[2]
                .proofs
                .push(ProofAnnotation::Pure),
            5 => function.blocks[0].body[2].proof_context = Some(Default::default()),
            6 => function.proofs.push(ProofAnnotation::Pure),
            7 => function.summary = Some(Default::default()),
            8 => function.body_gate = Some(BodyGate::Ungated),
            9 => function.attrs.readonly = true,
            10 => module.func_types[0].params[0] = Ty::I64,
            11 => {
                function.blocks[1].body[1].inst = Inst::Load {
                    ty: Ty::I32,
                    ptr: v(13),
                    volatile: false,
                    align: Some(4),
                }
            }
            12 => {
                function.blocks[1].body[7].inst = Inst::Select {
                    ty: Ty::Bool,
                    cond: v(18),
                    then_val: v(19),
                    else_val: v(7),
                }
            }
            13 => {
                function.blocks[0].body[9] = branch(10, 1, 4); // false: poisoned arm still inspected
                function.blocks[1].body[1].inst = Inst::Load {
                    ty: Ty::I64,
                    ptr: v(13),
                    volatile: true,
                    align: Some(8),
                };
            }
            14 => {
                function.blocks[0].body[9] = branch(10, 1, 4);
                function.blocks[1].body[1] = n(
                    Inst::Store {
                        ty: Ty::I64,
                        ptr: v(13),
                        value: v(7),
                        volatile: false,
                        align: Some(8),
                    },
                    None,
                );
            }
            15 => {
                function.blocks[0].body[1].inst = Inst::GEP {
                    pointee_ty: Ty::U8,
                    base: v(0),
                    indices: vec![v(4)],
                    inbounds: true,
                }
            }
            16 => {
                function.blocks[2].body[0].inst = Inst::Const {
                    ty: Ty::U64,
                    value: Constant::Int(-1),
                }
            }
            17 => function.blocks[4].body[1].inst = Inst::Return { values: vec![v(7)] },
            18 => {
                function.blocks[2].params = vec![(v(24), Ty::U64)];
                if let Inst::CondBr { then_args, .. } = &mut function.blocks[1].body[8].inst {
                    *then_args = vec![v(7)];
                }
            }
            _ => unreachable!(),
        }
        source_refuses(&module, &lir);
    }
}

#[test]
fn bounded_gep_shift_and_preallocation_controls_fail_closed() {
    let original = fixture(4);
    let (lir, _proof_context) = lower(&original);
    for mutation in 0..8 {
        let mut module = original.clone();
        let function = &mut module.functions[0];
        match mutation {
            0 => function.blocks[0].body[0] = literal(4, Ty::I64, 4096),
            1 => function.blocks[1].body[2] = binary(15, BinOp::AShr, 7, 7),
            2 => function.blocks[0].body[5] = literal(9, Ty::I64, 64),
            3 => function.blocks[0].body[0].results.push(v(100)),
            4 => {
                if let Inst::GEP { indices, .. } = &mut function.blocks[0].body[1].inst {
                    indices.push(v(4));
                }
            }
            5 => function.blocks[0]
                .params
                .extend((100..105).map(|id| (v(id), Ty::Ptr))),
            6 => function
                .blocks
                .extend((5..17).map(|id| CoreBlock::new(BlockId::new(id)))),
            7 => function.blocks[0]
                .body
                .extend((100..357).map(|id| literal(id, Ty::I64, 0))),
            _ => unreachable!(),
        }
        source_refuses(&module, &lir);
    }
    for mutation in 0..5 {
        let mut wrong = lir.clone();
        match mutation {
            0 => wrong
                .blocks
                .get_mut(&wrong.entry_block)
                .unwrap()
                .instructions
                .resize(
                    257,
                    Instruction {
                        opcode: Opcode::Return,
                        args: vec![LirValue(0)],
                        results: vec![],
                    },
                ),
            1 => wrong
                .value_types
                .extend((1000..1385).map(|id| (LirValue(id), LirType::I64))),
            2 => wrong.signature.params.resize(9, LirType::I64),
            3 => wrong
                .blocks
                .get_mut(&wrong.entry_block)
                .unwrap()
                .instructions[0]
                .results
                .extend([LirValue(1000), LirValue(1001)]),
            4 => wrong
                .blocks
                .get_mut(&wrong.entry_block)
                .unwrap()
                .instructions[0]
                .args
                .resize(4, LirValue(0)),
            _ => unreachable!(),
        }
        assert!(
            matches!(
                bind_read_only_source(&original, 0, &wrong),
                Err(ReadOnlySourceError::Budget(_))
            ),
            "LIR preallocation limit mutation {mutation}"
        );
    }
    for (pointer_size, endianness) in [(4, Endianness::Little), (8, Endianness::Big)] {
        let mut module = original.clone();
        let target = module.target_info.as_mut().unwrap();
        target.pointer_size = pointer_size;
        target.endianness = endianness;
        source_refuses(&module, &lir);
    }
}
