// Generic TrustIR coverage for adapter-fused static call recovery.

use std::collections::HashMap;

use trust_cg_lower::{GuardCarrierArch, StaticCallDevirtualizationStats, TlsDialect};
use trust_ir::inst::CastOp;
use trust_ir::{
    Block, BlockId, CallingConv, Constant, FieldDef, FuncId, FuncTy, FuncTyId, Function, Global,
    Inst, InstrNode, Linkage, Module, SourceSpan, StructDef, StructId, StructRepr, Ty, ValueId,
};

#[path = "common/typed_refusal.rs"]
mod typed_refusal;
use typed_refusal::assert_typed_const_refusal;

#[path = "common/below_admission.rs"]
mod below_admission;
use below_admission::{body_below_admission, body_refusal_below_admission};

fn add_signature(module: &mut Module, param: Ty, result: Ty) -> FuncTyId {
    module
        .add_func_type(FuncTy {
            params: vec![param],
            returns: vec![result],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture")
}

fn add_identity_target(module: &mut Module, sig: FuncTyId) {
    let mut target = Function::new(FuncId::new(0), "identity", sig, BlockId::new(0));
    target.linkage = Linkage::Internal;
    let mut entry = Block::new(BlockId::new(0));
    entry.params.push((ValueId::new(0), Ty::I64));
    entry.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(0)],
    }));
    target.blocks.push(entry);
    module.functions.push(target);
}

fn static_call_module(with_copy_reify: bool) -> Module {
    let mut module = Module::new("generic_static_call");
    let sig = add_signature(&mut module, Ty::I64, Ty::I64);
    add_identity_target(&mut module, sig);

    let mut caller = Function::new(FuncId::new(1), "caller", sig, BlockId::new(0));
    let mut entry = Block::new(BlockId::new(0));
    entry.params.push((ValueId::new(0), Ty::I64));
    entry.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::Func(sig),
            value: Constant::FnDef(FuncId::new(0)),
        })
        .with_result(ValueId::new(1)),
    );
    let callee = if with_copy_reify {
        entry.body.push(
            InstrNode::new(Inst::Cast {
                op: CastOp::ReifyFnPointer,
                src_ty: Ty::Func(sig),
                dst_ty: Ty::Ptr,
                operand: ValueId::new(1),
            })
            .with_result(ValueId::new(2)),
        );
        entry.body.push(
            InstrNode::new(Inst::Copy {
                ty: Ty::Ptr,
                operand: ValueId::new(2),
            })
            .with_result(ValueId::new(3)),
        );
        ValueId::new(3)
    } else {
        ValueId::new(1)
    };
    entry.body.push(
        InstrNode::new(Inst::CallIndirect {
            callee,
            sig,
            args: vec![ValueId::new(0)],
            calling_conv: CallingConv::C,
        })
        .with_result(ValueId::new(4)),
    );
    entry.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(4)],
    }));
    caller.blocks.push(entry);
    module.functions.push(caller);
    module
}

fn add_div_annotation_clone_trigger(module: &mut Module) {
    let caller = module
        .functions
        .iter_mut()
        .find(|function| function.name == "caller")
        .expect("caller function");
    caller.blocks[0].body.splice(
        0..0,
        [
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(84),
            })
            .with_result(ValueId::new(100)),
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(2),
            })
            .with_result(ValueId::new(101)),
            InstrNode::new(Inst::BinOp {
                op: trust_ir::BinOp::UDiv,
                ty: Ty::I64,
                lhs: ValueId::new(100),
                rhs: ValueId::new(101),
            })
            .with_result(ValueId::new(102)),
        ],
    );
}

fn add_swift_aggregate_clone_trigger(module: &mut Module) {
    let struct_id = StructId::new(99);
    module.structs.push(StructDef {
        origin: None,
        id: struct_id,
        name: "SwiftPair".to_string(),
        fields: vec![
            FieldDef {
                name: "left".to_string(),
                ty: Ty::I64,
                offset: None,
            },
            FieldDef {
                name: "right".to_string(),
                ty: Ty::I64,
                offset: None,
            },
        ],
        size: None,
        align: None,
        repr: StructRepr::C,
    });
    let aggregate = Ty::Struct(struct_id);
    let signature = module
        .add_func_type(FuncTy {
            params: vec![aggregate.clone()],
            returns: vec![aggregate.clone()],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = Function::new(
        FuncId::new(99),
        "swift_clone_trigger",
        signature,
        BlockId::new(0),
    );
    function.calling_conv = CallingConv::Swift;
    let mut entry = Block::new(BlockId::new(0));
    entry.params.push((ValueId::new(0), aggregate));
    entry.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(0)],
    }));
    function.blocks.push(entry);
    module.functions.push(function);
}

fn shared_deep_static_call_module(
    ordinary_values: u32,
    chain_definitions: u32,
    call_count: u32,
) -> Module {
    assert!(chain_definitions > 0);
    assert!(call_count > 0);

    let mut module = Module::new("generic_shared_deep_static_calls");
    let sig = add_signature(&mut module, Ty::I64, Ty::I64);
    add_identity_target(&mut module, sig);

    let mut caller = Function::new(FuncId::new(1), "caller", sig, BlockId::new(0));
    let mut entry = Block::new(BlockId::new(0));
    entry.params.push((ValueId::new(0), Ty::I64));
    let mut next_value = 1u32;
    for _ in 0..ordinary_values {
        entry
            .body
            .push(InstrNode::new(Inst::NullPtr).with_result(ValueId::new(next_value)));
        next_value += 1;
    }

    entry.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::Func(sig),
            value: Constant::FnDef(FuncId::new(0)),
        })
        .with_result(ValueId::new(next_value)),
    );
    let mut callee = ValueId::new(next_value);
    next_value += 1;
    for _ in 1..chain_definitions {
        entry.body.push(
            InstrNode::new(Inst::Copy {
                ty: Ty::Func(sig),
                operand: callee,
            })
            .with_result(ValueId::new(next_value)),
        );
        callee = ValueId::new(next_value);
        next_value += 1;
    }

    let mut last_result = None;
    for _ in 0..call_count {
        let result = ValueId::new(next_value);
        next_value += 1;
        entry.body.push(
            InstrNode::new(Inst::CallIndirect {
                callee,
                sig,
                args: vec![ValueId::new(0)],
                calling_conv: CallingConv::C,
            })
            .with_result(result),
        );
        last_result = Some(result);
    }
    entry.body.push(InstrNode::new(Inst::Return {
        values: vec![last_result.expect("at least one call")],
    }));
    caller.blocks.push(entry);
    module.functions.push(caller);
    module
}

fn lower(
    module: &Module,
) -> (
    Vec<(trust_cg_lower::Function, trust_cg_lower::ProofContext)>,
    StaticCallDevirtualizationStats,
) {
    let (functions, stats, validation) =
        trust_cg_lower::translate_module_for_arch_with_tls_and_stats_and_validation_with_license(
            module,
            GuardCarrierArch::default(),
            TlsDialect::default(),
            &permit_unlicensed(),
        )
        .expect("generic TrustIR module lowers");
    validation
        .replay_exact_module_calls(&functions)
        .expect("exact-call report replays against its source module");
    (functions, stats)
}

fn caller_has_direct_call(
    functions: &[(trust_cg_lower::Function, trust_cg_lower::ProofContext)],
) -> bool {
    functions
        .iter()
        .find(|(function, _)| function.name == "caller")
        .expect("caller LIR")
        .0
        .blocks
        .values()
        .flat_map(|block| &block.instructions)
        .any(|instruction| {
            matches!(
                &instruction.opcode,
                trust_cg_lower::instructions::Opcode::Call { name, .. } if name == "identity"
            )
        })
}

fn caller_has_indirect_call(
    functions: &[(trust_cg_lower::Function, trust_cg_lower::ProofContext)],
) -> bool {
    functions
        .iter()
        .find(|(function, _)| function.name == "caller")
        .expect("caller LIR")
        .0
        .blocks
        .values()
        .flat_map(|block| &block.instructions)
        .any(|instruction| instruction.opcode == trust_cg_lower::instructions::Opcode::CallIndirect)
}

fn function_has_named_call(function: &trust_cg_lower::Function, expected: &str) -> bool {
    function
        .blocks
        .values()
        .flat_map(|block| &block.instructions)
        .any(|instruction| {
            matches!(
                &instruction.opcode,
                trust_cg_lower::instructions::Opcode::Call { name, .. } if name == expected
            )
        })
}

fn function_has_indirect_call(function: &trust_cg_lower::Function) -> bool {
    function
        .blocks
        .values()
        .flat_map(|block| &block.instructions)
        .any(|instruction| instruction.opcode == trust_cg_lower::instructions::Opcode::CallIndirect)
}

fn assert_exact_receipt_rejects_lir_mutation(
    label: &str,
    mutate: impl FnOnce(&mut trust_cg_lower::Function, trust_cg_lower::instructions::Block, usize),
) {
    let module = static_call_module(true);
    let (mut functions, validation) =
        trust_cg_lower::translate_module_for_arch_with_tls_and_validation_with_license(
            &module,
            GuardCarrierArch::default(),
            TlsDialect::default(),
            &permit_unlicensed(),
        )
        .expect("module with one recoverable exact edge lowers");
    assert_eq!(validation.exact_module_call_count(), 1);

    let caller_index = functions
        .iter()
        .position(|(function, _)| function.name == "caller")
        .expect("caller LIR");
    let (block, instruction) = functions[caller_index]
        .0
        .blocks
        .iter()
        .find_map(|(block, body)| {
            body.instructions
                .iter()
                .position(|instruction| {
                    matches!(
                        &instruction.opcode,
                        trust_cg_lower::instructions::Opcode::Call {
                            binding: trust_cg_lower::instructions::DirectCallBinding::ExactModuleFunction { .. },
                            ..
                        }
                    )
                })
                .map(|instruction| (*block, instruction))
        })
        .expect("one exact LIR call");
    mutate(&mut functions[caller_index].0, block, instruction);

    assert!(
        validation.replay_exact_module_calls(&functions).is_err(),
        "sealed exact-call authority accepted {label} mutation"
    );
}

/// One function in an opcode snapshot: its name, then each of its blocks by
/// index with that block's opcode sequence.
type FunctionOpcodeSnapshot = (
    String,
    Vec<(u32, Vec<trust_cg_lower::instructions::Opcode>)>,
);

fn opcode_snapshot(
    functions: &[(trust_cg_lower::Function, trust_cg_lower::ProofContext)],
) -> Vec<FunctionOpcodeSnapshot> {
    let mut functions = functions
        .iter()
        .map(|(function, _)| {
            let mut blocks = function
                .blocks
                .iter()
                .map(|(block, body)| {
                    (
                        block.0,
                        body.instructions
                            .iter()
                            .map(|instruction| instruction.opcode.clone())
                            .collect(),
                    )
                })
                .collect::<Vec<_>>();
            blocks.sort_by_key(|(block, _)| *block);
            (function.name.clone(), blocks)
        })
        .collect::<Vec<_>>();
    functions.sort_by(|left, right| left.0.cmp(&right.0));
    functions
}

#[test]
fn direct_fndef_and_copy_reify_chains_emit_named_lir_calls() {
    for mut module in [static_call_module(false), static_call_module(true)] {
        let source_call_index = module.functions[1].blocks[0]
            .body
            .iter()
            .position(|node| matches!(node.inst, Inst::CallIndirect { .. }))
            .expect("source indirect call");
        let source_span = SourceSpan {
            file: 7,
            line: 31,
            col: 9,
        };
        module.functions[1].blocks[0].body[source_call_index].span = Some(source_span);
        let original_call = module.functions[1].blocks[0].body[source_call_index].clone();
        let (functions, stats) = lower(&module);

        assert_eq!(stats.indirect_calls_seen, 1);
        assert_eq!(stats.resolved_static_targets, 1);
        assert_eq!(stats.devirtualized_calls, 1);
        assert_eq!(stats.unresolved_callees, 0);
        assert_eq!(stats.incompatible_calls, 0);
        assert_eq!(stats.provenance_analyses_built, 1);
        assert_eq!(stats.use_site_indices_built, 1);
        assert_eq!(stats.definition_indices_built, 1);
        assert_eq!(stats.provenance_indices_built, 1);
        assert_eq!(stats.dominator_trees_built, 1);
        assert_eq!(stats.use_site_blocks_indexed, 1);
        assert_eq!(stats.use_site_parameters_indexed, 1);
        assert_eq!(stats.definition_blocks_indexed, 1);
        assert!(stats.definition_instructions_indexed >= 3);
        assert!(stats.definition_values_indexed >= 3);
        assert!(stats.provenance_definitions_visited >= 2);
        assert!(stats.provenance_entries_stored >= 1);
        assert_eq!(stats.provenance_summary_lookups, 1);
        assert_eq!(stats.exact_use_dominance_checks, 1);
        assert_eq!(stats.synthetic_direct_nodes_built, 1);
        assert_eq!(stats.prefilter_rejections, 0);
        assert!((1..=8).contains(&stats.prefilter_producer_probes));
        assert!(caller_has_direct_call(&functions));
        assert!(!caller_has_indirect_call(&functions));

        let caller = functions
            .iter()
            .find(|(function, _)| function.name == "caller")
            .expect("caller LIR");
        let (lir_block, direct_call_index) = caller
            .0
            .blocks
            .iter()
            .find_map(|(block, body)| {
                body.instructions
                    .iter()
                    .position(|instruction| {
                        matches!(
                            &instruction.opcode,
                            trust_cg_lower::instructions::Opcode::Call { name, .. }
                                if name == "identity"
                        )
                    })
                    .map(|index| (*block, index))
            })
            .expect("recovered named call");
        assert!(matches!(
            &caller.0.blocks[&lir_block].instructions[direct_call_index].opcode,
            trust_cg_lower::instructions::Opcode::Call {
                name,
                binding: trust_cg_lower::instructions::DirectCallBinding::ExactModuleFunction {
                    function: 0
                },
            } if name == "identity"
        ));
        assert_eq!(
            caller.0.trust_ir_origins[&lir_block][direct_call_index],
            Some(trust_cg_ir::TrustIrInstId(source_call_index as u32)),
            "the recovered call must retain the exact indirect source origin",
        );
        assert_eq!(
            caller.0.blocks[&lir_block].source_locs[direct_call_index],
            Some(trust_cg_ir::SourceLoc {
                file: source_span.file,
                line: source_span.line,
                col: source_span.col,
            }),
            "the recovered call must retain the exact indirect source span",
        );

        // Adapter fusion is observational: source nodes and their metadata are
        // not rewritten, reordered, or cloned into the cache identity.
        let source_call = module.functions[1].blocks[0]
            .body
            .iter()
            .find(|node| matches!(node.inst, Inst::CallIndirect { .. }))
            .expect("source indirect call remains");
        assert_eq!(source_call, &original_call);
    }
}

#[test]
fn shared_deep_chain_work_is_linear_and_provenance_storage_is_sparse() {
    const ORDINARY_VALUES: u32 = 512;
    const CHAIN_DEFINITIONS: u32 = 513;
    const CALL_COUNT: u32 = 1_000;

    let module = shared_deep_static_call_module(ORDINARY_VALUES, CHAIN_DEFINITIONS, CALL_COUNT);
    let (functions, stats) = lower(&module);

    assert_eq!(stats.indirect_calls_seen, CALL_COUNT as usize);
    assert_eq!(stats.resolved_static_targets, CALL_COUNT as usize);
    assert_eq!(stats.devirtualized_calls, CALL_COUNT as usize);
    assert_eq!(stats.unresolved_callees, 0);
    assert_eq!(stats.incompatible_calls, 0);
    assert_eq!(stats.provenance_analyses_built, 1);
    assert_eq!(stats.use_site_indices_built, 1);
    assert_eq!(stats.definition_indices_built, 1);
    assert_eq!(stats.provenance_indices_built, 1);
    assert_eq!(stats.dominator_trees_built, 1);
    assert_eq!(
        stats.prefilter_producer_probes, 8,
        "the adapter prefilter must run only before authoritative state exists",
    );
    assert_eq!(
        stats.trust_ir_prefilter_instructions_visited, 9,
        "TrustIR's local prefilter must stop after authoritative state exists",
    );
    assert_eq!(
        stats.exact_use_operands_visited, CALL_COUNT as usize,
        "exact-use authentication must stop when the leading callee matches",
    );
    assert_eq!(
        stats.provenance_entries_stored, CHAIN_DEFINITIONS as usize,
        "ordinary SSA definitions must not occupy provenance rows",
    );
    assert_eq!(
        stats.provenance_links_validated,
        CHAIN_DEFINITIONS as usize - 1,
    );
    assert_eq!(stats.provenance_summary_lookups, CALL_COUNT as usize);
    assert_eq!(stats.exact_use_dominance_checks, CALL_COUNT as usize);
    assert_eq!(stats.dominator_blocks_indexed, 1);
    assert_eq!(stats.dominator_edges_indexed, 0);
    assert_eq!(
        stats.dominator_instructions_indexed,
        stats.definition_instructions_indexed,
    );
    assert!(
        stats.provenance_definitions_visited
            <= stats.definition_values_indexed + CHAIN_DEFINITIONS as usize,
        "shared chains must be summarized once rather than walked per call",
    );
    assert!(caller_has_direct_call(&functions));
    assert!(!caller_has_indirect_call(&functions));
}

#[test]
fn standalone_translation_retains_indirect_calls_without_a_whole_module_receipt() {
    let module = static_call_module(false);
    let caller = &module.functions[1];

    let (bare, _) =
        trust_cg_lower::translate_function_with_license(caller, &module, &permit_unlicensed())
            .expect("standalone lowering succeeds");
    assert!(!function_has_named_call(&bare, "identity"));
    assert!(function_has_indirect_call(&bare));

    let mut incomplete_names = HashMap::new();
    incomplete_names.insert(FuncId::new(1), "caller".to_string());
    let (incomplete, _) = trust_cg_lower::translate_function_with_names_and_license(
        caller,
        &module,
        &incomplete_names,
        &permit_unlicensed(),
    )
    .expect("standalone lowering with incomplete names succeeds");
    assert!(!function_has_named_call(&incomplete, "identity"));
    assert!(function_has_indirect_call(&incomplete));
}

#[test]
fn module_without_indirect_calls_has_an_empty_recovery_census() {
    let mut module = static_call_module(false);
    let body = &mut module.functions[1].blocks[0].body;
    body.remove(0);
    body[0].inst = Inst::Call {
        callee: FuncId::new(0),
        args: vec![ValueId::new(0)],
    };
    let source_before = module.clone();

    let (functions, stats) = lower(&module);
    assert_eq!(stats, StaticCallDevirtualizationStats::default());
    assert_eq!(stats.provenance_analyses_built, 0);
    assert_eq!(stats.synthetic_direct_nodes_built, 0);
    assert_eq!(stats.prefilter_rejections, 0);
    assert_eq!(
        module, source_before,
        "adapter fusion must not clone/rewrite TrustIR"
    );
    assert!(caller_has_direct_call(&functions));
    assert!(!caller_has_indirect_call(&functions));
}

#[test]
fn traced_and_untraced_lowering_emit_identical_lir() {
    let module = static_call_module(true);
    let (untraced, validation) =
        trust_cg_lower::translate_module_for_arch_with_tls_and_validation_with_license(
            &module,
            GuardCarrierArch::default(),
            TlsDialect::default(),
            &permit_unlicensed(),
        )
        .expect("untraced module lowers");
    validation
        .replay_exact_module_calls(&untraced)
        .expect("untraced exact calls replay");
    let (traced, stats) = lower(&module);

    assert_eq!(opcode_snapshot(&untraced), opcode_snapshot(&traced));
    assert_eq!(stats.devirtualized_calls, 1);
}

#[test]
fn sealed_exact_call_receipt_rejects_lir_mutations() {
    use trust_cg_lower::Type;
    use trust_cg_lower::instructions::{DirectCallBinding, Opcode, Value};

    assert_exact_receipt_rejects_lir_mutation("callee name", |function, block, instruction| {
        let Opcode::Call { name, .. } = &mut function
            .blocks
            .get_mut(&block)
            .expect("call block")
            .instructions[instruction]
            .opcode
        else {
            unreachable!("fixture exact call")
        };
        name.push_str("_forged");
    });
    assert_exact_receipt_rejects_lir_mutation("binding class", |function, block, instruction| {
        let Opcode::Call { binding, .. } = &mut function
            .blocks
            .get_mut(&block)
            .expect("call block")
            .instructions[instruction]
            .opcode
        else {
            unreachable!("fixture exact call")
        };
        *binding = DirectCallBinding::Interposable;
    });
    assert_exact_receipt_rejects_lir_mutation(
        "operand identity",
        |function, block, instruction| {
            function
                .blocks
                .get_mut(&block)
                .expect("call block")
                .instructions[instruction]
                .args
                .push(Value(u32::MAX));
        },
    );
    assert_exact_receipt_rejects_lir_mutation("result identity", |function, block, instruction| {
        function
            .blocks
            .get_mut(&block)
            .expect("call block")
            .instructions[instruction]
            .results
            .clear();
    });
    assert_exact_receipt_rejects_lir_mutation("caller signature", |function, _, _| {
        function.signature.returns = vec![Type::I32];
    });
    assert_exact_receipt_rejects_lir_mutation("call value type", |function, block, instruction| {
        let result = function.blocks[&block].instructions[instruction].results[0];
        function.value_types.insert(result, Type::I32);
    });
    assert_exact_receipt_rejects_lir_mutation("source location", |function, block, instruction| {
        function
            .blocks
            .get_mut(&block)
            .expect("call block")
            .source_locs[instruction] = Some(trust_cg_ir::SourceLoc {
            file: 7,
            line: 11,
            col: 13,
        });
    });
    assert_exact_receipt_rejects_lir_mutation("source origin", |function, block, instruction| {
        function
            .trust_ir_origins
            .get_mut(&block)
            .expect("origin sidecar")[instruction] = Some(trust_cg_ir::TrustIrInstId(u32::MAX));
    });
}

#[test]
fn structural_signature_and_calling_convention_mismatches_stay_indirect() {
    let mut signature_mismatch = static_call_module(true);
    let wrong_sig = add_signature(&mut signature_mismatch, Ty::U64, Ty::U64);
    let caller = &mut signature_mismatch.functions[1];
    caller.ty = wrong_sig;
    caller.blocks[0].params[0].1 = Ty::U64;
    let call = caller.blocks[0]
        .body
        .iter_mut()
        .find(|node| matches!(node.inst, Inst::CallIndirect { .. }))
        .expect("indirect call");
    if let Inst::CallIndirect { sig, .. } = &mut call.inst {
        *sig = wrong_sig;
    }

    let mut convention_mismatch = static_call_module(true);
    let call = convention_mismatch.functions[1].blocks[0]
        .body
        .iter_mut()
        .find(|node| matches!(node.inst, Inst::CallIndirect { .. }))
        .expect("indirect call");
    if let Inst::CallIndirect { calling_conv, .. } = &mut call.inst {
        *calling_conv = CallingConv::Rust;
    }

    for module in [signature_mismatch, convention_mismatch] {
        let (functions, stats) = lower(&module);
        assert_eq!(stats.indirect_calls_seen, 1);
        assert_eq!(stats.resolved_static_targets, 1);
        assert_eq!(stats.devirtualized_calls, 0);
        assert_eq!(stats.incompatible_calls, 1);
        assert!(!caller_has_direct_call(&functions));
        assert!(caller_has_indirect_call(&functions));
    }
}

#[test]
fn argument_and_result_contract_mismatches_fail_closed() {
    let mut argument_mismatch = static_call_module(true);
    argument_mismatch.functions[1].blocks[0].params[0].1 = Ty::U64;

    let mut result_mismatch = static_call_module(true);
    result_mismatch.functions[1].blocks[0]
        .body
        .iter_mut()
        .find(|node| matches!(node.inst, Inst::CallIndirect { .. }))
        .expect("indirect call")
        .results
        .clear();

    for module in [argument_mismatch, result_mismatch] {
        assert!(
            trust_cg_lower::translate_module_for_arch_with_tls_and_stats_with_license(
                &module,
                GuardCarrierArch::default(),
                TlsDialect::default(),
                &permit_unlicensed(),
            )
            .is_err(),
            "an incompatible edge must not become a valid direct call"
        );
    }
}

#[test]
fn dynamic_callee_stays_indirect() {
    let mut module = static_call_module(false);
    let target_sig = module.functions[0].ty;
    let caller_sig = module
        .add_func_type(FuncTy {
            params: vec![Ty::Func(target_sig), Ty::I64],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let caller = &mut module.functions[1];
    caller.ty = caller_sig;
    let entry = &mut caller.blocks[0];
    entry
        .params
        .insert(0, (ValueId::new(8), Ty::Func(target_sig)));
    entry.body.remove(0);
    if let Inst::CallIndirect { callee, .. } = &mut entry.body[0].inst {
        *callee = ValueId::new(8);
    }

    let (functions, stats) = lower(&module);
    assert_eq!(stats.indirect_calls_seen, 1);
    assert_eq!(stats.resolved_static_targets, 0);
    assert_eq!(stats.devirtualized_calls, 0);
    assert_eq!(stats.unresolved_callees, 1);
    assert_eq!(stats.prefilter_rejections, 1);
    assert_eq!(stats.prefilter_producer_probes, 1);
    assert_eq!(stats.provenance_analyses_built, 0);
    assert!(caller_has_indirect_call(&functions));
}

#[test]
fn local_non_candidate_callee_is_prefiltered_without_provenance_state() {
    let mut module = static_call_module(false);
    let target_sig = module.functions[0].ty;
    let caller_sig = module
        .add_func_type(FuncTy {
            params: vec![Ty::Func(target_sig), Ty::I64],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let caller = &mut module.functions[1];
    caller.ty = caller_sig;
    let entry = &mut caller.blocks[0];
    entry
        .params
        .insert(0, (ValueId::new(8), Ty::Func(target_sig)));
    entry.body[0] = InstrNode::new(Inst::Copy {
        ty: Ty::Func(target_sig),
        operand: ValueId::new(8),
    })
    .with_result(ValueId::new(1));

    let (functions, stats) = lower(&module);
    assert_eq!(stats.indirect_calls_seen, 1);
    assert_eq!(stats.prefilter_rejections, 1);
    assert_eq!(stats.prefilter_producer_probes, 2);
    assert_eq!(stats.unresolved_callees, 1);
    assert_eq!(stats.provenance_analyses_built, 0);
    assert!(caller_has_indirect_call(&functions));
}

#[test]
fn dominating_cross_block_definition_emits_named_call() {
    let mut module = static_call_module(false);
    let caller = &mut module.functions[1];
    let mut old = std::mem::take(&mut caller.blocks[0].body).into_iter();
    let definition = old.next().expect("definition");
    let mut call = old.next().expect("call");
    if let Inst::CallIndirect { args, .. } = &mut call.inst {
        *args = vec![ValueId::new(10)];
    }

    let mut entry = Block::new(BlockId::new(0));
    entry.params.push((ValueId::new(0), Ty::I64));
    entry.body.push(definition);
    entry.body.push(InstrNode::new(Inst::Br {
        target: BlockId::new(1),
        args: vec![ValueId::new(0)],
    }));
    let mut call_block = Block::new(BlockId::new(1));
    call_block.params.push((ValueId::new(10), Ty::I64));
    call_block.body.push(call);
    call_block.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(4)],
    }));
    caller.blocks = vec![entry, call_block];

    let (functions, stats) = lower(&module);
    assert_eq!(stats.devirtualized_calls, 1);
    assert!(caller_has_direct_call(&functions));
    assert!(!caller_has_indirect_call(&functions));
}

#[test]
fn forward_and_sibling_definitions_do_not_gain_dominance() {
    let mut forward = static_call_module(false);
    let body = &mut forward.functions[1].blocks[0].body;
    let definition = body.remove(0);
    body.insert(1, definition);

    let mut sibling = static_call_module(false);
    let caller = &mut sibling.functions[1];
    let mut old = std::mem::take(&mut caller.blocks[0].body).into_iter();
    let definition = old.next().expect("definition");
    let call = old.next().expect("call");

    let mut entry = Block::new(BlockId::new(0));
    entry.params.push((ValueId::new(0), Ty::I64));
    entry.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::Bool,
            value: Constant::Bool(true),
        })
        .with_result(ValueId::new(9)),
    );
    entry.body.push(InstrNode::new(Inst::CondBr {
        cond: ValueId::new(9),
        then_target: BlockId::new(1),
        then_args: vec![],
        else_target: BlockId::new(2),
        else_args: vec![],
    }));
    let mut call_block = Block::new(BlockId::new(1));
    call_block.body.push(call);
    call_block.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(4)],
    }));
    let mut definition_block = Block::new(BlockId::new(2));
    definition_block.body.push(definition);
    definition_block.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(0)],
    }));
    caller.blocks = vec![entry, call_block, definition_block];

    for module in [forward, sibling] {
        let (functions, stats) = lower(&module);
        assert_eq!(stats.resolved_static_targets, 0);
        assert_eq!(stats.devirtualized_calls, 0);
        assert_eq!(stats.unresolved_callees, 1);
        assert!(caller_has_indirect_call(&functions));
    }
}

#[test]
fn signature_laundering_through_pointer_stays_indirect() {
    let mut module = static_call_module(true);
    let target_sig = module.functions[0].ty;
    let wrong_sig = add_signature(&mut module, Ty::I32, Ty::I64);
    let body = &mut module.functions[1].blocks[0].body;
    body[2] = InstrNode::new(Inst::Cast {
        op: CastOp::ReifyFnPointer,
        src_ty: Ty::Ptr,
        dst_ty: Ty::Func(wrong_sig),
        operand: ValueId::new(2),
    })
    .with_result(ValueId::new(3));
    body.insert(
        3,
        InstrNode::new(Inst::Cast {
            op: CastOp::ReifyFnPointer,
            src_ty: Ty::Func(wrong_sig),
            dst_ty: Ty::Ptr,
            operand: ValueId::new(3),
        })
        .with_result(ValueId::new(5)),
    );
    if let Inst::CallIndirect { callee, sig, .. } = &mut body[4].inst {
        *callee = ValueId::new(5);
        *sig = target_sig;
    }

    let (functions, stats) = lower(&module);
    assert_eq!(stats.resolved_static_targets, 0);
    assert_eq!(stats.devirtualized_calls, 0);
    assert_eq!(stats.unresolved_callees, 1);
    assert!(caller_has_indirect_call(&functions));
}

#[test]
fn duplicate_target_identity_rejects_the_module() {
    let mut module = static_call_module(false);
    let mut duplicate = module.functions[0].clone();
    duplicate.name = "duplicate_identity".to_string();
    module.functions.push(duplicate);

    let error = trust_cg_lower::translate_module_for_arch_with_tls_and_stats_with_license(
        &module,
        GuardCarrierArch::default(),
        TlsDialect::default(),
        &permit_unlicensed(),
    )
    .expect_err("an ambiguous FuncId cannot select code or a symbol name");
    // The caller's function-item constant names the duplicated identity, and
    // TrustIR's typed admission refuses that ambiguous item before the
    // adapter's own FuncId check (pinned by the test below) is reached.
    assert_typed_const_refusal(
        &error,
        "function 'caller' bb0",
        "a unique module-owned function item",
        "missing or ambiguous func.0",
    );
}

#[test]
fn unrelated_duplicate_function_identity_rejects_before_lowering() {
    let mut module = static_call_module(false);
    module.functions[1].blocks[0].body = vec![InstrNode::new(Inst::Return {
        values: vec![ValueId::new(0)],
    })];
    let mut duplicate = module.functions[0].clone();
    duplicate.name = "rust_eh_personality".to_string();
    module.functions.push(duplicate);

    let error = trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        &module,
        GuardCarrierArch::default(),
        TlsDialect::default(),
        &permit_unlicensed(),
    )
    .expect_err("ambiguous identities must not influence unrelated name policy");
    assert!(error.to_string().contains("ambiguous FuncId(0)"));
}

/// `static_call_module` with its target exported and its caller first, so the
/// adapter alone (which lowers a module's first function, and refuses a body
/// naming a module-local symbol) lowers the caller's function item.
fn caller_first_with_exported_target(mut module: Module) -> Module {
    let caller = module
        .functions
        .iter()
        .position(|function| function.name == "caller")
        .expect("caller function");
    let caller = module.functions.remove(caller);
    module.functions.insert(0, caller);
    for function in &mut module.functions {
        if function.name == "identity" {
            function.linkage = Linkage::External;
        }
    }
    module
}

/// A function item naming no module function. TrustIR's typed admission
/// refuses it on every codegen entry. Below that admission the adapter's own
/// function-symbol check refuses it by name rather than emit a relocation no
/// object defines, and the registered item lowers. The check's other half, an
/// AMBIGUOUS `FuncId`, never reaches it: every entry that builds an adapter,
/// `translate_body_template` included, refuses a duplicated identity at the
/// module's function catalog before any body is lowered.
#[test]
fn a_function_item_naming_no_module_function_is_refused_below_typed_admission() {
    let mut missing = static_call_module(false);
    let caller = missing
        .functions
        .iter_mut()
        .find(|function| function.name == "caller")
        .expect("caller function");
    let Inst::Const { value, .. } = &mut caller.blocks[0].body[0].inst else {
        panic!("the caller opens with its function item")
    };
    *value = Constant::FnDef(FuncId::new(9));
    let error = trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        &missing,
        GuardCarrierArch::default(),
        TlsDialect::default(),
        &permit_unlicensed(),
    )
    .expect_err("a function item naming no function must be refused");
    assert_typed_const_refusal(
        &error,
        "function 'caller' bb0",
        "a unique module-owned function item",
        "missing or ambiguous func.9",
    );
    assert_eq!(
        body_refusal_below_admission(&caller_first_with_exported_target(missing)),
        "not lowerable: unsupported trust_ir instruction: function symbol constant references \
         unregistered FuncId(9) or ambiguous FuncId(9)"
    );
    body_below_admission(&caller_first_with_exported_target(static_call_module(
        false,
    )))
    .expect("the registered function item lowers below admission");

    let mut duplicated = static_call_module(false);
    let mut duplicate = duplicated.functions[0].clone();
    duplicate.name = "duplicate_identity".to_string();
    duplicated.functions.push(duplicate);
    assert_eq!(
        body_refusal_below_admission(&caller_first_with_exported_target(duplicated)),
        "ambiguous function catalog: unsupported trust_ir instruction: module contains \
         ambiguous FuncId(0); exact call, symbol, and unwind semantics require unique function \
         identities"
    );
}

/// Two external declarations sharing one link-time symbol are REFUSED by the
/// trust-ir validator as of binary v41, before this crate ever sees the module.
///
/// This test used to build exactly that module and assert it lowered with both
/// source edges kept distinct. v41 made `Function::name` normatively the
/// link-time symbol and outlawed the ambiguity outright
/// (`ValidationError::DuplicateFunctionSymbol`), on the ground that the adapter
/// emits the name verbatim, `merge_modules` dedups on it and the CLI linker
/// assigns merged ids from it — so a shared symbol silently conflates two
/// bodies. The scenario is therefore no longer representable, and the guard
/// this test exists to hold — nothing may conflate two declarations of one
/// symbol — is now held one layer earlier and more strictly. Pinned here so
/// the refusal cannot regress into a silent lowering.
///
/// `compatible_external_declarations` in `static_call_devirtualization.rs` is
/// deliberately left in place: it still governs any path that reaches this
/// crate without that validation, and it compares every declaration field
/// except `FuncId`/`FuncTyId` — including v41's `body_gate` and `display_path`.
#[test]
fn repeated_external_declarations_are_refused_as_an_ambiguous_symbol() {
    let mut module = Module::new("repeated_import_calls");
    module.target_info = Some(trust_ir::TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: trust_ir::Endianness::Little,
        abi: None,
        struct_passing: trust_ir::StructPassingPolicy::NativeC,
    });
    for id in [7, 11] {
        let sig = add_signature(&mut module, Ty::I64, Ty::I64);
        module.functions.push(Function::new(
            FuncId::new(id),
            "imported",
            sig,
            BlockId::new(0),
        ));
    }
    let sig = add_signature(&mut module, Ty::I64, Ty::I64);
    let mut caller = Function::new(FuncId::new(42), "caller", sig, BlockId::new(0));
    let mut entry = Block::new(BlockId::new(0));
    entry.params.push((ValueId::new(0), Ty::I64));
    for (index, id) in [7, 11].into_iter().enumerate() {
        entry.body.push(
            InstrNode::new(Inst::Call {
                callee: FuncId::new(id),
                args: vec![ValueId::new(index as u32)],
            })
            .with_result(ValueId::new(index as u32 + 1)),
        );
    }
    entry.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(2)],
    }));
    caller.blocks.push(entry);
    module.functions.push(caller);

    let source_validation = trust_ir_build::validate_module_report(&module);
    let errors = format!("{:?}", source_validation.errors());
    assert!(
        errors.contains("DuplicateFunctionSymbol"),
        "v41 must refuse two declarations of one link-time symbol, got {errors}"
    );
    assert!(
        errors.contains("\"imported\""),
        "the refusal must name the colliding symbol, got {errors}"
    );
}

#[test]
fn duplicate_lowered_symbol_names_reject_before_identity_is_erased() {
    let mut module = static_call_module(false);
    module.functions[1].name = "identity".to_string();

    let error = trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        &module,
        GuardCarrierArch::default(),
        TlsDialect::default(),
        &permit_unlicensed(),
    )
    .expect_err("distinct FuncIds must not collapse to one downstream name");
    assert!(
        error
            .to_string()
            .contains("ambiguous lowered symbol name \"identity\"")
    );
}

#[test]
fn function_and_global_symbol_collision_rejects_before_identity_is_erased() {
    let mut module = static_call_module(false);
    module.globals.push(Global {
        name: "identity".to_string(),
        ty: Ty::I64,
        mutable: false,
        initializer: Some(Constant::Int(0)),
        linkage: Linkage::Internal,
        tls: None,
        align: None,
        section: None,
        visibility: trust_ir::Visibility::Default,
        retained: false,
    });

    let error = trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        &module,
        GuardCarrierArch::default(),
        TlsDialect::default(),
        &permit_unlicensed(),
    )
    .expect_err("a function and global cannot collapse into one linker symbol");
    assert!(
        error
            .to_string()
            .contains("ambiguous lowered symbol name \"identity\"")
    );
}

#[test]
fn duplicate_target_identity_rejects_an_ordinary_direct_call() {
    let mut module = static_call_module(false);
    let caller_body = &mut module.functions[1].blocks[0].body;
    caller_body.remove(0);
    caller_body[0].inst = Inst::Call {
        callee: FuncId::new(0),
        args: vec![ValueId::new(0)],
    };
    let mut duplicate = module.functions[0].clone();
    duplicate.name = "duplicate_identity".to_string();
    module.functions.push(duplicate);

    let error = trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        &module,
        GuardCarrierArch::default(),
        TlsDialect::default(),
        &permit_unlicensed(),
    )
    .expect_err("a direct call cannot choose between duplicate FuncIds");
    assert!(error.to_string().contains("ambiguous FuncId(0)"));
}

#[test]
fn duplicate_target_identity_rejects_invoke() {
    let mut module = Module::new("duplicate_invoke_target");
    let sig = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    for name in ["throwing_a", "throwing_b"] {
        let mut target = Function::new(FuncId::new(0), name, sig, BlockId::new(0));
        target.linkage = Linkage::External;
        module.functions.push(target);
    }

    let mut caller = Function::new(FuncId::new(1), "caller", sig, BlockId::new(0));
    let mut entry = Block::new(BlockId::new(0));
    entry.body.push(InstrNode::new(Inst::Invoke {
        callee: FuncId::new(0),
        args: vec![],
        normal_dest: BlockId::new(1),
        normal_args: vec![],
        unwind_dest: BlockId::new(2),
    }));
    let mut normal = Block::new(BlockId::new(1));
    normal
        .body
        .push(InstrNode::new(Inst::Return { values: vec![] }));
    let mut unwind = Block::new(BlockId::new(2));
    unwind.body.push(
        InstrNode::new(Inst::LandingPad {
            is_cleanup: true,
            catch_type_indices: vec![],
        })
        .with_results(vec![ValueId::new(10), ValueId::new(11)]),
    );
    unwind.body.push(InstrNode::new(Inst::Resume {
        exn: ValueId::new(10),
    }));
    caller.blocks = vec![entry, normal, unwind];
    module.functions.push(caller);

    let error = trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        &module,
        GuardCarrierArch::default(),
        TlsDialect::default(),
        &permit_unlicensed(),
    )
    .expect_err("invoke cannot choose between duplicate FuncIds");
    assert!(error.to_string().contains("ambiguous FuncId(0)"));
}

#[test]
fn duplicate_argument_ssa_identity_is_rejected_by_shared_validation() {
    let mut module = static_call_module(false);
    module.functions[1].blocks[0].body.insert(
        1,
        InstrNode::new(Inst::Const {
            ty: Ty::I64,
            value: Constant::Int(7),
        })
        .with_result(ValueId::new(0)),
    );

    let error = trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        &module,
        GuardCarrierArch::default(),
        TlsDialect::default(),
        &permit_unlicensed(),
    )
    .expect_err("duplicate SSA identities must fail before backend recovery");
    assert!(error.to_string().contains("defined more than once"));
}

/// A module-local target named like a name-recognized intrinsic keeps its
/// exact source identity: its spelling does not make exact static recovery
/// re-enter external-intrinsic recognition. A module-local target named like
/// a routine the backend itself calls by name (`memcpy`, `memmove`,
/// `memset`) is refused by the translation entry before lowering instead
/// (`BackendSymbolShadowed`), since a backend memory-intrinsic call would
/// reach it.
#[test]
fn every_intrinsic_like_module_local_target_uses_exact_source_identity() {
    for name in ["memcpy", "memmove", "memset"] {
        let mut module = static_call_module(true);
        module.functions[0].name = name.to_string();
        let error = trust_cg_lower::translate_module_for_arch_with_tls_with_license(
            &module,
            GuardCarrierArch::default(),
            TlsDialect::default(),
            &permit_unlicensed(),
        )
        .expect_err("a module-local body named like a backend runtime call");
        assert!(
            matches!(
                &error,
                trust_cg_lower::AdapterError::BackendSymbolShadowed { name: shadowed, .. }
                    if shadowed == name
            ),
            "{name}: {error}"
        );
    }
    for name in [
        "llvm.bitreverse.i64",
        "llvm.objectsize.i64.p0",
        "llvm.fmuladd.f32",
        "llvm.fma.f64",
        "llvm.fmuladd.v4f32",
        "llvm.fmuladd.v2f64",
    ] {
        let mut module = static_call_module(true);
        // Every fixture body is the integer identity function. The source
        // FuncId and Internal body own the semantics; its spelling must not
        // make exact static recovery re-enter unrelated external-intrinsic
        // recognition.
        module.functions[0].name = name.to_string();

        let (functions, stats) = lower(&module);
        assert_eq!(stats.resolved_static_targets, 1, "{name}");
        assert_eq!(stats.devirtualized_calls, 1, "{name}");
        assert_eq!(stats.incompatible_calls, 0, "{name}");
        assert!(function_has_named_call(&functions[1].0, name), "{name}");
        assert!(!caller_has_indirect_call(&functions), "{name}");
    }
}

#[test]
fn validated_adapter_clones_refuse_materialized_local_function_identity() {
    for (label, trigger) in [
        ("div", add_div_annotation_clone_trigger as fn(&mut Module)),
        ("swift", add_swift_aggregate_clone_trigger),
    ] {
        let mut module = static_call_module(true);
        trigger(&mut module);
        let error = trust_cg_lower::translate_module_for_arch_with_tls_and_validation_with_license(
            &module,
            GuardCarrierArch::AArch64,
            TlsDialect::default(),
            &permit_unlicensed(),
        )
        .expect_err("a transformed report cannot borrow different source identity");
        let diagnostic = error.to_string();
        assert!(
            diagnostic.contains("adapter-owned module clone")
                && diagnostic.contains("1 materialized function identity value(s)"),
            "{label}: {diagnostic}"
        );
    }
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
