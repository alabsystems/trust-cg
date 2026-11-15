// Copyright 2026 Andrew Yates | Apache-2.0
use super::*;
fn fixture() -> (Module, Function) {
    let module = super::super::liveness_tests::original_branch_module(true);
    let (lir, _) = trust_cg_lower::translate_function_with_license(
        &module.functions[0],
        &module,
        &crate::license_test_support::permit_unlicensed(),
    )
    .unwrap();
    (module, lir)
}
#[test]
fn scalar_edge_projection_exact_original_branch_transports_and_raw_ssa_floor() {
    let (module, lir) = fixture();
    let before = lir.canonical_verifier_identity_bytes().unwrap();
    let checked = check_scalar_block_arguments(&module, 0, &lir).unwrap();
    assert_eq!(checked.transports().len(), 2);
    assert!(
        checked
            .transports()
            .iter()
            .all(|e| e.source_arguments == [100]
                && e.copy_instructions.len() == 1
                && e.parameter_codecs == [ScalarEdgeCodec::Pointer])
    );
    assert!(super::super::lir::graph(&lir).is_err());
    assert!(
        super::super::lir::graph_projected(&module, 0, &lir, Profile::ReadOnly, &checked).is_ok()
    );
    assert_eq!(before, lir.canonical_verifier_identity_bytes().unwrap());
    let cloned = lir.clone();
    assert!(
        super::super::lir::graph_projected(&module, 0, &cloned, Profile::ReadOnly, &checked)
            .is_err()
    );
    let foreign = module.clone();
    assert!(
        super::super::lir::graph_projected(&foreign, 0, &lir, Profile::ReadOnly, &checked).is_err()
    );
}
#[test]
fn scalar_edge_projection_actual_original_e1_def_five_lane_copy_group() {
    let bytes = include_bytes!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../reports/2026-11-12-original-e1-machine/fixture/core.tmbc"
    ));
    let module = trust_cg_codegen::pipeline::decode_tmbc(bytes).unwrap();
    let policy = crate::license_test_support::permit_unlicensed();
    let (functions, validation) =
        trust_cg_lower::translate_module_strict_for_arch_with_tls_and_validation_with_license(
            &module,
            trust_cg_lower::GuardCarrierArch::AArch64,
            trust_cg_lower::TlsDialect::MachOTlv,
            &policy,
        )
        .unwrap();
    validation
        .replay_strict_call_bindings_exhaustive(&functions)
        .unwrap();
    assert_eq!(functions.len(), 6);
    for name in ["tla_def_0", "tla_def_1"] {
        let ordinal = module
            .functions
            .iter()
            .position(|f| f.name == name)
            .unwrap();
        let lir = &functions.iter().find(|(f, _)| f.name == name).unwrap().0;
        let checked = check_scalar_block_arguments(&module, ordinal, lir)
            .unwrap_or_else(|e| panic!("{name}: {e}"));
        let edges: Vec<_> = checked
            .transports()
            .iter()
            .filter(|e| !e.source_arguments.is_empty())
            .collect();
        assert_eq!(edges.len(), 1);
        assert_eq!(edges[0].source_arguments.len(), 5);
        assert_eq!(edges[0].copy_instructions.len(), 5);
        if name == "tla_def_0" {
            let edge = edges[0];
            let mut changed = lir.clone();
            let block = LirBlock(edge.lowering_block);
            changed
                .blocks
                .get_mut(&block)
                .unwrap()
                .instructions
                .swap(edge.copy_instructions[0], edge.copy_instructions[1]);
            assert!(
                check_scalar_block_arguments(&module, ordinal, &changed).is_err(),
                "different emitted order cannot reuse exact transport binding"
            );
        }

        println!(
            "ORIGINAL_E1_CHECKED_SCALAR_EDGE {name} args={:?} target_args={:?} copies={:?} codecs={:?} body_proof=false native_credit=false",
            edges[0].source_arguments,
            edges[0].lowering_arguments,
            edges[0].copy_instructions,
            edges[0].parameter_codecs
        );
        assert!(
            matches!(
                super::super::lir::graph_projected(
                    &module,
                    ordinal,
                    lir,
                    Profile::ReadOnly,
                    &checked
                ),
                Err(ReadOnlySourceError::Lowering(
                    "requires an ordinary word-returning read-only LIR body"
                ))
            ),
            "the next vector-return/NativeDependency aggregate ABI frontier must remain"
        );
    }
}

#[test]
fn scalar_edge_projection_wrong_missing_foreign_and_nondominating_copies_refuse() {
    let (module, original) = fixture();
    let binding = check_scalar_block_arguments(&module, 0, &original).unwrap();
    let edge = &binding.transports()[0];
    let block = LirBlock(edge.lowering_block);
    let first = edge.copy_instructions[0];
    for mutation in 0..11 {
        let mut lir = original.clone();
        match mutation {
            0 => {
                lir.blocks
                    .get_mut(&block)
                    .unwrap()
                    .instructions
                    .remove(first);
                lir.trust_ir_origins.get_mut(&block).unwrap().remove(first);
            }
            1 => {
                lir.blocks.get_mut(&block).unwrap().instructions[first].args[0] = LirValue(1);
            } // U64 cannot replace pointer carrier/source occurrence
            2 => {
                lir.blocks.get_mut(&block).unwrap().instructions[first].results[0] = LirValue(999);
            }
            3 => {
                lir.blocks.get_mut(&block).unwrap().instructions[first].args[0] = LirValue(999);
            }
            4 => {
                let copy = lir.blocks[&block].instructions[first].clone();
                let entry = lir.entry_block;
                let pos = lir.blocks[&entry].instructions.len() - 1;
                lir.blocks
                    .get_mut(&entry)
                    .unwrap()
                    .instructions
                    .insert(pos, copy);
                lir.trust_ir_origins
                    .get_mut(&entry)
                    .unwrap()
                    .insert(pos, None);
            }
            5 => {
                let end = lir.blocks[&block].instructions.len() - 1;
                lir.blocks.get_mut(&block).unwrap().instructions[end].opcode = Opcode::Jump {
                    dest: lir.entry_block,
                };
            }
            6 => {
                lir.trust_ir_origins.get_mut(&block).unwrap()[first] =
                    Some(trust_cg_ir::TrustIrInstId(0));
            }
            7 => {
                let target = LirBlock(edge.lowering_target);
                lir.blocks.get_mut(&target).unwrap().params[0].1 = Type::I32;
            }
            8 => {
                let entry = lir.entry_block;
                let cond = lir
                    .blocks
                    .get_mut(&entry)
                    .unwrap()
                    .instructions
                    .last_mut()
                    .unwrap();
                if let Opcode::Brif { then_dest, .. } = &mut cond.opcode {
                    *then_dest = LirBlock(edge.lowering_target);
                }
            }
            9 => {
                let target = LirBlock(edge.lowering_target);
                let value = lir.blocks[&target].instructions[0].results[0];
                lir.blocks.get_mut(&block).unwrap().instructions[first].args[0] = value;
            }
            10 => {
                let entry = lir.entry_block;
                let branch = lir
                    .blocks
                    .get_mut(&entry)
                    .unwrap()
                    .instructions
                    .last_mut()
                    .unwrap();
                if let Opcode::Brif { cond, .. } = &mut branch.opcode {
                    *cond = LirValue(1);
                    branch.args = vec![LirValue(1)];
                }
            }
            _ => unreachable!(),
        }
        assert!(
            check_scalar_block_arguments(&module, 0, &lir).is_err(),
            "malformed edge mutation {mutation}"
        );
    }
    let mut source = module.clone();
    let entry_id = source.functions[0].entry;
    let entry = source.functions[0]
        .blocks
        .iter_mut()
        .find(|b| b.id == entry_id)
        .unwrap();
    if let Inst::CondBr { then_args, .. } = &mut entry.body.last_mut().unwrap().inst {
        then_args.clear();
    }
    assert!(check_scalar_block_arguments(&source, 0, &original).is_err());
}

#[test]
fn scalar_edge_projection_preserves_exact_existing_parallel_schedule_and_cycles() {
    use trust_cg_lower::instructions::Instruction;
    let v = LirValue;
    let actual = trust_cg_lower::block_arguments::schedule_parallel_copies(
        vec![
            (v(1), v(13)),
            (v(11), v(14)),
            (v(10), v(15)),
            (v(12), v(16)),
            (v(12), v(17)),
        ],
        || panic!("acyclic group needs no temporary"),
    );
    assert_eq!(
        actual.iter().map(|n| n.results[0].0).collect::<Vec<_>>(),
        [13, 17, 16, 15, 14]
    );
    let cycle = trust_cg_lower::block_arguments::schedule_parallel_copies(
        vec![(v(0), v(1)), (v(1), v(0))],
        || v(2),
    );
    let mut values = HashMap::from([(v(0), 17), (v(1), 29)]);
    for Instruction {
        opcode,
        args,
        results,
    } in cycle
    {
        assert!(matches!(opcode, Opcode::Copy));
        let value = values[&args[0]];
        values.insert(results[0], value);
    }
    assert_eq!(values[&v(0)], 29);
    assert_eq!(values[&v(1)], 17);
}

#[test]
fn scalar_edge_projection_oversized_source_inventory_refuses_before_identity_maps() {
    let (module, _) = fixture();
    let mut function = module.functions[0].clone();
    let node = function.blocks[0].body[0].clone();
    function.blocks[0].body = vec![node; MAX_INSTRUCTIONS + 1];
    assert!(matches!(
        source_edges(&function),
        Err(ReadOnlySourceError::Budget(
            "scalar edge source instructions"
        ))
    ));
    let mut function = module.functions[0].clone();
    let mut node = function.blocks[0].body[0].clone();
    node.results = (0..8).map(ValueId::new).collect();
    function.blocks[0].body = vec![node; MAX_VALUES / 8 + 1];
    assert!(matches!(
        source_edges(&function),
        Err(ReadOnlySourceError::Budget("scalar edge source values"))
    ));
}

#[test]
fn scalar_edge_projection_aggregate_parameters_and_wrong_scalar_hints_refuse() {
    let (module, lir) = fixture();
    let projection = check_scalar_block_arguments(&module, 0, &lir).unwrap();
    let target = LirBlock(projection.transports()[0].lowering_target);
    let mut changed = lir.clone();
    changed.blocks.get_mut(&target).unwrap().params[0].1 = Type::Struct(vec![Type::I64, Type::I64]);
    assert!(check_scalar_block_arguments(&module, 0, &changed).is_err());
    let mut changed = lir.clone();
    changed.value_types.insert(
        LirValue(projection.transports()[0].lowering_arguments[0]),
        Type::I32,
    );
    assert!(check_scalar_block_arguments(&module, 0, &changed).is_err());
    let mut huge = module.clone();
    huge.name = "x".repeat(4 * 1024 * 1024 + 1);
    assert!(matches!(
        check_scalar_block_arguments(&huge, 0, &lir),
        Err(ReadOnlySourceError::Budget(_))
    ));
}
