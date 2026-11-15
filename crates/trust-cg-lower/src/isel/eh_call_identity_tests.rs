// Author: Andrew Yates | Copyright 2026 | License: Apache-2.0

use super::*;
use trust_cg_ir::function::EhCallSiteBindings;

fn actual_selected() -> InstructionSelector {
    let mut selector = InstructionSelector::new("exact_invoke".to_owned(), Signature::default());
    selector.set_abi_variant(AArch64AbiVariant::Darwin);
    for block in [Block(0), Block(1), Block(2)] {
        selector.func.ensure_block(block);
    }
    let helper = || Instruction {
        opcode: Opcode::Call {
            name: "same_symbol".to_owned(),
            binding: DirectCallBinding::Interposable,
        },
        args: Vec::new(),
        results: Vec::new(),
    };
    selector
        .select_block(
            Block(0),
            &[
                helper(),
                helper(),
                Instruction {
                    opcode: Opcode::Invoke {
                        binding: DirectCallBinding::Interposable,
                        name: "same_symbol".to_owned(),
                        normal_dest: Block(1),
                        unwind_dest: Block(2),
                    },
                    args: Vec::new(),
                    results: Vec::new(),
                },
            ],
        )
        .unwrap();
    selector
        .select_block(
            Block(1),
            &[Instruction {
                opcode: Opcode::Return,
                args: Vec::new(),
                results: Vec::new(),
            }],
        )
        .unwrap();
    selector
        .select_block(
            Block(2),
            &[
                Instruction {
                    opcode: Opcode::LandingPad {
                        catch_type_indices: Vec::new(),
                        is_cleanup: true,
                    },
                    args: Vec::new(),
                    results: vec![Value(0), Value(1)],
                },
                Instruction {
                    opcode: Opcode::Resume,
                    args: vec![Value(0)],
                    results: Vec::new(),
                },
            ],
        )
        .unwrap();
    selector
}

#[test]
fn actual_invoke_call_emitter_returns_exact_sparse_coordinate() {
    let selector = actual_selected();
    assert_eq!(selector.func.eh_invoke_bindings.len(), 1);
    let binding = selector.func.eh_invoke_bindings[0];
    assert_eq!(binding.call_block, Block(0));
    assert_eq!(binding.call_index, 2);
    let mut source = selector.func.eh_info.clone();
    source.personality = Some("rust_eh_personality".to_owned());
    let machine = selector
        .finalize_with_eh_info(&source)
        .unwrap()
        .to_ir_func();
    let EhCallSiteBindings::ExactInstructions(bindings) = &machine.eh_metadata.call_site_bindings
    else {
        panic!("actual Invoke selection must not request legacy inference");
    };
    assert_eq!(bindings.len(), 1);
    assert_eq!(bindings[0].call_inst, machine.blocks[0].insts[2]);
    assert_eq!(bindings[0].call_block, trust_cg_ir::BlockId(0));
    assert_eq!(bindings[0].landing_pad_block, trust_cg_ir::BlockId(2));
    assert_eq!(
        machine.blocks[0]
            .insts
            .iter()
            .filter(|&&id| machine.inst(id).is_call())
            .count(),
        3
    );
    machine.admit_id_counters().unwrap();
}

#[test]
fn checked_finalizers_refuse_missing_duplicate_orphan_and_stale_coordinates() {
    for mutation in 0..5 {
        let mut selector = actual_selected();
        let source = selector.func.eh_info.clone();
        match mutation {
            0 => selector.func.eh_invoke_bindings.clear(),
            1 => selector
                .func
                .eh_invoke_bindings
                .push(selector.func.eh_invoke_bindings[0]),
            2 => selector.func.eh_invoke_bindings[0].landing_pad_block = Block(1),
            3 => selector.func.eh_invoke_bindings[0].call_index = 3,
            4 => selector.func.eh_invoke_bindings[0].call_index = usize::MAX,
            _ => unreachable!(),
        }
        let error = if mutation % 2 == 0 {
            selector.finalize_with_eh_info(&source).unwrap_err()
        } else {
            selector
                .finalize_with_value_map_and_eh_info(&source)
                .unwrap_err()
        };
        assert!(matches!(error, ISelError::InvalidEhMetadata(_)));
    }
}

#[test]
fn infallible_projection_keeps_unmapped_coordinates_as_refusal_evidence() {
    let mut selected = actual_selected().finalize();
    selected.eh_invoke_bindings[0].call_index = usize::MAX;
    let machine = selected.to_ir_func();
    let EhCallSiteBindings::ExactInstructions(bindings) = &machine.eh_metadata.call_site_bindings
    else {
        panic!("malformed modern data must not request legacy inference");
    };
    assert_eq!(bindings.len(), 2);
    assert_eq!(bindings[0], bindings[1]);
    assert!(machine.admit_id_counters().is_err());
}

#[test]
fn ordinary_calls_keep_empty_sparse_storage_and_legacy_machine_defaults() {
    let mut selector = InstructionSelector::new("ordinary".to_owned(), Signature::default());
    selector.set_abi_variant(AArch64AbiVariant::Darwin);
    selector.func.ensure_block(Block(0));
    selector
        .select_call("ordinary", &[], &[], &[], Block(0))
        .unwrap();
    let selected = selector
        .finalize_with_eh_info(&EhFunctionInfo::default())
        .unwrap();
    assert!(selected.eh_invoke_bindings.is_empty());
    assert_eq!(selected.eh_invoke_bindings.capacity(), 0);
    assert!(matches!(
        selected.to_ir_func().eh_metadata.call_site_bindings,
        EhCallSiteBindings::LegacyBlocks
    ));
}
