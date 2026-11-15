// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Actual original TY scalar-action preparation/encoding diagnostics.
//! The source is the complete captured Standalone module, not a reconstructed
//! scalar function. Only ordinary host target metadata is explicitly bound.
//! Observed MachIR, frame, memory-form decoding and encoder success provide no
//! Checked, write-effect, caller-memory, native-execution or replay authority.

#![cfg(all(target_arch = "aarch64", target_os = "macos"))]

use crate::CoreHostJitTarget;
use crate::compiler::{Compiler, CompilerConfig};
use crate::jit::JitFn;
use crate::legacy_module_capture::assert_legacy_module_image as assert_capture;
use crate::pipeline::{OptLevel, Pipeline, PipelineConfig, encode_function_with_fixups_and_sites};
use serde_json::{Value as Json, json};
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use trust_cg_ir::regs::{SpecialReg, preg_class};
use trust_cg_ir::{MachFunction, MachOperand};
use trust_cg_verify::aarch64_scalar_memory_proofs::{
    bind_scalar_memory_instruction, decode_scalar_memory_word,
};
use trust_cg_verify::lowering_proof::ProofObligation;
use trust_cg_verify::read_only_target::{
    ScalarMemoryTargetAccess, ScalarMemoryTargetEndpoint, ScalarMemoryTargetQueries,
    bind_scalar_memory_bytes, bind_scalar_memory_machine,
};
use trust_cg_verify::smt::SmtExpr;
use trust_cg_verify::source_bound_frame::{
    ScalarMemoryAccess, bind_read_only_source, bind_scalar_memory_source, source_admits_frame_owner,
};
use trust_ir::{CallingConv, InstShape, Linkage, Module, Ty};

fn sha256(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}

fn access_inventory(accesses: &[ScalarMemoryAccess]) -> Json {
    json!(
        accesses
            .iter()
            .map(|access| json!({
                "block": access.site.block,
                "instruction": access.site.instruction,
                "guard": access.guard.to_string(),
                "address": access.address.to_string(),
                "byte_width": access.byte_width,
                "alignment": access.alignment,
                "codec": format!("{:?}", access.codec),
            }))
            .collect::<Vec<_>>()
    )
}

fn pending_query_inventory(query: &ProofObligation) -> Json {
    json!({
        "name": query.name,
        "inputs": query.inputs,
        "fp_inputs": query.fp_inputs,
        "source_expression": query.trust_ir_expr.to_string(),
        "lowering_expression": query.aarch64_expr.to_string(),
        "source_sort": format!("{:?}", query.trust_ir_expr.sort()),
        "lowering_sort": format!("{:?}", query.aarch64_expr.sort()),
        "premise_count": query.preconditions.len(),
        "category": format!("{:?}", query.category),
        "machine_side_provenance": format!("{:?}", query.machine_side_provenance),
        "verdict": "not attempted; pending original-source query only",
    })
}

fn target_access_inventory(accesses: &[ScalarMemoryTargetAccess]) -> Json {
    json!(
        accesses
            .iter()
            .map(|access| json!({
                "step": access.step,
                "lane": access.lane,
                "guard": access.guard.to_string(),
                "address": access.address.to_string(),
                "byte_width": access.byte_width,
                "alignment": access.alignment,
            }))
            .collect::<Vec<_>>()
    )
}

fn target_query_inventory(queries: &ScalarMemoryTargetQueries<'_>) -> Json {
    let source = queries.source();
    let abi_arity = source.lir().signature.params.len();
    assert_eq!(
        abi_arity, 4,
        "exact original action ABI, not observer count"
    );
    let mut architectural_inputs: Vec<_> =
        (0..abi_arity).map(|i| (format!("abi_x{i}"), 64)).collect();
    let mut source_inputs = architectural_inputs.clone();
    source_inputs.push(("observe".into(), 64));
    assert_eq!(source.status_obligation().inputs, source_inputs);
    architectural_inputs.extend((abi_arity..31).map(|i| (format!("entry_x{i}"), 64)));
    architectural_inputs
        .extend(["entry_n", "entry_z", "entry_c", "entry_v"].map(|name| (name.into(), 1)));
    let mut expected_inputs = source_inputs;
    expected_inputs.extend(architectural_inputs[abi_arity..].iter().cloned());
    assert!(!queries.return_obligations().is_empty());
    assert_eq!(
        queries.return_obligations().len(),
        queries.memory_obligations().len()
    );
    assert_eq!(queries.read_obligations().len(), queries.reads().len());
    assert_eq!(queries.write_obligations().len(), queries.writes().len());
    let obligations = queries
        .return_obligations()
        .iter()
        .chain(queries.memory_obligations())
        .chain(queries.read_obligations())
        .chain(queries.write_obligations());
    for query in obligations {
        assert_eq!(
            query.inputs, expected_inputs,
            "{} ABI declarations",
            query.name
        );
        assert_eq!(
            query.preconditions.len(),
            source.source_geometry().len()
                + source.original_encoding_definitions().len()
                + queries.encoding_definitions().len(),
            "{} exact premise inventory",
            query.name
        );
    }
    // The free observer participates only in final-byte comparisons. Inspect
    // actual endpoint equations too: declaring entry_x4 would not catch a
    // driver that incorrectly initialized X4 with the observer's value.
    let mut pending: Vec<_> = queries.encoding_definitions().iter().collect();
    let mut seen = HashSet::new();
    while let Some(node) = pending.pop() {
        if !seen.insert(node as *const SmtExpr) {
            continue;
        }
        if let SmtExpr::Var { name, width } = node {
            assert!(
                architectural_inputs
                    .iter()
                    .any(|(allowed, bits)| allowed == name && bits == width),
                "nonarchitectural target input {name}:{width}"
            );
        }
        node.for_each_child(&mut |child| pending.push(child));
    }
    let endpoint = match queries.endpoint() {
        ScalarMemoryTargetEndpoint::Machine(_) => "actual allocated MachIR",
        ScalarMemoryTargetEndpoint::FinalBytes(_) => "independently decoded actual final words",
    };
    json!({
        "format": "ty-original-scalar-action-pending-target-queries-v1",
        "endpoint": endpoint,
        "inputs": expected_inputs,
        "abi_arity": abi_arity,
        "observer_is_architectural_input": false,
        "status_queries": queries.return_obligations().iter().map(pending_query_inventory).collect::<Vec<_>>(),
        "all_final_bytes_queries": queries.memory_obligations().iter().map(pending_query_inventory).collect::<Vec<_>>(),
        "read_demand_queries": queries.read_obligations().iter().map(pending_query_inventory).collect::<Vec<_>>(),
        "write_demand_queries": queries.write_obligations().iter().map(pending_query_inventory).collect::<Vec<_>>(),
        "reads": target_access_inventory(queries.reads()),
        "writes": target_access_inventory(queries.writes()),
        "encoding_definitions": queries.encoding_definitions().iter().map(ToString::to_string).collect::<Vec<_>>(),
        "return_query_count": queries.return_obligations().len(),
        "final_memory_query_count": queries.memory_obligations().len(),
        "read_demand_count": queries.read_obligations().len(),
        "write_demand_count": queries.write_obligations().len(),
        "query_count": queries.return_obligations().len() + queries.memory_obligations().len()
            + queries.read_obligations().len() + queries.write_obligations().len(),
        "encoding_definition_count": queries.encoding_definitions().len(),
        "original_source_encoding_definition_count": source.original_encoding_definitions().len(),
        "original_source_geometry_count": source.source_geometry().len(),
        "premise_scope": "complete original Core equations and original source geometry plus these endpoint equations; no unrelated LIR equations, target geometry, alias assumptions or caller permission",
        "boundary": "constructed unresolved original Core/target status, arbitrary final-byte and separate access-demand queries; no solver, replay, Checked/native, caller-memory or frame authority",
    })
}

fn register_width(operand: &MachOperand) -> Option<u32> {
    match operand {
        MachOperand::PReg(reg) | MachOperand::MemOp { base: reg, .. } => {
            Some(preg_class(*reg).size_bits())
        }
        MachOperand::VReg(reg) => Some(reg.class.size_bits()),
        MachOperand::Special(SpecialReg::SP | SpecialReg::XZR) => Some(64),
        MachOperand::Special(SpecialReg::WZR) => Some(32),
        _ => None,
    }
}

/// Inventory linked execution separately from arena/tombstone storage. This
/// does not turn annotation/ownership metadata into semantic proof credit.
fn inventory(machine: &MachFunction) -> Json {
    let mut layout = BTreeSet::new();
    for block in &machine.block_order {
        assert!((block.0 as usize) < machine.blocks.len());
        assert!(layout.insert(block.0), "duplicate actual layout block");
    }
    assert!(layout.contains(&machine.entry.0));
    let mut owners = vec![Vec::new(); machine.insts.len()];
    let mut blocks = Vec::new();
    for (block_index, block) in machine.blocks.iter().enumerate() {
        let mut local = BTreeSet::new();
        for (position, id) in block.insts.iter().enumerate() {
            assert!((id.0 as usize) < machine.insts.len());
            assert!(local.insert(id.0), "duplicate actual block instruction");
            owners[id.0 as usize].push((block_index, position));
        }
        for target in block.preds.iter().chain(&block.succs) {
            assert!((target.0 as usize) < machine.blocks.len());
        }
        blocks.push(json!({
            "arena_block_index": block_index,
            "in_layout": layout.contains(&(block_index as u32)),
            "instruction_ids": block.insts.iter().map(|id| id.0).collect::<Vec<_>>(),
            "predecessors": block.preds.iter().map(|id| id.0).collect::<Vec<_>>(),
            "successors": block.succs.iter().map(|id| id.0).collect::<Vec<_>>(),
            "loop_depth": block.loop_depth,
        }));
    }
    let mut arena_opcodes = BTreeMap::<String, usize>::new();
    let mut linked_opcodes = BTreeMap::<String, usize>::new();
    let mut linked_widths = BTreeMap::<u32, usize>::new();
    let mut memory_widths = BTreeMap::<String, usize>::new();
    let mut linked = 0;
    let mut reads = 0;
    let mut writes = 0;
    let mut opcode_reads = 0;
    let mut opcode_writes = 0;
    let mut virtual_operands = 0;
    let mut nodes = Vec::new();
    for (index, (inst, owner_list)) in machine.insts.iter().zip(&owners).enumerate() {
        assert!(
            owner_list.len() <= 1,
            "unique actual arena instruction ownership"
        );
        let live = owner_list
            .iter()
            .any(|(block, _)| layout.contains(&(*block as u32)));
        let opcode = format!("{:?}", inst.opcode);
        *arena_opcodes.entry(opcode.clone()).or_default() += 1;
        let widths: Vec<_> = inst.operands.iter().map(register_width).collect();
        let memory_form = if inst.reads_memory()
            || inst.writes_memory()
            || inst.opcode.default_flags().reads_memory()
            || inst.opcode.default_flags().writes_memory()
        {
            match bind_scalar_memory_instruction(inst) {
                Ok(binding) => {
                    if live {
                        *memory_widths
                            .entry(format!(
                                "{:?}:{}bytes",
                                binding.form.transfer, binding.form.access_bytes
                            ))
                            .or_default() += 1;
                    }
                    json!({"observation": "shared scalar operand binding only", "binding_debug": format!("{binding:#?}"), "access_bytes": binding.form.access_bytes})
                }
                Err(reason) => {
                    json!({"observation": "not a supported shared scalar memory operand binding", "refusal": reason})
                }
            }
        } else {
            Json::Null
        };
        if live {
            linked += 1;
            *linked_opcodes.entry(opcode.clone()).or_default() += 1;
            reads += usize::from(inst.reads_memory());
            writes += usize::from(inst.writes_memory());
            opcode_reads += usize::from(inst.opcode.default_flags().reads_memory());
            opcode_writes += usize::from(inst.opcode.default_flags().writes_memory());
            virtual_operands += inst.operands.iter().filter(|op| op.is_vreg()).count();
            for width in widths.iter().flatten() {
                *linked_widths.entry(*width).or_default() += 1;
            }
        }
        nodes.push(json!({
            "arena_inst_id": index,
            "owners_block_and_position": owner_list,
            "linked_in_layout": live,
            "opcode": opcode,
            "flags_bits": inst.flags.bits(),
            "reads_memory_flag": inst.reads_memory(),
            "writes_memory_flag": inst.writes_memory(),
            "reads_memory_opcode": inst.opcode.default_flags().reads_memory(),
            "writes_memory_opcode": inst.opcode.default_flags().writes_memory(),
            "operand_register_bits": widths,
            "implicit_defs_debug": format!("{:?}", inst.implicit_defs),
            "implicit_uses_debug": format!("{:?}", inst.implicit_uses),
            "lowering_provenance_debug": format!("{:?}", machine.inst_lowering_provenance(trust_cg_ir::InstId(index as u32))),
            "scalar_memory_form": memory_form,
            "original_prepared_inst_debug": format!("{inst:#?}"),
        }));
    }
    assert_eq!(arena_opcodes.values().sum::<usize>(), machine.insts.len());
    assert_eq!(linked_opcodes.values().sum::<usize>(), linked);
    assert_eq!(
        linked,
        machine
            .block_order
            .iter()
            .map(|id| machine.block(*id).insts.len())
            .sum::<usize>()
    );
    json!({
        "arena_block_count": machine.blocks.len(),
        "linked_block_count": machine.block_order.len(),
        "block_order": machine.block_order.iter().map(|id| id.0).collect::<Vec<_>>(),
        "entry_block_id": machine.entry.0,
        "arena_instruction_count": machine.insts.len(),
        "linked_instruction_count": linked,
        "unowned_arena_instruction_count": owners.iter().filter(|owner| owner.is_empty()).count(),
        "linked_reads_memory_flag_count": reads,
        "linked_writes_memory_flag_count": writes,
        "linked_reads_memory_opcode_count": opcode_reads,
        "linked_writes_memory_opcode_count": opcode_writes,
        "linked_virtual_operand_count": virtual_operands,
        "arena_opcode_histogram": arena_opcodes,
        "linked_opcode_histogram": linked_opcodes,
        "linked_register_operand_width_histogram": linked_widths,
        "linked_supported_scalar_memory_width_histogram": memory_widths,
        "width_scope": "all actual register operands counted by shared register classes; memory widths only when the existing shared scalar operand binding succeeds, with every refusal retained per node",
        "blocks": blocks,
        "arena_instructions": nodes,
    })
}

#[test]
fn actual_original_ty_scalar_action_captures_machine_and_final_bytes() {
    let captured: Json = serde_json::from_str(include_str!(
        "../../trust-cg-verify/tests/fixtures/ty_original_scalar_action.json"
    ))
    .unwrap();
    assert_eq!(captured["format"], "ty-original-scalar-action-source-v1");
    assert_eq!(captured["selection"]["unit_role"], "Next");
    assert_eq!(captured["selection"]["unit_key"], "next:Next@91-101");
    assert_eq!(captured["selection"]["function_id"], 60_002);
    assert_eq!(captured["selection"]["original_function_ordinal"], 3);
    assert_eq!(captured["original_core_instruction_count"], 117);
    assert_eq!(captured["original_core_block_count"], 16);
    let original: Module = serde_json::from_value(captured["module"].clone()).unwrap();
    assert!(original.target_info.is_none());
    assert_eq!(original.functions.len(), 10);
    assert_capture(&original, &captured["module"], "original module image");
    let host = CoreHostJitTarget::detect().expect("actual supported executing host");
    let mut module = original.clone();
    module.target_info = Some(host.trust_ir_target_info().clone());
    let mut restored = module.clone();
    restored.target_info = None;
    assert_capture(&restored, &captured["module"], "restored module image");
    let ordinal = 3;
    let source = &module.functions[ordinal];
    assert_eq!(source.id.index(), 60_002);
    assert_eq!(source.name, "tyw1_u1");
    assert_eq!(source.linkage, Linkage::Internal);
    assert_eq!(source.calling_conv, CallingConv::C);
    assert_eq!(source.blocks.len(), 16);
    assert_eq!(
        source.blocks.iter().map(|b| b.body.len()).sum::<usize>(),
        117
    );
    let mut source_opcodes = BTreeMap::new();
    for node in source.blocks.iter().flat_map(|block| &block.body) {
        *source_opcodes
            .entry(format!("{:?}", node.inst.shape()))
            .or_insert(0) += 1;
    }
    assert_eq!(source_opcodes.get("Load"), Some(&10));
    assert_eq!(source_opcodes.get("Store"), Some(&5));
    assert!(
        source
            .blocks
            .iter()
            .flat_map(|b| &b.body)
            .all(|node| !matches!(
                node.inst.shape(),
                InstShape::Call
                    | InstShape::CallIndirect
                    | InstShape::Invoke
                    | InstShape::InvokeIndirect
            ))
    );
    let signature = &module.func_types[source.ty.index() as usize];
    assert_eq!(signature.params, [Ty::Ptr, Ty::Ptr, Ty::Ptr, Ty::Ptr]);
    assert_eq!(signature.returns, [Ty::U64]);
    assert!(!signature.is_vararg);
    let module_json = serde_json::to_value(&module).unwrap();
    let (lir, proof_context) = trust_cg_lower::translate_function_with_license(
        source,
        &module,
        &crate::license_test_support::permit_unlicensed(),
    )
    .expect("actual original action adapter");
    let lir_json = serde_json::to_value(&lir).unwrap();
    let context_debug = format!("{proof_context:#?}");
    assert!(
        !source_admits_frame_owner(&lir),
        "existing affine owner stays outside pointer/writer source"
    );
    let read_only_refusal = bind_read_only_source(&module, ordinal, &lir)
        .err()
        .expect("the original action writes and is not a read-only source");
    let scalar_queries = bind_scalar_memory_source(&module, ordinal, &lir)
        .expect("actual original 117-node Next must construct scalar-memory source queries");
    assert!(std::ptr::eq(scalar_queries.module(), &module));
    assert!(std::ptr::eq(scalar_queries.source(), source));
    assert!(std::ptr::eq(scalar_queries.lir(), &lir));
    assert_eq!(
        scalar_queries.read_obligations().len(),
        scalar_queries.lowering_reads().len()
    );
    assert_eq!(
        scalar_queries.write_obligations().len(),
        scalar_queries.lowering_writes().len()
    );
    let scalar_query_inventory = json!({
        "format": "ty-original-scalar-action-pending-source-queries-v1",
        "original_function_id": source.id.index(),
        "original_function_ordinal": ordinal,
        "original_core_instruction_count": 117,
        "original_core_block_count": 16,
        "original_reads": access_inventory(scalar_queries.source_reads()),
        "original_writes": access_inventory(scalar_queries.source_writes()),
        "lowering_reads": access_inventory(scalar_queries.lowering_reads()),
        "lowering_writes": access_inventory(scalar_queries.lowering_writes()),
        "status_query": pending_query_inventory(scalar_queries.status_obligation()),
        "all_final_bytes_query": pending_query_inventory(scalar_queries.memory_obligation()),
        "read_demand_queries": scalar_queries.read_obligations().iter().map(pending_query_inventory).collect::<Vec<_>>(),
        "write_demand_queries": scalar_queries.write_obligations().iter().map(pending_query_inventory).collect::<Vec<_>>(),
        "encoding_definitions": scalar_queries.encoding_definitions().iter().map(ToString::to_string).collect::<Vec<_>>(),
        "source_geometry": scalar_queries.source_geometry().iter().map(ToString::to_string).collect::<Vec<_>>(),
        "source_read_count": scalar_queries.source_reads().len(),
        "source_write_count": scalar_queries.source_writes().len(),
        "lowering_read_count": scalar_queries.lowering_reads().len(),
        "lowering_write_count": scalar_queries.lowering_writes().len(),
        "query_count": 2 + scalar_queries.read_obligations().len() + scalar_queries.write_obligations().len(),
        "encoding_definition_count": scalar_queries.encoding_definitions().len(),
        "source_geometry_count": scalar_queries.source_geometry().len(),
        "premise_scope": "every query retains these original source geometry premises and BOTH stage semantic encoding-definition sets; definitions are equations, not caller permissions",
        "boundary": "pending Core/LIR status, arbitrary final-byte and access-demand relations only; no solver replay, native/Checked credit, machine correspondence, caller ownership or frame proof",
    });
    println!(
        "TY_SCALAR_ACTION_SOURCE_QUERIES source_reads={} source_writes={} lowering_reads={} lowering_writes={} queries={} definitions={} geometry={} checked_credit=false replay=false",
        scalar_queries.source_reads().len(),
        scalar_queries.source_writes().len(),
        scalar_queries.lowering_reads().len(),
        scalar_queries.lowering_writes().len(),
        2 + scalar_queries.read_obligations().len() + scalar_queries.write_obligations().len(),
        scalar_queries.encoding_definitions().len(),
        scalar_queries.source_geometry().len()
    );
    println!(
        "BEGIN_SCALAR_ACTION_SOURCE_QUERIES_JSON\n{}\nEND_SCALAR_ACTION_SOURCE_QUERIES_JSON",
        serde_json::to_string_pretty(&scalar_query_inventory).unwrap()
    );
    let mut captures = 0;
    for level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
        let pipeline = Pipeline::new(PipelineConfig {
            opt_level: level,
            verify: false,
            ..PipelineConfig::for_target(host.target_spec().triple())
        });
        let (machine, metrics) = pipeline
            .prepare_function_with_metrics_and_trust_ir_module(
                &lir,
                Some(&proof_context),
                &module,
                source,
            )
            .unwrap_or_else(|error| {
                panic!("actual original Next preparation at {level:?}: {error}")
            });
        assert_eq!(machine.name, source.name);
        assert!(metrics.pre_optimization_affine_lowering.is_none());
        let frame = metrics
            .frame_layout
            .as_ref()
            .expect("actual computed frame layout");
        let machine_debug = format!("{machine:#?}");
        let profile = inventory(&machine);
        let (bytes, fixups, sites) = encode_function_with_fixups_and_sites(&machine)
            .unwrap_or_else(|error| panic!("actual original Next encoder at {level:?}: {error}"));
        assert!(!bytes.is_empty());
        let (chunks, tail) = bytes.as_chunks::<4>();
        assert!(tail.is_empty());
        let words: Vec<_> = chunks.iter().copied().map(u32::from_le_bytes).collect();
        let mut decoded_memory_widths = BTreeMap::<String, usize>::new();
        let mut decoded_memory = Vec::new();
        for (index, word) in words.iter().copied().enumerate() {
            if let Some(binding) = decode_scalar_memory_word(word) {
                *decoded_memory_widths
                    .entry(format!(
                        "{:?}:{}bytes",
                        binding.form.transfer, binding.form.access_bytes
                    ))
                    .or_default() += 1;
                decoded_memory.push(json!({"word_index": index, "word": word, "binding_debug": format!("{binding:#?}"), "access_bytes": binding.form.access_bytes}));
            }
        }
        // Consume the exact encoder-produced relocation-origin sidecar. No
        // guessed one-word-per-MachInst correspondence or empty-fixup profile.
        assert_eq!(sites.len(), fixups.len());
        let mut fixup_inventory = Vec::new();
        for (index, site) in sites.iter().enumerate() {
            let fixup = fixups.get(index).unwrap();
            assert_eq!(site.fixup_index, index);
            assert_eq!(site.offset, fixup.offset);
            assert!(machine.block_order.contains(&site.block));
            assert!(machine.block(site.block).insts.contains(&site.inst));
            assert_eq!(machine.inst(site.inst).opcode, site.opcode);
            assert_eq!(site.offset % 4, 0);
            assert_eq!(words[site.offset as usize / 4], site.placeholder_word);
            fixup_inventory.push(json!({"fixup_index": index, "offset": site.offset, "origin_block": site.block.0, "origin_inst": site.inst.0, "opcode": format!("{:?}", site.opcode), "placeholder_word": site.placeholder_word, "fixup_debug": format!("{fixup:#?}")}));
        }
        let machine_queries =
            bind_scalar_memory_machine(&scalar_queries, &machine).unwrap_or_else(|error| {
                panic!("actual original Next pending MachIR at {level:?}: {error}")
            });
        let byte_queries =
            bind_scalar_memory_bytes(&scalar_queries, &bytes).unwrap_or_else(|error| {
                panic!("actual original Next pending final words at {level:?}: {error}")
            });
        assert!(std::ptr::eq(machine_queries.source(), &scalar_queries));
        assert!(std::ptr::eq(byte_queries.source(), &scalar_queries));
        let ScalarMemoryTargetEndpoint::Machine(retained_machine) = machine_queries.endpoint()
        else {
            panic!("retained actual machine endpoint")
        };
        assert!(std::ptr::eq(retained_machine, &machine));
        let ScalarMemoryTargetEndpoint::FinalBytes(retained_bytes) = byte_queries.endpoint() else {
            panic!("retained actual final-word endpoint")
        };
        assert!(std::ptr::eq(retained_bytes, bytes.as_slice()));
        let machine_pending = target_query_inventory(&machine_queries);
        let byte_pending = target_query_inventory(&byte_queries);
        println!(
            "TY_SCALAR_ACTION_TARGET_QUERIES level={level:?} machine_queries={} machine_reads={} machine_writes={} machine_definitions={} final_word_queries={} final_word_reads={} final_word_writes={} final_word_definitions={} checked_credit=false native_execution=false replay=false",
            machine_pending["query_count"],
            machine_queries.reads().len(),
            machine_queries.writes().len(),
            machine_queries.encoding_definitions().len(),
            byte_pending["query_count"],
            byte_queries.reads().len(),
            byte_queries.writes().len(),
            byte_queries.encoding_definitions().len()
        );
        assert_eq!(format!("{machine:#?}"), machine_debug);
        assert_eq!(serde_json::to_value(&module).unwrap(), module_json);
        assert_eq!(serde_json::to_value(&lir).unwrap(), lir_json);
        assert_eq!(format!("{proof_context:#?}"), context_debug);
        println!(
            "TY_SCALAR_ACTION_MACHINE_INVENTORY level={level:?} arena_instructions={} linked_instructions={} blocks={} stack_slots={} spill_slots={} frame_bytes={} encoded_words={} fixups={} reads={} writes={} checked_credit=false native_execution=false replay=false",
            machine.insts.len(),
            profile["linked_instruction_count"],
            machine.block_order.len(),
            machine.stack_slots.len(),
            metrics.spill_slot_count,
            frame.total_frame_size,
            words.len(),
            fixups.len(),
            profile["linked_reads_memory_flag_count"],
            profile["linked_writes_memory_flag_count"]
        );
        let payload = json!({
            "format": "ty-original-scalar-action-machine-capture-v1",
            "level": format!("{level:?}"),
            "stage": "ordinary original-source translate_function + diagnostic prepare_function_with_metrics_and_trust_ir_module + actual policy-qualified encode_function_with_fixups_and_sites; no Checked/write-effect/native/proof credit",
            "target_binding": "only CoreHostJitTarget::detect metadata supplied to original full Standalone module clone; selected source body, IDs, linkage, attributes, proof context and all sibling/module context unchanged",
            "original_ty_capture": captured,
            "target_bound_original_module": module,
            "original_lir": lir,
            "original_proof_context_debug": context_debug,
            "source_opcode_histogram": source_opcodes,
            "machine_profile": profile,
            "prepared_machine_debug": machine_debug,
            "frame_layout_debug": format!("{frame:#?}"),
            "preparation_metrics_debug": format!("{metrics:#?}"),
            "stack_slot_count": machine.stack_slots.len(),
            "stack_slots_debug": format!("{:#?}", machine.stack_slots),
            "spill_slot_count": metrics.spill_slot_count,
            "frame_bytes": frame.total_frame_size,
            "encoded_bytes": bytes,
            "encoded_bytes_sha256": sha256(&bytes),
            "encoded_words_little_endian": words,
            "decoded_supported_scalar_memory_width_histogram": decoded_memory_widths,
            "decoded_supported_scalar_memory_words": decoded_memory,
            "decoded_memory_scope": "existing independent scalar memory decoder observations only; all words retained, including words outside that decoder; not a write/memory correspondence proof",
            "encoded_fixups_debug": format!("{fixups:#?}"),
            "encoded_originating_sites_debug": format!("{sites:#?}"),
            "fixup_inventory": fixup_inventory,
            "source_admits_frame_owner": false,
            "read_only_source_refusal": format!("{read_only_refusal:?}"),
            "scalar_memory_source_query_count": 2 + scalar_queries.read_obligations().len() + scalar_queries.write_obligations().len(),
            "scalar_memory_source_query_status": "constructed and unresolved; separately captured before O0 loop",
            "read_only_target_status": "not attempted: original action source is not admitted by the read-only source contract",
            "scalar_memory_machine_pending": machine_pending,
            "scalar_memory_final_words_pending": byte_pending,
            "scalar_memory_target_query_status": "both actual endpoints must construct pending original-source queries at every O0-O3 level; every query remains unresolved",
            "boundary": "actual RW source/target correspondence is queried but unresolved; private-frame separation, caller live/initialized readable+writable storage and sink ABI, independent replay and native execution remain separate unresolved gates",
        });
        println!(
            "BEGIN_SCALAR_ACTION_MACHINE_CAPTURE_JSON {level:?}\n{}\nEND_SCALAR_ACTION_MACHINE_CAPTURE_JSON {level:?}",
            serde_json::to_string_pretty(&payload).unwrap()
        );
        captures += 1;
    }
    assert_eq!(captures, 4);
}

// Exact-width test carriers independently read from TY
// crates/tla-mc-native/src/abi.rs::{ModelCtx,SuccessorSink}; their offsets are
// exported by crates/tla-model-native/src/abi.rs and used in lower/gen.rs::emit.
// These local carriers are not permission, ABI replay or transcription evidence.
#[repr(C)]
#[derive(Clone, Copy)]
struct NativeModelCtx {
    abi_version: u32,
    state_words: u32,
    literal_pool: *const i64,
    literal_pool_len: u64,
    frontend: *const std::ffi::c_void,
    canon_host: *const std::ffi::c_void,
}

#[repr(C)]
#[derive(Clone, Copy)]
struct NativeSuccessorSink {
    states: *mut i64,
    actions: *mut u32,
    capacity: u32,
    len: u32,
}

#[repr(C)]
#[derive(Clone, Copy)]
struct Guarded<T> {
    before: u64,
    body: T,
    after: u64,
}

type ScalarAction =
    unsafe extern "C" fn(*const NativeModelCtx, *const u64, *mut u64, *mut u64) -> u64;

fn assert_native_carrier_layouts() {
    use std::mem::{align_of, offset_of, size_of};
    assert_eq!(size_of::<NativeModelCtx>(), 40);
    assert_eq!(align_of::<NativeModelCtx>(), 8);
    assert_eq!(offset_of!(NativeModelCtx, abi_version), 0);
    assert_eq!(offset_of!(NativeModelCtx, state_words), 4);
    assert_eq!(offset_of!(NativeModelCtx, literal_pool), 8);
    assert_eq!(offset_of!(NativeModelCtx, literal_pool_len), 16);
    assert_eq!(offset_of!(NativeModelCtx, frontend), 24);
    assert_eq!(offset_of!(NativeModelCtx, canon_host), 32);
    assert_eq!(size_of::<NativeSuccessorSink>(), 24);
    assert_eq!(align_of::<NativeSuccessorSink>(), 8);
    assert_eq!(offset_of!(NativeSuccessorSink, states), 0);
    assert_eq!(offset_of!(NativeSuccessorSink, actions), 8);
    assert_eq!(offset_of!(NativeSuccessorSink, capacity), 16);
    assert_eq!(offset_of!(NativeSuccessorSink, len), 20);
    assert_eq!(offset_of!(Guarded<NativeModelCtx>, body), 8);
    assert_eq!(offset_of!(Guarded<NativeModelCtx>, after), 48);
    assert_eq!(size_of::<Guarded<NativeModelCtx>>(), 56);
    assert_eq!(offset_of!(Guarded<NativeSuccessorSink>, body), 8);
    assert_eq!(offset_of!(Guarded<NativeSuccessorSink>, after), 32);
    assert_eq!(size_of::<Guarded<NativeSuccessorSink>>(), 40);
}

fn context_bytes(context: &Guarded<NativeModelCtx>) -> Vec<u8> {
    let mut bytes = Vec::new();
    bytes.extend_from_slice(&context.before.to_le_bytes());
    bytes.extend_from_slice(&context.body.abi_version.to_le_bytes());
    bytes.extend_from_slice(&context.body.state_words.to_le_bytes());
    bytes.extend_from_slice(&(context.body.literal_pool as u64).to_le_bytes());
    bytes.extend_from_slice(&context.body.literal_pool_len.to_le_bytes());
    bytes.extend_from_slice(&(context.body.frontend as u64).to_le_bytes());
    bytes.extend_from_slice(&(context.body.canon_host as u64).to_le_bytes());
    bytes.extend_from_slice(&context.after.to_le_bytes());
    assert_eq!(bytes.len(), std::mem::size_of_val(context));
    bytes
}

fn sink_bytes(sink: &Guarded<NativeSuccessorSink>) -> Vec<u8> {
    let mut bytes = Vec::new();
    bytes.extend_from_slice(&sink.before.to_le_bytes());
    bytes.extend_from_slice(&(sink.body.states as u64).to_le_bytes());
    bytes.extend_from_slice(&(sink.body.actions as u64).to_le_bytes());
    bytes.extend_from_slice(&sink.body.capacity.to_le_bytes());
    bytes.extend_from_slice(&sink.body.len.to_le_bytes());
    bytes.extend_from_slice(&sink.after.to_le_bytes());
    assert_eq!(bytes.len(), std::mem::size_of_val(sink));
    bytes
}

const ACTION_ERROR: u64 = (1 << 32) | 1;
const ACTION_FALLBACK: u64 = (3 << 32) | 4;
const ACTION_SINK_FULL: u64 = 3;
const WORD_CANARY: u64 = 0xa193_7e5b_2c60_d84f;
const ACTION_CANARY: u32 = 0xd37a_90c5;

fn integer(value: i64) -> u64 {
    (value as u64).wrapping_shl(3) | 1
}

#[derive(Clone, Copy, Debug)]
struct NativeSample {
    input: u64,
    arithmetic_status: u64,
    assigned: Option<u64>,
}

fn native_samples() -> Vec<NativeSample> {
    let mut samples = Vec::new();
    for value in [
        i64::from(i32::MIN),
        -2,
        -1,
        0,
        1,
        17,
        i64::from(i32::MAX) - 1,
    ] {
        samples.push(NativeSample {
            input: integer(value),
            arithmetic_status: 0,
            assigned: Some(integer(value + 1)),
        });
    }
    for value in [
        i64::from(i32::MIN) - 1,
        i64::from(i32::MAX),
        i64::from(i32::MAX) + 1,
        -(1i64 << 60),
        (1i64 << 60) - 1,
    ] {
        samples.push(NativeSample {
            input: integer(value),
            arithmetic_status: ACTION_ERROR,
            assigned: None,
        });
    }
    for input in [0, 2, 3, 5, 6, 7, u64::MAX] {
        samples.push(NativeSample {
            input,
            arithmetic_status: ACTION_ERROR,
            assigned: None,
        });
    }
    for input in [4, u64::MAX - 3] {
        samples.push(NativeSample {
            input,
            arithmetic_status: ACTION_FALLBACK,
            assigned: None,
        });
    }
    samples
}

#[derive(Clone, Copy, Debug)]
enum NativeAlias {
    Separate,
    ParentScratch,
    SinkStatesParent,
    SinkStatesScratch,
}

fn word_bytes(words: &[u64]) -> Vec<u8> {
    words.iter().flat_map(|word| word.to_le_bytes()).collect()
}

fn action_bytes(words: &[u32]) -> Vec<u8> {
    words.iter().flat_map(|word| word.to_le_bytes()).collect()
}

/// A test-private, lifetime-bound compatibility call. It accepts no caller
/// pointers: all live initialized storage, extents and aliases are supplied
/// internally. Safety here is a concrete test-call contract, not a compiler
/// certificate, K3 wrapper authority or caller permission inferred from Ptr.
struct UncheckedNative<'code> {
    function: JitFn<'code, ScalarAction>,
}

impl UncheckedNative<'_> {
    fn run(&self, sample: NativeSample, alias: NativeAlias, capacity: u32, len: u32) {
        assert!(len <= capacity && capacity <= 4);
        // Independently inspected TY exports: ModelCtx is repr(C), 40 bytes,
        // literal_pool at byte8; SuccessorSink is repr(C), 24 bytes, states@0,
        // actions@8, capacity:u32@16, len:u32@20. The generated unit frame has
        // sink pointer in word0. Every byte below is initialized; asserted
        // complete field coverage excludes Rust padding. Adjacent U32
        // capacity/len also detect overly wide stores.
        let mut pool = [WORD_CANARY, 1, 9, 10, 9, 1, !WORD_CANARY];
        let pool_ptr = pool.as_mut_ptr().wrapping_add(1);
        let mut context = Guarded {
            before: WORD_CANARY,
            body: NativeModelCtx {
                abi_version: 2,
                state_words: 1,
                literal_pool: pool_ptr.cast(),
                literal_pool_len: 5,
                frontend: std::ptr::null(),
                canon_host: std::ptr::null(),
            },
            after: !WORD_CANARY,
        };
        let mut parent = [
            WORD_CANARY,
            sample.input,
            0x1234_5678_9abc_def0,
            0x2345_6789_abcd_ef01,
            0x3456_789a_bcde_f012,
            !WORD_CANARY,
        ];
        let mut scratch = [
            WORD_CANARY,
            0x4567_89ab_cdef_0123,
            0x5678_9abc_def0_1234,
            0x6789_abcd_ef01_2345,
            0x789a_bcde_f012_3456,
            !WORD_CANARY,
        ];
        let mut states = [
            WORD_CANARY,
            0x89ab_cdef_0123_4567,
            0x9abc_def0_1234_5678,
            0xabcd_ef01_2345_6789,
            0xbcde_f012_3456_789a,
            !WORD_CANARY,
        ];
        let mut actions = [
            ACTION_CANARY,
            0xe1e2_e3e4,
            0xd1d2_d3d4,
            0xc1c2_c3c4,
            0xb1b2_b3b4,
            !ACTION_CANARY,
        ];
        let parent_ptr = parent.as_mut_ptr().wrapping_add(1);
        let scratch_ptr = if matches!(alias, NativeAlias::ParentScratch) {
            parent_ptr
        } else {
            scratch.as_mut_ptr().wrapping_add(1)
        };
        let state_ptr = match alias {
            NativeAlias::SinkStatesParent => parent_ptr,
            NativeAlias::SinkStatesScratch => scratch.as_mut_ptr().wrapping_add(1),
            NativeAlias::Separate | NativeAlias::ParentScratch => {
                states.as_mut_ptr().wrapping_add(1)
            }
        };
        let action_ptr = actions.as_mut_ptr().wrapping_add(1);
        let mut sink = Guarded {
            before: WORD_CANARY,
            body: NativeSuccessorSink {
                states: state_ptr.cast(),
                actions: action_ptr,
                capacity,
                len,
            },
            after: !WORD_CANARY,
        };
        let sink_ptr = std::ptr::addr_of_mut!(sink.body);
        let mut frame = [WORD_CANARY, sink_ptr as u64, !WORD_CANARY];
        let context_before = context;
        let pool_before = pool;
        let frame_before = frame;
        let mut expected_parent = parent;
        let mut expected_scratch = scratch;
        let mut expected_states = states;
        let mut expected_actions = actions;
        let mut expected_sink = sink;
        let scratch_value = sample.assigned.unwrap_or(sample.input);
        match alias {
            NativeAlias::ParentScratch => expected_parent[1] = scratch_value,
            _ => expected_scratch[1] = scratch_value,
        }
        let status = if sample.arithmetic_status != 0 {
            sample.arithmetic_status
        } else if len == capacity {
            ACTION_SINK_FULL
        } else {
            let at = len as usize + 1;
            let successor = sample.assigned.expect("successful x + 1 assigned value");
            match alias {
                NativeAlias::SinkStatesParent => expected_parent[at] = successor,
                NativeAlias::SinkStatesScratch => expected_scratch[at] = successor,
                NativeAlias::Separate | NativeAlias::ParentScratch => {
                    expected_states[at] = successor
                }
            }
            expected_actions[at] = 1; // Exact original Next unit/action id.
            expected_sink.body.len = len + 1;
            0
        };
        // SAFETY: the exact retained original function has four C Ptr lanes
        // and a U64 result. Context owns five aligned words, including the
        // actual original five-word literal pool pointer; parent/scratch and
        // all sink-state aliases own at least four aligned initialized words.
        // Frame word0 points to three aligned sink words; actions owns four
        // initialized U32 entries. 0<=len<=capacity<=4 bounds every append.
        // The aliases below are explicit valid low-level mutable storage,
        // without a readonly/noalias claim for parent/scratch/output. They
        // preserve ctx/pool and frame/sink pointer carriers. Every owner and
        // lifetime-bound code buffer stays alive for this synchronous call.
        let actual = unsafe {
            self.function.as_ref()(
                std::ptr::addr_of_mut!(context.body),
                parent_ptr,
                scratch_ptr,
                frame.as_mut_ptr().wrapping_add(1),
            )
        };
        assert_eq!(
            actual, status,
            "Unchecked native {sample:?}/{alias:?}/cap{capacity}/len{len}"
        );
        // Compare the ENTIRE allocated byte image, including every guard,
        // previous successor/action and unused tail, not just sink.len/output.
        for (name, actual, expected) in [
            ("pool", word_bytes(&pool), word_bytes(&pool_before)),
            (
                "context",
                context_bytes(&context),
                context_bytes(&context_before),
            ),
            ("parent", word_bytes(&parent), word_bytes(&expected_parent)),
            (
                "scratch",
                word_bytes(&scratch),
                word_bytes(&expected_scratch),
            ),
            ("states", word_bytes(&states), word_bytes(&expected_states)),
            (
                "actions",
                action_bytes(&actions),
                action_bytes(&expected_actions),
            ),
            ("sink", sink_bytes(&sink), sink_bytes(&expected_sink)),
            ("frame", word_bytes(&frame), word_bytes(&frame_before)),
        ] {
            assert_eq!(
                actual, expected,
                "{name}: {sample:?}/{alias:?}/cap{capacity}/len{len}"
            );
        }
    }
}

#[test]
fn unchecked_mac_original_scalar_action_preserves_full_status_memory_and_aliases() {
    assert_native_carrier_layouts();
    let captured: Json = serde_json::from_str(include_str!(
        "../../trust-cg-verify/tests/fixtures/ty_original_scalar_action.json"
    ))
    .unwrap();
    assert_eq!(captured["selection"]["function_id"], 60_002);
    assert_eq!(captured["selection"]["original_function_ordinal"], 3);
    assert_eq!(captured["literal_pool"], json!([1, 9, 10, 9, 1]));
    assert_eq!(captured["state_words"], 1);
    assert_eq!(captured["frame_words"], 1);
    assert_eq!(captured["native_frame_words"], 1);
    let original: Module = serde_json::from_value(captured["module"].clone()).unwrap();
    assert!(original.target_info.is_none());
    assert_eq!(original.functions.len(), 10);
    assert_capture(&original, &captured["module"], "original module image");
    let host = CoreHostJitTarget::detect().expect("actual supported executing Mac host");
    let mut module = original.clone();
    module.target_info = Some(host.trust_ir_target_info().clone());
    let mut restored = module.clone();
    restored.target_info = None;
    assert_capture(&restored, &captured["module"], "restored module image");
    let source = &module.functions[3];
    assert_eq!(source.id.index(), 60_002);
    assert_eq!(source.name, "tyw1_u1");
    assert_eq!(source.calling_conv, CallingConv::C);
    assert_eq!(source.linkage, Linkage::Internal);
    assert_eq!(source.blocks.len(), 16);
    assert_eq!(
        source
            .blocks
            .iter()
            .map(|block| block.body.len())
            .sum::<usize>(),
        117
    );
    let signature = &module.func_types[source.ty.index() as usize];
    assert_eq!(signature.params, [Ty::Ptr, Ty::Ptr, Ty::Ptr, Ty::Ptr]);
    assert_eq!(signature.returns, [Ty::U64]);
    assert!(!signature.is_vararg);
    assert!(
        source
            .attrs
            .params
            .iter()
            .all(|attr| !attr.noalias && !attr.readonly)
    );
    let module_json = serde_json::to_value(&module).unwrap();
    let (lir, proof_context) = trust_cg_lower::translate_function_with_license(
        source,
        &module,
        &crate::license_test_support::permit_unlicensed(),
    )
    .unwrap();
    let queries = bind_scalar_memory_source(&module, 3, &lir)
        .expect("native diagnostics retain pending queries from the SAME original source/LIR");
    assert!(std::ptr::eq(queries.source(), source));
    assert!(std::ptr::eq(queries.module(), &module));
    assert!(std::ptr::eq(queries.lir(), &lir));
    let lir_json = serde_json::to_value(&lir).unwrap();
    let context_debug = format!("{proof_context:#?}");
    let samples = native_samples();
    let mut compiled = 0;
    let mut calls = 0;
    for level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
        let compiler = Compiler::new_for_target_spec(
            CompilerConfig {
                opt_level: level,
                emit_proofs: false,
                ..CompilerConfig::for_host_jit_unchecked()
            },
            host.target_spec(),
        )
        .with_codegen_license(crate::license_test_support::permit_unlicensed());
        assert!(!compiler.config().emit_proofs);
        assert!(compiler.config().jit_validation_mode().is_unchecked());
        let result = compiler
            .compile_module_to_jit(&module, &HashMap::new())
            .unwrap_or_else(|error| {
                panic!("Unchecked original full-module Next {level:?}: {error}")
            });
        assert!(!result.buffer.code_slice().is_empty());
        assert_eq!(result.metrics.function_count, module.functions.len());
        assert!(result.proofs.is_none());
        let validation = result
            .validation
            .as_ref()
            .expect("actual JIT validation provenance");
        assert!(validation.mode.is_unchecked());
        assert!(!validation.every_function_semantics_verified());
        assert!(
            validation
                .functions
                .iter()
                .all(|function| !function.verified)
        );
        // SAFETY: source/signature assertions above establish this exact four
        // pointer C ABI and U64 result; the selected body and module were not
        // projected, exported, renamed or rewritten. This compatibility symbol
        // lookup grants no source/frame/byte correspondence or publication seal.
        let function = unsafe {
            result
                .buffer
                .get_fn_bound::<ScalarAction>(&source.name)
                .unwrap()
        };
        let native = UncheckedNative { function };
        for &sample in &samples {
            for alias in [
                NativeAlias::Separate,
                NativeAlias::ParentScratch,
                NativeAlias::SinkStatesParent,
                NativeAlias::SinkStatesScratch,
            ] {
                for (capacity, len) in [(0, 0), (1, 0), (1, 1), (4, 0), (4, 1), (4, 4)] {
                    native.run(sample, alias, capacity, len);
                    calls += 1;
                }
            }
        }
        assert_eq!(serde_json::to_value(&module).unwrap(), module_json);
        assert_eq!(serde_json::to_value(&lir).unwrap(), lir_json);
        assert_eq!(format!("{proof_context:#?}"), context_debug);
        compiled += 1;
    }
    assert_eq!(compiled, 4);
    assert_eq!(calls, samples.len() * 4 * 6 * 4);
    println!(
        "TY_ORIGINAL_SCALAR_ACTION_NATIVE compiled={compiled} calls={calls} full_module_functions=10 original_function_id=60002 full_status=true full_initialized_buffers_and_sentinels=true capacities=0,1,4 alias_profiles=4 validation=Unchecked emit_proofs=false independent_replay=false machine_correspondence=false private_frame_proof=false caller_authority_from_Ptr=false"
    );
}
