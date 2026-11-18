//! AOT counter admission and transactional insertion regressions.

use super::*;
use std::sync::Mutex;
use trust_cg_ir::Signature;
use trust_cg_opt::pgo::CounterMap;

fn function(blocks: usize) -> IrMachFunction {
    let mut function = IrMachFunction::new("aot_profile".into(), Signature::new(vec![], vec![]));
    for _ in 1..blocks {
        function.create_block();
    }
    for block in function.block_order.clone() {
        let ret = function.push_inst(IrMachInst::new(IrOpcode::Ret, vec![]));
        function.append_inst(block, ret);
    }
    function
}

fn refused_without_changes(func: &mut IrMachFunction, sink: &Arc<Mutex<CounterMap>>) {
    let before_function = format!("{func:?}");
    let before_map = sink
        .lock()
        .unwrap_or_else(|error| error.into_inner())
        .clone();
    let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        inject_aot_block_counters(func, sink)
    }));
    assert!(outcome.is_ok(), "admission must return an error, not panic");
    assert!(
        outcome.unwrap().is_err(),
        "invalid admission must be refused"
    );
    assert_eq!(format!("{func:?}"), before_function);
    assert_eq!(
        *sink.lock().unwrap_or_else(|error| error.into_inner()),
        before_map
    );
}

#[test]
fn aot_counter_boundary_first_block_register_exhaustion_is_atomic() {
    let mut func = function(1);
    func.next_vreg = u32::MAX - 3;
    refused_without_changes(&mut func, &Arc::new(Mutex::new(CounterMap::new())));
}

#[test]
fn aot_counter_boundary_later_block_register_exhaustion_is_atomic() {
    let mut func = function(2);
    func.next_vreg = u32::MAX - 7;
    refused_without_changes(&mut func, &Arc::new(Mutex::new(CounterMap::new())));
}

#[test]
fn aot_counter_boundary_stale_counter_is_refused_and_orphans_and_noalias_ids_count() {
    for noalias in [false, true] {
        let mut func = function(1);
        if noalias {
            func.noalias_params.push(1000);
        } else {
            func.push_inst(IrMachInst::new(
                IrOpcode::MovR,
                vec![IrOperand::VReg(VReg::new(1000, RegClass::Gpr64))],
            ));
        }
        // L10-P5: a counter below a detached instruction's or a noalias
        // parameter's register is refused by name, not raised past it.
        let sink = Arc::new(Mutex::new(CounterMap::new()));
        let mut stale = func.clone();
        refused_without_changes(&mut stale, &sink);
        match inject_aot_block_counters(&mut stale, &sink) {
            Err(PipelineError::MachIdAdmission(refusal)) => {
                assert_eq!(refusal.boundary, "AOT profile instrumentation entry");
                assert!(matches!(
                    refusal.error,
                    trust_cg_ir::MachIdAdmissionError::StaleCounter { live_id: 1000, .. }
                ));
            }
            other => panic!("expected an identity refusal, got {other:?}"),
        }

        // Admitted, the counter registers start at the counter, above both.
        func.next_vreg = 1001;
        let original_insts = func.insts.len();
        inject_aot_block_counters(&mut func, &sink).unwrap();
        let ids: BTreeSet<_> = func.insts[original_insts..]
            .iter()
            .flat_map(|inst| &inst.operands)
            .filter_map(|operand| match operand {
                IrOperand::VReg(reg) => Some(reg.id),
                _ => None,
            })
            .collect();
        assert_eq!(ids, BTreeSet::from([1001, 1002, 1003, 1004]));
        assert_eq!(func.next_vreg, 1005);
        assert_eq!(sink.lock().unwrap().len(), 1);
    }
}

#[test]
fn aot_counter_boundary_poisoned_metadata_is_not_recovered() {
    let sink = Arc::new(Mutex::new(CounterMap::new()));
    let poison = Arc::clone(&sink);
    assert!(
        std::thread::spawn(move || {
            let _guard = poison.lock().unwrap();
            panic!("deliberate metadata poison");
        })
        .join()
        .is_err()
    );
    refused_without_changes(&mut function(1), &sink);
}

#[test]
fn aot_counter_boundary_invalid_later_layout_is_atomic() {
    for defect in 0..6 {
        let mut func = function(2);
        match defect {
            0 => func.block_order[1] = BlockId(99),
            1 => func.block_order[1] = func.entry,
            2 => func.blocks[1].insts.push(InstId(99)),
            3 => func.blocks[1].insts = func.blocks[0].insts.clone(),
            4 => {
                let phi = func.push_inst(IrMachInst::new(IrOpcode::Phi, vec![]));
                func.blocks[1].insts.push(phi);
            }
            5 => {
                func.block_order.remove(0);
            }
            _ => unreachable!(),
        }
        refused_without_changes(&mut func, &Arc::new(Mutex::new(CounterMap::new())));
    }
}

#[test]
fn aot_counter_boundary_final_register_group_is_usable() {
    let mut func = function(2);
    func.next_vreg = u32::MAX - 8;
    let sink = Arc::new(Mutex::new(CounterMap::new()));
    inject_aot_block_counters(&mut func, &sink).unwrap();
    let ids: BTreeSet<_> = func
        .insts
        .iter()
        .flat_map(|inst| &inst.operands)
        .filter_map(|operand| match operand {
            IrOperand::VReg(reg) => Some(reg.id),
            _ => None,
        })
        .collect();
    assert_eq!(ids, (u32::MAX - 8..u32::MAX).collect());
    assert_eq!(func.next_vreg, u32::MAX);
    assert_eq!(sink.lock().unwrap().len(), 2);
}

#[test]
fn aot_counter_boundary_existing_maximum_id_cannot_be_reused() {
    for noalias in [false, true] {
        let mut func = function(1);
        if noalias {
            func.noalias_params.push(u32::MAX);
        } else {
            func.push_inst(IrMachInst::new(
                IrOpcode::MovR,
                vec![IrOperand::VReg(VReg::new(u32::MAX, RegClass::Gpr64))],
            ));
        }
        refused_without_changes(&mut func, &Arc::new(Mutex::new(CounterMap::new())));
    }
}

fn previous_sites(count: u32) -> CounterMap {
    CounterMap {
        sites: (0..count)
            .map(|index| trust_cg_opt::pgo::CounterSite {
                function: "previous".into(),
                block_id: index,
                counter_index: index,
                symbol: trust_cg_opt::pgo::counter_symbol("previous", index),
            })
            .collect(),
    }
}

#[test]
fn aot_counter_boundary_last_scaled_offset_and_ceiling_diagnostic() {
    let sink = Arc::new(Mutex::new(previous_sites(4095)));
    let mut func = function(1);
    inject_aot_block_counters(&mut func, &sink).unwrap();
    let offsets: Vec<_> = func
        .insts
        .iter()
        .filter(|inst| matches!(inst.opcode, IrOpcode::LdrRI | IrOpcode::StrRI))
        .map(|inst| inst.operands[2].clone())
        .collect();
    assert_eq!(
        offsets,
        [IrOperand::Imm(4095 * 8), IrOperand::Imm(4095 * 8)]
    );
    assert_eq!(
        sink.lock().unwrap().sites.last().unwrap().counter_index,
        4095
    );
    let mut next = function(1);
    next.name = "next".into();
    assert!(matches!(
        inject_aot_block_counters(&mut next, &sink),
        Err(PipelineError::AotProfile(
            crate::AotProfileError::CounterIndexTooLarge {
                index: 4096,
                max: 4095,
                ..
            }
        ))
    ));
    refused_without_changes(&mut next, &sink);
    refused_without_changes(
        &mut function(2),
        &Arc::new(Mutex::new(previous_sites(4095))),
    );
}

#[test]
fn aot_counter_boundary_inconsistent_or_duplicate_metadata_is_refused() {
    for defect in 0..3 {
        let mut map = previous_sites(2);
        match defect {
            0 => map.sites[1].counter_index = 0,
            1 => map.sites[1].block_id = 0,
            2 => map.sites[0].function = "aot_profile".into(),
            _ => unreachable!(),
        }
        let sink = Arc::new(Mutex::new(map));
        assert!(matches!(
            inject_aot_block_counters(&mut function(1), &sink),
            Err(PipelineError::AotProfile(
                crate::AotProfileError::InvalidCounterMap { .. }
            ))
        ));
        refused_without_changes(&mut function(1), &sink);
    }
}

#[test]
fn aot_counter_boundary_leading_phis_and_original_instruction_ids_are_preserved() {
    let mut func = function(2);
    let original_returns: Vec<_> = func.blocks.iter().map(|block| block.insts[0]).collect();
    let phi = func.push_inst(IrMachInst::new(
        IrOpcode::Phi,
        vec![
            IrOperand::VReg(VReg::new(1, RegClass::Gpr64)),
            IrOperand::VReg(VReg::new(0, RegClass::Gpr64)),
            IrOperand::Block(func.entry),
        ],
    ));
    func.blocks[1].insts.insert(0, phi);
    // The phi names v0 and v1, which the counter must cover (L10-P5).
    func.next_vreg = 2;
    let old_arena = format!("{:?}", func.insts);
    let sink = Arc::new(Mutex::new(CounterMap::new()));
    inject_aot_block_counters(&mut func, &sink).unwrap();
    assert_eq!(format!("{:?}", &func.insts[..3]), old_arena);
    assert_eq!(
        func.blocks[0].insts,
        [
            InstId(3),
            InstId(4),
            InstId(5),
            InstId(6),
            InstId(7),
            original_returns[0]
        ]
    );
    assert_eq!(
        func.blocks[1].insts,
        [
            phi,
            InstId(8),
            InstId(9),
            InstId(10),
            InstId(11),
            InstId(12),
            original_returns[1]
        ]
    );
    assert_eq!(func.block_order, [BlockId(0), BlockId(1)]);
}

#[test]
fn aot_counter_boundary_concurrent_functions_keep_contiguous_disjoint_sites() {
    let sink = Arc::new(Mutex::new(CounterMap::new()));
    let jobs: Vec<_> = (0..8)
        .map(|index| {
            let sink = Arc::clone(&sink);
            std::thread::spawn(move || {
                let mut func = function(2);
                func.name = format!("worker_{index}");
                inject_aot_block_counters(&mut func, &sink).unwrap();
                func
            })
        })
        .collect();
    let functions: Vec<_> = jobs.into_iter().map(|job| job.join().unwrap()).collect();
    let map = sink.lock().unwrap();
    assert_eq!(map.len(), 16);
    for (index, pair) in map.sites.as_chunks::<2>().0.iter().enumerate() {
        assert_eq!(pair[0].function, pair[1].function);
        assert_eq!(pair[0].counter_index, index as u32 * 2);
        assert_eq!(pair[1].counter_index, index as u32 * 2 + 1);
    }
    for func in functions {
        let actual: Vec<_> = func
            .insts
            .iter()
            .filter(|inst| inst.opcode == IrOpcode::LdrRI)
            .map(|inst| inst.operands[2].clone())
            .collect();
        let expected: Vec<_> = map
            .sites_for(&func.name)
            .map(|site| IrOperand::Imm(i64::from(site.counter_index) * 8))
            .collect();
        assert_eq!(actual, expected);
    }
}

#[test]
fn aot_counter_boundary_empty_layout_is_an_unchanged_noop_at_capacity() {
    let mut func = function(1);
    func.block_order.clear();
    func.next_vreg = u32::MAX;
    let before = format!("{func:?}");
    let map = previous_sites(4096);
    let sink = Arc::new(Mutex::new(map.clone()));
    inject_aot_block_counters(&mut func, &sink).unwrap();
    assert_eq!(format!("{func:?}"), before);
    assert_eq!(*sink.lock().unwrap(), map);
}

#[test]
fn aot_counter_public_ir_routes_propagate_poison_refusal() {
    let sink = Arc::new(Mutex::new(CounterMap::new()));
    let poison = Arc::clone(&sink);
    assert!(
        std::thread::spawn(move || {
            let _guard = poison.lock().unwrap();
            panic!("deliberate public-route metadata poison");
        })
        .join()
        .is_err()
    );
    let pipeline = profile_pipeline(sink);
    for compile in [false, true] {
        let mut func = function(1);
        let result = if compile {
            pipeline.compile_ir_function(&mut func).map(|_| ())
        } else {
            pipeline.prepare_ir_function(&mut func)
        };
        assert!(matches!(
            result,
            Err(PipelineError::AotProfile(
                crate::AotProfileError::PoisonedCounterMap { .. }
            ))
        ));
    }
}

fn lir_function() -> trust_cg_lower::Function {
    use trust_cg_lower::function::{BasicBlock, Function, Signature};
    use trust_cg_lower::instructions::{Block, Instruction, Opcode};
    let mut input = Function::new("lir_profile", Signature::default());
    input.block_order.push(Block(0));
    input.blocks.insert(
        Block(0),
        BasicBlock {
            instructions: vec![Instruction {
                opcode: Opcode::Return,
                args: vec![],
                results: vec![],
            }],
            source_locs: vec![None],
            ..BasicBlock::default()
        },
    );
    input
}

#[test]
fn aot_counter_public_lir_preparation_retains_instrumentation() {
    let sink = Arc::new(Mutex::new(CounterMap::new()));
    let prepared = profile_pipeline(Arc::clone(&sink))
        .prepare_function(&lir_function())
        .unwrap();
    assert_eq!(sink.lock().unwrap().len(), 1);
    assert!(
        prepared
            .insts
            .iter()
            .any(|inst| inst.opcode == IrOpcode::Adrp)
    );
}

fn profile_pipeline(sink: Arc<Mutex<CounterMap>>) -> Pipeline {
    Pipeline::new(PipelineConfig {
        opt_level: OptLevel::O0,
        verify: true,
        target_triple: "aarch64-apple-darwin".into(),
        ..PipelineConfig::default()
    })
    .with_profile_generate_sink(sink)
}

#[test]
fn aot_counter_public_lir_compilation_honors_profile_generation_sink() {
    let sink = Arc::new(Mutex::new(CounterMap::new()));
    let object = profile_pipeline(Arc::clone(&sink))
        .compile_function(&lir_function())
        .unwrap();
    assert_eq!(sink.lock().unwrap().len(), 1);
    let parsed = crate::macho::linker::MachOParser::parse(&object).unwrap();
    assert!(
        parsed
            .symbols
            .iter()
            .any(|symbol| symbol.name.ends_with(PGO_COUNTER_ARRAY_SYMBOL))
    );
}

#[test]
fn aot_counter_public_prepare_ir_honors_profile_generation_sink() {
    let sink = Arc::new(Mutex::new(CounterMap::new()));
    let mut func = function(1);
    profile_pipeline(Arc::clone(&sink))
        .prepare_ir_function(&mut func)
        .unwrap();
    assert_eq!(sink.lock().unwrap().len(), 1);
    assert!(func.insts.iter().any(|inst| inst.opcode == IrOpcode::Adrp));
}

#[test]
fn aot_counter_public_compile_ir_honors_profile_generation_sink() {
    let sink = Arc::new(Mutex::new(CounterMap::new()));
    let object = profile_pipeline(Arc::clone(&sink))
        .compile_ir_function(&mut function(1))
        .unwrap();
    assert_eq!(sink.lock().unwrap().len(), 1);
    let parsed = crate::macho::linker::MachOParser::parse(&object).unwrap();
    assert!(
        parsed
            .symbols
            .iter()
            .any(|symbol| symbol.name.ends_with(PGO_COUNTER_ARRAY_SYMBOL))
    );
}

#[test]
fn aot_counter_public_absent_sink_preserves_the_function_and_emits_no_counter_symbol() {
    let mut pipeline = profile_pipeline(Arc::new(Mutex::new(CounterMap::new())));
    pipeline.profile_generate_sink = None;
    let mut func = function(1);
    let before = format!("{func:?}");
    pipeline.inject_profile_counters(&mut func).unwrap();
    assert_eq!(format!("{func:?}"), before);
    let object = pipeline.compile_ir_function(&mut func).unwrap();
    let parsed = crate::macho::linker::MachOParser::parse(&object).unwrap();
    assert!(
        parsed
            .symbols
            .iter()
            .all(|symbol| !symbol.name.ends_with(PGO_COUNTER_ARRAY_SYMBOL))
    );
}

#[test]
fn aot_counter_public_parallel_batch_reserves_sites_in_input_order() {
    use trust_cg_lower::instructions::{Instruction, Opcode, Value};
    // The verifier captures its worker policy for the process lifetime. Select
    // this test's cap before any verifier use, independently of sibling tests;
    // changing a previously captured policy must continue to refuse.
    const CHILD: &str = "AOT_COUNTER_PARALLEL_BATCH_CHILD";
    const PASSED: &str = "[AOT-COUNTER-PARALLEL-BATCH-PASS]";
    if std::env::var_os(CHILD).is_none() {
        let output = std::process::Command::new(
            std::env::current_exe().expect("current trust-cg-codegen test executable"),
        )
        .args([
            "pipeline::aot_profile_tests::aot_counter_public_parallel_batch_reserves_sites_in_input_order",
            "--exact",
            "--nocapture",
            "--test-threads=1",
        ])
        .env(CHILD, "1")
        .env(crate::resource_limits::TRUST_CG_MAX_PARALLELISM_ENV, "2")
        .output()
        .expect("run isolated AOT counter batch test");
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            output.status.success(),
            "isolated counter batch failed:\nstdout:\n{}\nstderr:\n{stderr}",
            String::from_utf8_lossy(&output.stdout)
        );
        assert!(
            stderr.contains(PASSED),
            "counter batch assertions did not execute: {stderr}"
        );
        return;
    }
    assert_eq!(std::env::var(CHILD).unwrap(), "1");
    crate::env_lock::with_env_edits(|env| {
        env.set(crate::resource_limits::TRUST_CG_MAX_PARALLELISM_ENV, "2");
        let mut inputs: Vec<_> = (0..32)
            .map(|index| {
                let mut input = lir_function();
                input.name = format!("batch_{index}");
                (input, trust_cg_lower::ProofContext::default())
            })
            .collect();
        // Unequal real verification/selection work exposes completion-order
        // reservation when a two-worker host is available. The contract still
        // applies on hosts whose budget selects the existing serial fallback.
        let first = &mut inputs[0].0;
        let mut prefix = Vec::new();
        for index in 0..512 {
            first.value_types.insert(Value(index), LowerType::I64);
            prefix.push(Instruction {
                opcode: Opcode::Iconst {
                    ty: LowerType::I64,
                    imm: i64::from(index),
                },
                args: vec![],
                results: vec![Value(index)],
            });
        }
        let entry = first.blocks.get_mut(&first.entry_block).unwrap();
        prefix.append(&mut entry.instructions);
        entry.instructions = prefix;
        entry.source_locs = vec![None; entry.instructions.len()];
        eprintln!(
            "[aot-profile-batch] admitted workers: {:?}",
            crate::resource_limits::worker_count_for_items(inputs.len()).unwrap()
        );
        let sink = Arc::new(Mutex::new(CounterMap::new()));
        let prepared = profile_pipeline(Arc::clone(&sink)).prepare_functions_parallel(&inputs);
        let prepared: Vec<_> = prepared.into_iter().map(Result::unwrap).collect();
        let names: Vec<_> = prepared
            .iter()
            .map(|function| function.name.clone())
            .collect();
        let expected: Vec<_> = inputs
            .iter()
            .map(|(function, _)| function.name.clone())
            .collect();
        assert_eq!(names, expected);
        let actual: Vec<_> = sink
            .lock()
            .unwrap()
            .sites
            .iter()
            .map(|site| site.function.clone())
            .collect();
        assert_eq!(
            actual, expected,
            "counter slots must follow input order, not worker completion order"
        );
        let serial_sink = Arc::new(Mutex::new(CounterMap::new()));
        let serial = profile_pipeline(Arc::clone(&serial_sink));
        for (parallel, (input, proofs)) in prepared.iter().zip(&inputs) {
            let serial_function = serial
                .prepare_function_with_proofs(input, Some(proofs))
                .unwrap();
            let (parallel_bytes, _) = encode_function_with_fixups(parallel).unwrap();
            let (serial_bytes, _) = encode_function_with_fixups(&serial_function).unwrap();
            assert_eq!(parallel_bytes, serial_bytes, "{}", input.name);
        }
        assert_eq!(*sink.lock().unwrap(), *serial_sink.lock().unwrap());
    });
    eprintln!("{PASSED}");
}

#[test]
fn aot_counter_public_profile_batch_still_rejects_invalid_execution_budget() {
    crate::env_lock::with_env_edits(|env| {
        env.set(crate::resource_limits::TRUST_CG_MAX_PARALLELISM_ENV, "0");
        let sink = Arc::new(Mutex::new(CounterMap::new()));
        let result = profile_pipeline(Arc::clone(&sink)).prepare_functions_parallel(&[(
            lir_function(),
            trust_cg_lower::ProofContext::default(),
        )]);
        assert_eq!(result.len(), 1);
        assert!(matches!(&result[0], Err(PipelineError::ResourceBudget(_))));
        assert!(sink.lock().unwrap().is_empty());
    });
}
