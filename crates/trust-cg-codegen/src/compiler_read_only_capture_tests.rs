// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Diagnostic capture of the authentic TY read-only predicate's actual
//! compatibility preparation and policy-qualified encoder endpoints.
//! Frame layout, MachIR and bytes are observed, not reconstructed or granted
//! frame ownership, Checked/native credit, memory permission or replay proof.

#![cfg(all(target_arch = "aarch64", target_os = "macos"))]

use crate::CoreHostJitTarget;
use crate::pipeline::{OptLevel, Pipeline, PipelineConfig, encode_function_with_fixups_and_sites};
use serde_json::json;
use std::collections::BTreeMap;
use std::convert::Infallible;
use trust_cg_verify::aarch64_control_decode::{A64ControlWord, decode_a64_control_word};
use trust_cg_verify::aarch64_value_decode_proofs::{A64ValueWord, decode_a64_value_word};
use trust_cg_verify::memory_proofs::{encode_store_le, memory_sort, zeroed_memory};
use trust_cg_verify::read_only_target::{
    ReadOnlyTargetQueries, bind_read_only_bytes, bind_read_only_machine,
};
use trust_cg_verify::smt::{EvalEnv, SmtExpr as E};
use trust_cg_verify::source_bound_frame::{bind_read_only_source, source_admits_frame_owner};
use trust_ir::{CallingConv, Linkage, Module, Ty};

fn evaluate(expression: &E, memory: &E, env: &EvalEnv) -> trust_cg_verify::smt::EvalResult {
    let bound = expression
        .try_rewrite_dag::<Infallible>(&mut |node| {
            Ok(matches!(node, E::UF { name, args, ret_sort }
                if name == "entry_memory" && args.is_empty() && *ret_sort == memory_sort())
            .then(|| memory.clone()))
        })
        .unwrap()
        .unwrap_or_else(|| expression.clone());
    bound
        .try_eval(env)
        .expect("finite nonuniform concrete array")
}

fn integer(value: i64) -> u64 {
    (value as u64).wrapping_shl(3) | 1
}

fn samples() -> Vec<(u64, u64, u64)> {
    let yes = 1 << 32;
    let error = (3 << 32) | 1;
    let fallback = (3 << 32) | 4;
    let mut cases = vec![
        (integer(i64::from(i32::MIN)), 9, yes),
        (integer(i64::from(i32::MIN) + 1), 9, yes),
        (integer(-1), 9, yes),
        (integer(0), 9, yes),
        (integer(1), 9, 0),
        (integer(2), 9, 0),
        (integer(i64::from(i32::MAX) - 1), 9, 0),
        (integer(i64::from(i32::MAX)), 9, 0),
        (integer(0), integer(-1), 0),
        (integer(0), integer(0), 0),
        (integer(0), integer(i64::from(i32::MAX)), yes),
        (
            integer(i64::from(i32::MIN)),
            integer(i64::from(i32::MIN)),
            0,
        ),
        (
            integer(i64::from(i32::MAX)),
            integer(i64::from(i32::MAX)),
            0,
        ),
    ];
    for value in [
        i64::from(i32::MIN) - 1,
        i64::from(i32::MAX) + 1,
        -(1i64 << 60),
        (1i64 << 60) - 1,
    ] {
        cases.push((integer(value), 9, error));
        cases.push((integer(0), integer(value), error));
    }
    for tag in [0, 2, 3, 4, 5, 6, 7] {
        let expected = if tag == 4 { fallback } else { error };
        cases.push((tag, 9, expected));
        cases.push((1, tag, expected));
    }
    cases.extend([
        (4, 2, fallback),
        (2, 4, fallback),
        (4, integer(i64::from(i32::MAX) + 1), fallback),
        (integer(i64::from(i32::MIN) - 1), 4, fallback),
        (u64::MAX - 3, 2, fallback),
        (u64::MAX, 9, error),
    ]);
    cases
}

fn case(state: u64, literal: u64, alias: bool) -> (E, EvalEnv) {
    let ctx = 0x1000;
    let parent = if alias { ctx } else { 0x2000 };
    let pool = 0x3000;
    let mut memory = zeroed_memory();
    for (address, value) in [
        (ctx + 8, pool),
        (parent, state),
        (pool + 24, literal),
        (parent + 8, 0xdead_beef),
    ] {
        memory = encode_store_le(
            &memory,
            &E::bv_const(address, 64),
            &E::bv_const(value, 64),
            8,
        );
    }
    // Avoid overwriting the live pool pointer when parent aliases context.
    if alias {
        memory = encode_store_le(
            &memory,
            &E::bv_const(ctx + 8, 64),
            &E::bv_const(pool, 64),
            8,
        );
    }
    let mut env = EvalEnv::default();
    for (i, word) in [
        ctx,
        parent,
        if alias { parent } else { 0x4000 },
        if alias { parent } else { 0x5000 },
    ]
    .into_iter()
    .enumerate()
    {
        env.insert(format!("abi_x{i}"), word);
    }
    for i in 4..31 {
        env.insert(format!("entry_x{i}"), 0xbad0_0000 + i);
    }
    for (i, flag) in ["entry_n", "entry_z", "entry_c", "entry_v"]
        .into_iter()
        .enumerate()
    {
        env.insert(flag.into(), ((state ^ literal) >> i) & 1);
    }
    (memory, env)
}

fn holds(queries: &ReadOnlyTargetQueries<'_>, memory: &E, env: &EvalEnv, loads: bool) -> bool {
    let obligations = if loads {
        queries.load_obligations()
    } else {
        queries.return_obligations()
    };
    obligations.iter().all(|q| {
        assert!(
            q.preconditions
                .iter()
                .all(|p| evaluate(p, memory, env).as_bool()),
            "SOURCE premises must hold; no target premise hides a fault"
        );
        evaluate(&q.aarch64_expr, memory, env).as_bool()
    })
}

fn encoded(words: &[u32]) -> Vec<u8> {
    words.iter().flat_map(|w| w.to_le_bytes()).collect()
}

fn refute_byte_mutants(
    source: &trust_cg_verify::source_bound_frame::ReadOnlySourceQueries<'_>,
    words: &[u32],
) {
    let load = words
        .iter()
        .position(|word| word & 0xffc0_0000 == 0xf940_0000)
        .unwrap();
    let branch = words
        .iter()
        .position(|word| word & 0xff00_0010 == 0x5400_0000)
        .unwrap();
    let mut wrong_base = words.to_vec();
    wrong_base[load] = (wrong_base[load] & !(31 << 5)) | (3 << 5);
    let mut wrong_offset = words.to_vec();
    wrong_offset[load] ^= 1 << 10;
    let mut wrong_guard = words.to_vec();
    wrong_guard[branch] ^= 1;
    let mut extra = vec![0xf940_0471]; // LDR X17,[X3,#8], never used by original body.
    extra.extend_from_slice(words);
    let mut wrong_status = words.to_vec();
    let status = words
        .iter()
        // Optimized code builds the terminal true status in a temporary and
        // copies it into X0. Earlier identical literals are range-check bounds;
        // choose the final occurrence, retaining its actual allocated register.
        .rposition(|word| {
            matches!(
                decode_a64_value_word(*word),
                Ok(A64ValueWord::MoveWide {
                    sf: 1,
                    opc: 3,
                    hw: 2,
                    imm16: 1,
                    ..
                })
            )
        })
        .expect("actual terminal MOVK Xd,#1,LSL#32 true-status high word");
    let Ok(A64ValueWord::MoveWide { rd, .. }) = decode_a64_value_word(words[status]) else {
        unreachable!("selected decoded MOVK")
    };
    assert_eq!(
        decode_a64_value_word(words[status - 1]).unwrap(),
        A64ValueWord::MoveWide {
            sf: 1,
            opc: 2,
            hw: 0,
            imm16: 0,
            rd,
        },
        "true-status high word follows zero initialization, not a range bound"
    );
    let return_index = if rd == 0 {
        status + 1
    } else {
        assert_eq!(
            decode_a64_value_word(words[status + 1]).unwrap(),
            A64ValueWord::LogicalShiftedReg {
                sf: 1,
                opc: 1,
                shift: 0,
                n: 0,
                rm: rd,
                imm6: 0,
                rn: 31,
                rd: 0,
            },
            "allocated true status is copied intact into X0"
        );
        status + 2
    };
    assert_eq!(
        decode_a64_control_word(words[return_index]),
        Some(A64ControlWord::Return { register: 30 }),
        "mutated status reaches the actual return"
    );
    // Change only imm16: nonzero remains nonzero, but the full U64 is wrong.
    wrong_status[status] = (wrong_status[status] & !(0xffff << 5)) | (2 << 5);
    let mut wrong_select = words.to_vec();
    let select = words
        .iter()
        .position(|w| w & 0x3fe0_0800 == 0x1a80_0000)
        .expect("actual conditional-select instruction");
    wrong_select[select] ^= 1 << 12;
    for (name, mutant, must_refute_read, unchanged_return) in [
        ("wrong base", wrong_base, true, false),
        ("wrong offset", wrong_offset, true, false),
        ("inverted branch", wrong_guard, false, false),
        ("dead extra read", extra, true, true),
        ("wrong full status high word", wrong_status, false, false),
        ("inverted select polarity", wrong_select, false, false),
    ] {
        let code = encoded(&mutant);
        let queries = bind_read_only_bytes(source, &code).unwrap_or_else(|e| {
            panic!("supported semantic mutant {name} must construct, not skip: {e}")
        });
        let mut return_counterexample = false;
        let mut read_counterexample = false;
        for (state, literal, _) in samples() {
            let (memory, env) = case(state, literal, false);
            let returns = holds(&queries, &memory, &env, false);
            return_counterexample |= !returns;
            read_counterexample |= !holds(&queries, &memory, &env, true);
            if unchanged_return {
                assert!(returns, "extra unused read leaves return unchanged");
            }
        }
        assert!(
            if must_refute_read {
                read_counterexample
            } else {
                return_counterexample
            },
            "mandatory counterexample for {name}"
        );
    }
}

#[test]
fn actual_ty_read_only_predicate_captures_prepared_machine_frame_and_final_words() {
    let captured: serde_json::Value = serde_json::from_str(include_str!(
        "../../trust-cg-verify/tests/fixtures/ty_original_read_only_predicate.json"
    ))
    .unwrap();
    assert_eq!(
        captured["format"],
        "ty-original-read-only-predicate-source-v1"
    );
    assert_eq!(captured["selection"]["unit_key"], "inv:Second");
    assert_eq!(captured["original_core_instruction_count"], 59);
    let original: Module = serde_json::from_value(captured["module"].clone()).unwrap();
    assert!(original.target_info.is_none());
    assert_eq!(original.functions.len(), 1);
    let host = CoreHostJitTarget::detect().expect("exact supported executing host");
    let mut module = original.clone();
    // Disclosed metadata-only binding, exactly the ordinary TY native-JIT
    // construction boundary. It is not independent Core admission authority.
    module.target_info = Some(host.trust_ir_target_info().clone());
    let mut restored = module.clone();
    restored.target_info = None;
    assert_eq!(
        serde_json::to_value(restored).unwrap(),
        serde_json::to_value(&original).unwrap(),
        "only explicit target context changes"
    );
    let source = &module.functions[0];
    assert_eq!(source.id.index(), 60_004);
    assert_eq!(source.name, "tyw1_u3");
    assert_eq!(source.linkage, Linkage::Internal);
    assert_eq!(source.calling_conv, CallingConv::C);
    assert_eq!(source.blocks.len(), 12);
    let signature = &module.func_types[source.ty.index() as usize];
    assert_eq!(signature.params, [Ty::Ptr, Ty::Ptr, Ty::Ptr, Ty::Ptr]);
    assert_eq!(signature.returns, [Ty::U64]);
    assert!(!signature.is_vararg);
    let module_json = serde_json::to_value(&module).unwrap();
    let (lowering, proof_context) = trust_cg_lower::translate_function_with_license(
        source,
        &module,
        &crate::license_test_support::permit_unlicensed(),
    )
    .unwrap();
    let lowering_json = serde_json::to_value(&lowering).unwrap();
    let proof_context_debug = format!("{proof_context:#?}");
    assert!(
        !source_admits_frame_owner(&lowering),
        "the existing scalar affine frame owner must not acquire this source"
    );
    let queries = bind_read_only_source(&module, 0, &lowering).unwrap();
    assert!(std::ptr::eq(queries.module(), &module));
    assert!(std::ptr::eq(queries.source(), source));
    assert!(std::ptr::eq(queries.lir(), &lowering));
    assert_eq!(queries.read_requirements().len(), 3);
    assert_eq!(queries.lowering_reads().len(), 3);

    let mut profiles = 0;
    for level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
        let pipeline = Pipeline::new(PipelineConfig {
            opt_level: level,
            verify: false,
            ..PipelineConfig::for_target(host.target_spec().triple())
        });
        let (machine, metrics) = pipeline
            .prepare_function_with_metrics_and_trust_ir_module(
                &lowering,
                Some(&proof_context),
                &module,
                source,
            )
            .unwrap_or_else(|error| panic!("actual TY diagnostic preparation {level:?}: {error}"));
        assert_eq!(machine.name, source.name);
        assert!(metrics.pre_optimization_affine_lowering.is_none());
        let frame = metrics
            .frame_layout
            .as_ref()
            .expect("actual preparation retains its computed frame layout");
        let machine_debug = format!("{machine:#?}");
        let (bytes, fixups, sites) = encode_function_with_fixups_and_sites(&machine)
            .unwrap_or_else(|error| panic!("actual TY final encoder {level:?}: {error}"));
        assert!(!bytes.is_empty());
        let (chunks, tail) = bytes.as_chunks::<4>();
        assert!(tail.is_empty());
        let words: Vec<_> = chunks.iter().copied().map(u32::from_le_bytes).collect();
        assert!(
            fixups.is_empty(),
            "authentic captured final stream has no pending relocation holes"
        );
        let machine_queries = bind_read_only_machine(&queries, &machine).unwrap_or_else(|e| {
            panic!("actual TY MachIR at {level:?} must construct, not skip: {e}")
        });
        let byte_queries = bind_read_only_bytes(&queries, &bytes).unwrap_or_else(|e| {
            panic!("actual TY final words at {level:?} must construct, not skip: {e}")
        });
        assert_eq!(machine_queries.reads().len(), 3);
        assert_eq!(byte_queries.reads().len(), 3);
        assert!(!machine_queries.return_obligations().is_empty());
        assert!(!byte_queries.return_obligations().is_empty());
        let mut concrete = 0;
        for alias in [false, true] {
            for (state, literal, expected) in samples() {
                let (memory, env) = case(state, literal, alias);
                assert_eq!(
                    evaluate(&queries.return_obligation().trust_ir_expr, &memory, &env).as_u64(),
                    expected
                );
                assert_eq!(
                    evaluate(&queries.return_obligation().aarch64_expr, &memory, &env).as_u64(),
                    expected
                );
                for q in queries.load_obligations() {
                    assert!(evaluate(&q.aarch64_expr, &memory, &env).as_bool());
                }
                for endpoint in [&machine_queries, &byte_queries] {
                    assert!(std::ptr::eq(endpoint.source(), &queries));
                    assert!(
                        holds(endpoint, &memory, &env, false),
                        "{level:?}/{state:#x}/{literal:#x}/alias{alias} full return"
                    );
                    assert!(
                        holds(endpoint, &memory, &env, true),
                        "{level:?}/{state:#x}/{literal:#x}/alias{alias} read demand"
                    );
                    concrete += 1;
                }
            }
        }
        assert_eq!(concrete, 164);
        refute_byte_mutants(&queries, &words);
        let mut wrong_machine = machine.clone();
        let load = wrong_machine
            .block_order
            .iter()
            .flat_map(|b| wrong_machine.block(*b).insts.iter().copied())
            .find(|id| wrong_machine.inst(*id).opcode == trust_cg_ir::AArch64Opcode::LdrRI)
            .unwrap();
        let trust_cg_ir::MachOperand::Imm(offset) =
            &mut wrong_machine.insts[load.0 as usize].operands[2]
        else {
            panic!("actual LdrRI byte offset")
        };
        *offset += 8;
        let wrong_queries = bind_read_only_machine(&queries, &wrong_machine)
            .expect("supported actual-machine wrong-offset mutant must construct");
        let (memory, env) = case(1, 9, false);
        assert!(
            !holds(&wrong_queries, &memory, &env, true),
            "actual-machine wrong read has a mandatory demand counterexample"
        );
        println!(
            "TY_READ_ONLY_TARGET_QUERIES level={level:?} machine_guarded_returns={} word_guarded_returns={} machine_reads=3 word_reads=3 concrete_endpoints={concrete} required_semantic_byte_mutants=6 required_semantic_machine_mutants=1 independent_proof=false checked_credit=false native_execution=false replay=false",
            machine_queries.return_obligations().len(),
            byte_queries.return_obligations().len()
        );

        // Consume the ACTUAL originating-site sidecar, never infer sites from
        // an instruction count or a second hand-built instruction stream.
        assert_eq!(sites.len(), fixups.len());
        for (index, site) in sites.iter().enumerate() {
            let fixup = fixups.get(index).unwrap();
            assert_eq!(site.fixup_index, index);
            assert_eq!(site.offset, fixup.offset);
            assert!(machine.block(site.block).insts.contains(&site.inst));
            assert_eq!(machine.inst(site.inst).opcode, site.opcode);
            assert_eq!(site.offset % 4, 0);
            assert_eq!(words[site.offset as usize / 4], site.placeholder_word);
        }
        assert_eq!(format!("{machine:#?}"), machine_debug);
        assert_eq!(serde_json::to_value(&module).unwrap(), module_json);
        assert_eq!(serde_json::to_value(&lowering).unwrap(), lowering_json);
        assert_eq!(format!("{proof_context:#?}"), proof_context_debug);

        let mut opcodes = BTreeMap::<String, usize>::new();
        let mut linked = 0;
        for block in &machine.block_order {
            for id in &machine.block(*block).insts {
                *opcodes
                    .entry(format!("{:?}", machine.inst(*id).opcode))
                    .or_default() += 1;
                linked += 1;
            }
        }
        println!(
            "TY_READ_ONLY_MACHINE_INVENTORY level={level:?} machine_blocks={} arena_instructions={} linked_instructions={linked} stack_slots={} spill_slots={} frame_bytes={} encoded_words={} fixups={} originating_sites={} source_admits_frame_owner=false diagnostic_preparation=true checked_credit=false native_execution=false replay=false opcodes={}",
            machine.block_order.len(),
            machine.insts.len(),
            machine.stack_slots.len(),
            metrics.spill_slot_count,
            frame.total_frame_size,
            words.len(),
            fixups.len(),
            sites.len(),
            serde_json::to_string(&opcodes).unwrap(),
        );
        let payload = json!({
            "format": "ty-original-read-only-machine-capture-v1",
            "level": format!("{level:?}"),
            "stage": "compatibility diagnostic prepare_function_with_metrics_and_trust_ir_module, then actual policy-qualified encode_function_with_fixups_and_sites; no semantic/Checked/native/proof credit",
            "target_binding": "CoreHostJitTarget::detect metadata clone only; original targetless body, linkage, IDs, types, attributes and context otherwise unchanged",
            "original_ty_capture": captured,
            "target_bound_original_module": module,
            "original_lir": lowering,
            "original_proof_context_debug": proof_context_debug,
            "prepared_machine_debug": machine_debug,
            "frame_layout_debug": format!("{frame:#?}"),
            "preparation_metrics_debug": format!("{metrics:#?}"),
            "linked_opcode_inventory": opcodes,
            "encoded_bytes": bytes,
            "encoded_words_little_endian": words,
            "encoded_fixups_debug": format!("{fixups:#?}"),
            "encoded_originating_sites_debug": format!("{sites:#?}"),
            "source_admits_frame_owner": false,
            "boundary": "caller readable initialized live extents, machine/private-frame separation, source-to-final-machine/byte correspondence and independent replay remain unresolved; capture is not a substitute",
        });
        println!(
            "BEGIN_TY_READ_ONLY_MACHINE_CAPTURE_JSON {level:?}\n{}\nEND_TY_READ_ONLY_MACHINE_CAPTURE_JSON {level:?}",
            serde_json::to_string_pretty(&payload).unwrap()
        );
        profiles += 1;
    }
    assert_eq!(profiles, 4);
}
