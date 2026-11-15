// Copyright 2026 Andrew Yates | Apache-2.0
//! Finite observation/native controls, never independent proof or ABI credit.
use super::super::scalar_memory::tests::{evaluate, expand};
use super::*;
use crate::smt::{EvalEnv, SmtSort};
use trust_cg_lower::instructions::{IntCC, Value as LirValue};
use trust_ir::{CallingConv, ICmpOp, Inst, Ty};
use trust_ir_build::{ModuleBuilder, validate_module};

pub(crate) fn ordinary(memory: bool) -> Module {
    let host = trust_cg_codegen::CoreHostJitTarget::detect().unwrap();
    let mut m = ModuleBuilder::new_with_target_info(
        "ordinary_scalar_returns",
        host.trust_ir_target_info().clone(),
    );
    let codecs = vec![Ty::Ptr, Ty::U64, Ty::I64, Ty::U64, Ty::U64];
    let sig = m.add_func_type(vec![Ty::Ptr, Ty::U64], codecs.clone());
    let mut f = m.function("five_scalar_branch", sig);
    f.set_calling_conv(CallingConv::Fast);
    let entry = f.create_block();
    let pointer = f.add_block_param(entry, Ty::Ptr);
    let seed = f.add_block_param(entry, Ty::U64);
    let yes = f.create_block();
    let no = f.create_block();
    let join = f.create_block();
    let returned = codecs
        .iter()
        .cloned()
        .map(|ty| f.add_block_param(join, ty))
        .collect::<Vec<_>>();
    f.switch_to_block(entry);
    let old = if memory {
        let value = f.load(Ty::U64, pointer);
        f.store(Ty::U64, pointer, seed);
        Some(value)
    } else {
        None
    };
    let zero = f.iconst(Ty::U64, 0);
    let is_zero = f.icmp(ICmpOp::Eq, Ty::U64, seed, zero);
    f.condbr(is_zero, yes, vec![], no, vec![]);
    f.switch_to_block(yes);
    let seven = f.iconst(Ty::U64, 7);
    let negative = f.iconst(Ty::I64, -23);
    let site = f.iconst(Ty::U64, 0);
    let aux = f.iconst(Ty::U64, 17);
    f.br(
        join,
        vec![pointer, old.unwrap_or(seven), negative, site, aux],
    );
    f.switch_to_block(no);
    let negative = f.iconst(Ty::I64, -9);
    let site = f.iconst(Ty::U64, 7);
    let aux = f.iconst(Ty::U64, 17);
    f.br(
        join,
        vec![pointer, seed, negative, site, old.unwrap_or(aux)],
    );
    f.switch_to_block(join);
    f.ret(returned);
    let callee = f.build();
    let wrapper_sig = m.add_func_type(vec![Ty::Ptr, Ty::U64, Ty::Ptr], vec![]);
    let mut f = m.function("store_scalar_results", wrapper_sig);
    let entry = f.create_block();
    let pointer = f.add_block_param(entry, Ty::Ptr);
    let seed = f.add_block_param(entry, Ty::U64);
    let out = f.add_block_param(entry, Ty::Ptr);
    f.switch_to_block(entry);
    let values = f.call_results::<5>(callee, vec![pointer, seed]);
    for (lane, (value, ty)) in values.into_iter().zip(codecs).enumerate() {
        let address = f.gep_byte_offset(out, (lane * 8) as u64);
        f.store(ty, address, value);
    }
    f.ret(vec![]);
    f.build();
    let m = m.build().unwrap();
    assert_eq!(validate_module(&m), []);
    m
}
pub(crate) fn lowering(module: &Module) -> Function {
    trust_cg_lower::translate_function_with_license(
        &module.functions[0],
        module,
        &crate::license_test_support::permit_unlicensed(),
    )
    .unwrap()
    .0
}
fn all<'a>(q: &'a ScalarReturnSourceQueries<'_>) -> Vec<&'a ProofObligation> {
    q.return_obligations()
        .iter()
        .chain(std::iter::once(q.memory_obligation()))
        .chain(q.read_obligations())
        .chain(q.write_obligations())
        .collect()
}
fn environment(seed: u64) -> EvalEnv {
    let mut e = EvalEnv::default();
    e.insert("abi_x0".into(), 0x1000);
    e.insert("abi_x1".into(), seed);
    e.insert("observe".into(), 0x1000);
    e
}
fn memory() -> E {
    encode_store_le(
        &E::const_array(SmtSort::BitVec(64), E::bv_const(0xa5, 8)),
        &E::bv_const(0x1000, 64),
        &E::bv_const(29, 64),
        8,
    )
}
fn relation_holds(q: &ScalarReturnSourceQueries<'_>, seed: u64) -> bool {
    let substitutions = expand(q.definitions(), &memory());
    let e = environment(seed);
    all(q).iter().all(|ob| {
        assert!(
            ob.preconditions
                .iter()
                .all(|p| evaluate(p, &substitutions, &e).as_bool())
        );
        evaluate(&ob.trust_ir_expr, &substitutions, &e)
            == evaluate(&ob.aarch64_expr, &substitutions, &e)
    })
}

#[test]
fn scalar_returns_keep_all_original_codecs_paths_edge_copies_memory_and_demands() {
    for memory in [false, true] {
        let m = ordinary(memory);
        let l = lowering(&m);
        let before = l.canonical_verifier_identity_bytes().unwrap();
        let checked = scalar_edge_projection::check_scalar_block_arguments(&m, 0, &l).unwrap();
        assert_eq!(
            checked
                .transports()
                .iter()
                .filter(|e| !e.source_arguments.is_empty())
                .count(),
            2
        );
        let q = bind_scalar_return_source(&m, 0, &l).unwrap();
        assert_eq!(
            q.return_codecs(),
            [
                ScalarReturnCodec::Pointer,
                ScalarReturnCodec::Unsigned64,
                ScalarReturnCodec::Signed64,
                ScalarReturnCodec::Unsigned64,
                ScalarReturnCodec::Unsigned64
            ]
        );
        assert_eq!(q.return_obligations().len(), 5);
        assert_eq!(q.source_reads().len(), usize::from(memory));
        assert_eq!(q.source_writes().len(), usize::from(memory));
        for ob in all(&q) {
            assert_eq!(
                ob.preconditions.len(),
                q.geometry().len() + q.definitions().len()
            );
        }
        for seed in [0, 1, 7, u64::MAX] {
            assert!(relation_holds(&q, seed));
        }
        assert_eq!(before, l.canonical_verifier_identity_bytes().unwrap());
        // The old word/status/void contracts are not widened by this profile.
        assert!(bind_read_only_source(&m, 0, &l).is_err());
        assert!(scalar_memory::bind_scalar_memory_source(&m, 0, &l).is_err());
    }
}
#[test]
fn scalar_returns_wrong_lane_order_branch_width_arity_source_and_definitions_refuse_or_disagree() {
    let m = ordinary(false);
    let original = lowering(&m);
    for mutation in 0..9 {
        let mut l = original.clone();
        let ret = l
            .blocks
            .iter()
            .find(|(_, b)| matches!(b.instructions.last().unwrap().opcode, Opcode::Return))
            .unwrap()
            .0
            .to_owned();
        match mutation {
            0 => {
                l.blocks
                    .get_mut(&ret)
                    .unwrap()
                    .instructions
                    .last_mut()
                    .unwrap()
                    .args
                    .swap(0, 1);
            }
            1 => {
                l.blocks
                    .get_mut(&ret)
                    .unwrap()
                    .instructions
                    .last_mut()
                    .unwrap()
                    .args[4] = l.blocks[&ret].instructions.last().unwrap().args[1];
            }
            2 => {
                l.signature.returns[0] = trust_cg_lower::Type::I32;
            }
            3 => {
                l.blocks
                    .get_mut(&ret)
                    .unwrap()
                    .instructions
                    .last_mut()
                    .unwrap()
                    .args
                    .pop();
            }
            4 => {
                l.blocks
                    .get_mut(&ret)
                    .unwrap()
                    .instructions
                    .last_mut()
                    .unwrap()
                    .args[2] = LirValue(9999);
            }
            5 => {
                l.name = "foreign_scalar_body".into();
            }
            6 => {
                for b in l.blocks.values_mut() {
                    for n in &mut b.instructions {
                        if let Opcode::Icmp { cond } = &mut n.opcode {
                            *cond = IntCC::NotEqual;
                        }
                    }
                }
            }
            7 => {
                for b in l.blocks.values_mut() {
                    for n in &mut b.instructions {
                        if let Opcode::Brif {
                            then_dest,
                            else_dest,
                            ..
                        } = &mut n.opcode
                        {
                            std::mem::swap(then_dest, else_dest);
                        }
                    }
                }
            }
            8 => {
                l.blocks
                    .get_mut(&ret)
                    .unwrap()
                    .instructions
                    .last_mut()
                    .unwrap()
                    .args
                    .clear();
            }
            _ => unreachable!(),
        }
        match bind_scalar_return_source(&m, 0, &l) {
            Err(_) => {}
            Ok(q) => assert!(
                !relation_holds(&q, 0) || !relation_holds(&q, 1),
                "mutation {mutation}"
            ),
        }
    }
    let mut changed = m.clone();
    let sig = changed.functions[0].ty.index() as usize;
    changed.func_types[sig].returns.swap(1, 2);
    assert!(bind_scalar_return_source(&changed, 0, &original).is_err());
    let mut huge = m.clone();
    huge.name = "x".repeat(4 * 1024 * 1024 + 1);
    assert!(matches!(
        bind_scalar_return_source(&huge, 0, &original),
        Err(ReadOnlySourceError::Budget(_))
    ));
}
#[test]
fn scalar_returns_narrow_boolean_lanes_have_exact_original_widths() {
    let host = trust_cg_codegen::CoreHostJitTarget::detect().unwrap();
    let mut m = ModuleBuilder::new_with_target_info(
        "narrow_scalar_returns",
        host.trust_ir_target_info().clone(),
    );
    let sig = m.add_func_type(vec![Ty::U64], vec![Ty::U32, Ty::Bool, Ty::I64]);
    let mut f = m.function("narrow", sig);
    f.set_calling_conv(CallingConv::Fast);
    let b = f.create_block();
    f.add_block_param(b, Ty::U64);
    f.switch_to_block(b);
    let x = f.iconst(Ty::U32, u32::MAX as i128);
    let y = f.bool_const(true);
    let z = f.iconst(Ty::I64, -17);
    f.ret(vec![x, y, z]);
    f.build();
    let m = m.build().unwrap();
    let l = lowering(&m);
    let q = bind_scalar_return_source(&m, 0, &l).unwrap();
    assert_eq!(
        q.return_codecs(),
        [
            ScalarReturnCodec::Unsigned32,
            ScalarReturnCodec::Boolean,
            ScalarReturnCodec::Signed64
        ]
    );
    assert_eq!(
        q.return_obligations()
            .iter()
            .map(|o| o.trust_ir_expr.try_bv_width().unwrap())
            .collect::<Vec<_>>(),
        [32, 1, 64]
    );
    assert!(relation_holds(&q, 0));
}
#[test]
fn scalar_returns_original_e1_advances_to_actual_call_aggregate_abi_owner() {
    let m = trust_cg_codegen::pipeline::decode_tmbc(include_bytes!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../reports/2026-11-12-original-e1-machine/fixture/core.tmbc"
    )))
    .unwrap();
    let (functions, validation) =
        trust_cg_lower::translate_module_strict_for_arch_with_tls_and_validation_with_license(
            &m,
            trust_cg_lower::GuardCarrierArch::AArch64,
            trust_cg_lower::TlsDialect::MachOTlv,
            &crate::license_test_support::permit_unlicensed(),
        )
        .unwrap();
    validation
        .replay_strict_call_bindings_exhaustive(&functions)
        .unwrap();
    assert_eq!(functions.len(), 6);
    for name in ["tla_def_0", "tla_def_1"] {
        let ordinal = m.functions.iter().position(|f| f.name == name).unwrap();
        let l = &functions.iter().find(|(l, _)| l.name == name).unwrap().0;
        assert!(scalar_edge_projection::check_scalar_block_arguments(&m, ordinal, l).is_ok());
        let error = bind_scalar_return_source(&m, ordinal, l).err().unwrap();
        assert_eq!(
            error,
            ReadOnlySourceError::Source(
                "scalar-return calls require a checked callee/aggregate ABI owner"
            )
        );
        let first = &m.functions[ordinal]
            .blocks
            .iter()
            .find(|b| b.id == m.functions[ordinal].entry)
            .unwrap()
            .body[0];
        let Inst::Call { callee, .. } = first.inst else {
            panic!("original first instruction must remain a call")
        };
        let declaration = m.functions.iter().find(|f| f.id == callee).unwrap();
        let lerror =
            super::super::lir::graph_bound(&m, ordinal, l, Profile::ScalarReturns(Endpoint::Lir))
                .err()
                .unwrap();
        assert_eq!(
            lerror,
            ReadOnlySourceError::Lowering(
                "scalar-return calls require a checked callee/aggregate ABI owner"
            )
        );
        println!(
            "SCALAR_RETURN_ORIGINAL_E1 {name} returns={:?} first_callee={} original_signature={:?} refusal={error} lir_refusal={lerror} body_proof=false native_credit=false",
            l.signature.returns,
            declaration.name,
            m.func_types[declaration.ty.index() as usize]
        );
    }
}

#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
#[test]
fn scalar_returns_unchecked_arm64_macos_fast_c_caller_stores_all_lanes_o0_o2() {
    use trust_cg_codegen::pipeline::OptLevel;
    use trust_cg_codegen::{Compiler, CompilerConfig, CoreHostJitTarget};
    type Wrapper = unsafe extern "C" fn(*mut u64, u64, *mut u64);
    let host = CoreHostJitTarget::detect().unwrap();
    let mut calls = 0;
    for memory in [false, true] {
        let m = ordinary(memory);
        let before = serde_json::to_value(&m).unwrap();
        let l = lowering(&m);
        assert!(bind_scalar_return_source(&m, 0, &l).is_ok());
        for opt in [OptLevel::O0, OptLevel::O2] {
            let compiler = Compiler::new_for_target_spec(
                CompilerConfig {
                    opt_level: opt,
                    emit_proofs: false,
                    // Exercise the real Fast edge at O2 instead of accepting
                    // an inlined wrapper as a return-convention control.
                    never_inline: std::collections::BTreeSet::from(["five_scalar_branch".into()]),
                    ..CompilerConfig::for_host_jit_unchecked()
                },
                host.target_spec(),
            )
            .with_codegen_license(crate::license_test_support::permit_unlicensed());
            assert!(compiler.config().jit_validation_mode().is_unchecked());
            let compiled = compiler.compile_module_to_jit(&m, &HashMap::new()).unwrap();
            assert_eq!(compiled.metrics.function_count, 2);
            let caller = *compiled
                .buffer
                .symbol_offsets()
                .get("store_scalar_results")
                .unwrap() as usize;
            let callee = *compiled
                .buffer
                .symbol_offsets()
                .get("five_scalar_branch")
                .unwrap() as i64;
            let end = compiled
                .buffer
                .symbols()
                .filter_map(|(_, offset)| {
                    let offset = offset as usize;
                    (offset > caller).then_some(offset)
                })
                .min()
                .unwrap_or(compiled.buffer.code_len());
            let reaches_original_fast_function = compiled.buffer.code_slice()[caller..end]
                .as_chunks::<4>()
                .0
                .iter()
                .enumerate()
                .any(|(i, bytes)| {
                    let word = u32::from_le_bytes(*bytes);
                    if word & 0xfc00_0000 != 0x9400_0000 {
                        return false;
                    }
                    let delta = (((word & 0x03ff_ffff) as i32) << 6) >> 4;
                    caller as i64 + (i * 4) as i64 + i64::from(delta) == callee
                });
            assert!(
                reaches_original_fast_function,
                "the ordinary Fast call must execute at {opt:?}"
            );
            // SAFETY: only the retained void C wrapper crosses Rust's ABI.
            // Both live arrays outlive the call; Fast results stay internal.
            let wrapper = unsafe {
                compiled
                    .buffer
                    .get_fn_bound::<Wrapper>("store_scalar_results")
                    .unwrap()
            };
            for seed in [0, 1, 7, u64::MAX, 1 << 63, 0xfedc_ba98_7654_3210] {
                let mut state = 29u64;
                let pointer = (&mut state as *mut u64) as u64;
                let mut out = [0xaaaa_aaaa_aaaa_aaaa; 7];
                unsafe {
                    wrapper.as_ref()(&mut state, seed, out[1..].as_mut_ptr());
                }
                let expected = if seed == 0 {
                    [pointer, if memory { 29 } else { 7 }, (-23i64) as u64, 0, 17]
                } else {
                    [
                        pointer,
                        seed,
                        (-9i64) as u64,
                        7,
                        if memory { 29 } else { 17 },
                    ]
                };
                assert_eq!(&out[1..6], expected);
                assert_eq!(out[0], 0xaaaa_aaaa_aaaa_aaaa);
                assert_eq!(out[6], 0xaaaa_aaaa_aaaa_aaaa);
                assert_eq!(state, if memory { seed } else { 29 });
                calls += 1;
            }
            assert_eq!(serde_json::to_value(&m).unwrap(), before);
        }
    }
    assert_eq!(calls, 24);
    println!(
        "SCALAR_RETURN_NATIVE compiled=4 wrappers=24 lanes=120 opt=O0,O2 validation=Unchecked emit_proofs=false body_proof=false native_credit=false"
    );
}

#[test]
fn scalar_returns_keep_return_resource_and_cold_branch_guards() {
    let m = ordinary(false);
    let l = lowering(&m);
    let mut oversized = m.clone();
    let sig = oversized.functions[0].ty.index() as usize;
    oversized.func_types[sig].returns = vec![Ty::I64; 9];
    assert!(bind_scalar_return_source(&oversized, 0, &l).is_err());
    let mut changed = m.clone();
    let branch = changed.functions[0]
        .blocks
        .iter_mut()
        .find(|b| matches!(b.body.last().unwrap().inst, Inst::Br { .. }))
        .unwrap();
    branch.body.last_mut().unwrap().inst = Inst::Return { values: vec![] };
    assert!(bind_scalar_return_source(&changed, 0, &l).is_err());
    let mut target = l.clone();
    target.signature.returns = vec![trust_cg_lower::Type::I64; 9];
    assert!(bind_scalar_return_source(&m, 0, &target).is_err());
    assert!(matches!(
        bind_scalar_return_source(&m, 999, &l),
        Err(ReadOnlySourceError::Source(_))
    ));
}

#[test]
fn scalar_returns_retain_exact_pure_raw_queries_and_sat_controls() {
    use sha2::{Digest, Sha256};
    let m = ordinary(false);
    let l = lowering(&m);
    let q = bind_scalar_return_source(&m, 0, &l).unwrap();
    let mut cases: Vec<(String, ProofObligation)> = q
        .return_obligations()
        .iter()
        .enumerate()
        .map(|(i, o)| (format!("lane-{i}"), o.clone()))
        .collect();
    cases.push(("final-memory".into(), q.memory_obligation().clone()));
    let mut premises = q.return_obligations()[0].clone();
    premises.trust_ir_expr = E::BoolConst(true);
    premises.aarch64_expr = E::BoolConst(false);
    cases.push(("premises-sat".into(), premises));
    let mut wrong = l.clone();
    let ret = wrong
        .blocks
        .values_mut()
        .find(|b| matches!(b.instructions.last().unwrap().opcode, Opcode::Return))
        .unwrap();
    ret.instructions.last_mut().unwrap().args.swap(0, 1);
    let wrong = bind_scalar_return_source(&m, 0, &wrong).unwrap();
    cases.push((
        "wrong-lane-sat".into(),
        wrong.return_obligations()[0].clone(),
    ));
    for (name, obligation) in cases {
        let config = crate::ay_bridge::AYConfig {
            solver: None,
            timeout_ms: crate::ay_bridge::DEFAULT_AY_TIMEOUT_MS,
            produce_models: true,
        };
        let query = crate::ay_bridge::generate_smt2_query_raw(&obligation, &config);
        println!(
            "SCALAR_RETURN_QUERY={}",
            serde_json::json!({"case":name,"bytes":query.len(),"sha256":format!("{:x}",Sha256::digest(query.as_bytes())),"query":query,"source_bound":false,"native_credit":false})
        );
    }
}

#[test]
fn scalar_returns_memory_transition_changes_do_not_hide_behind_equal_lanes() {
    let m = ordinary(true);
    let original = lowering(&m);
    for mutation in 0..3 {
        let mut l = original.clone();
        let entry = l.entry_block;
        let index = l.blocks[&entry]
            .instructions
            .iter()
            .position(|n| matches!(n.opcode, Opcode::Store { .. }))
            .unwrap();
        match mutation {
            0 => {
                l.blocks.get_mut(&entry).unwrap().instructions[index].args[0] = LirValue(0);
            }
            1 => {
                l.blocks.get_mut(&entry).unwrap().instructions.remove(index);
                l.trust_ir_origins.get_mut(&entry).unwrap().remove(index);
            }
            2 => {
                l.blocks.get_mut(&entry).unwrap().instructions[index].args[1] = LirValue(1);
            }
            _ => unreachable!(),
        }
        let q = bind_scalar_return_source(&m, 0, &l).unwrap();
        let substitutions = expand(q.definitions(), &memory());
        let e = environment(1);
        assert!(
            q.return_obligations()
                .iter()
                .all(|o| evaluate(&o.trust_ir_expr, &substitutions, &e)
                    == evaluate(&o.aarch64_expr, &substitutions, &e)),
            "lanes remain equal for mutation {mutation}"
        );
        assert!(!relation_holds(&q, 1), "memory/access mutation {mutation}");
    }
}
