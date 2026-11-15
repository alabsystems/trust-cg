// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
//! Required native arithmetic under proof-required JIT, with exact source types.
//!
//! Runs on the host's own AArch64 triple (aarch64-apple-darwin or
//! aarch64-unknown-linux-gnu), through the host JIT's publication (MAP_JIT
//! with per-thread write protection on Apple silicon). Publication needs the
//! frame, ALU and constant theorems discharged by the identity-admitted AY and replayed
//! by an independent Clean checker; without such a pair these tests fail and
//! name the tools they resolved (tests/common/source_bound_proof_tools.rs).
//! Live copies use a raw body theorem; unused scalar argument copies are
//! removed before allocation. Every one of the fixed 160 rows must publish.
#![cfg(all(target_arch = "aarch64", feature = "verify"))]

use sha2::{Digest, Sha256};
use std::collections::HashMap;
use trust_cg_codegen::compiler::{Compiler, CompilerConfig, JitValidationMode};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::Target;
use trust_ir::Ty;
use trust_ir_build::ModuleBuilder;

#[path = "common/source_bound_proof_tools.rs"]
mod source_bound_proof_tools;
use source_bound_proof_tools::{proof_tool_context, require_proof_tools};

const SHAPES: [&str; 10] = [
    "add",
    "sub",
    "add_small",
    "add_shifted",
    "sub_small",
    "sub_shifted",
    "add_negative",
    "sub_negative",
    "chain",
    "double",
];

fn module(ty: Ty, shape: &str) -> trust_ir::Module {
    let mut builder = ModuleBuilder::new("source_bound_arithmetic");
    let signature = builder.add_func_type(vec![ty.clone(); 2], vec![ty.clone()]);
    let mut f = builder.function("calculate", signature);
    let entry = f.create_block();
    let a = f.add_block_param(entry, ty.clone());
    let b = f.add_block_param(entry, ty.clone());
    f.switch_to_block(entry);
    let constant = |value: i128| match ty {
        Ty::U32 => value as u32 as i128,
        Ty::U64 => value as u64 as i128,
        _ => value,
    };
    let result = match shape {
        "add" => f.add(ty.clone(), a, b),
        "sub" => f.sub(ty.clone(), a, b),
        "double" => f.add(ty.clone(), a, a),
        "chain" => {
            let c = f.iconst(ty.clone(), 4096);
            let d = f.iconst(ty.clone(), constant(-3));
            let v = f.add(ty.clone(), a, c);
            let v = f.sub(ty.clone(), v, b);
            f.add(ty.clone(), v, d)
        }
        _ => {
            let value = if shape.ends_with("small") {
                4095
            } else if shape.ends_with("shifted") {
                4096
            } else {
                -1
            };
            let c = f.iconst(ty.clone(), constant(value));
            if shape.starts_with("add") {
                f.add(ty.clone(), a, c)
            } else {
                f.sub(ty.clone(), a, c)
            }
        }
    };
    f.ret(vec![result]);
    f.build();
    builder.build().expect("ModuleBuilder::build: test fixture")
}

fn expected(shape: &str, a: u64, b: u64) -> u64 {
    match shape {
        "add" => a.wrapping_add(b),
        "sub" => a.wrapping_sub(b),
        "double" => a.wrapping_add(a),
        "add_small" => a.wrapping_add(4095),
        "sub_small" => a.wrapping_sub(4095),
        "add_shifted" => a.wrapping_add(4096),
        "sub_shifted" => a.wrapping_sub(4096),
        "add_negative" => a.wrapping_sub(1),
        "sub_negative" => a.wrapping_add(1),
        "chain" => a.wrapping_add(4096).wrapping_sub(b).wrapping_sub(3),
        _ => unreachable!("closed source corpus"),
    }
}

// The return-value checker intentionally cannot distinguish dead constants.
// Encoding custody uses the production independent decoder against actual
// allocated MachIR, so it must reject their changed imm16 fields as well.
fn decode_items(
    lir: &trust_cg_lower::Function,
    level: OptLevel,
    bytes: &[u8],
) -> Vec<trust_cg_codegen::decode_check::DecodeCheckItem<trust_cg_ir::MachInst>> {
    use trust_cg_codegen::pipeline::{Pipeline, PipelineConfig, encode_function};
    let machine = Pipeline::new(PipelineConfig {
        opt_level: level,
        verify: false,
        enable_jit_fast_regalloc: true,
        ..PipelineConfig::for_host_aarch64()
    })
    .with_proof_grade_aarch64_publication()
    .prepare_function(lir)
    .unwrap();
    assert_eq!(
        encode_function(&machine).unwrap(),
        bytes,
        "re-prepared allocated stream must match the published function"
    );
    machine
        .block_order
        .iter()
        .flat_map(|block| &machine.blocks[block.0 as usize].insts)
        .map(|id| &machine.insts[id.0 as usize])
        .filter(|inst| !inst.is_pseudo())
        .enumerate()
        .map(
            |(index, inst)| trust_cg_codegen::decode_check::DecodeCheckItem {
                start: index * 4,
                end: (index + 1) * 4,
                intent: inst.clone(),
                hole: None,
            },
        )
        .collect()
}

fn arithmetic_matrix() {
    require_proof_tools();
    let mut failures = Vec::new();
    let mut compiled = 0;
    let mut refused = 0;
    let mut calls = 0;
    let mut add_mutants = 0;
    let mut shift_mutants = 0;
    let mut constant_mutants = 0;
    let mut copy_mutants = 0;
    let mut constant_return_mutants = 0;
    let mut dead_constant_mutants = 0;
    let inputs = [
        0,
        1,
        2,
        4095,
        4096,
        u32::MAX as u64,
        1 << 31,
        1 << 32,
        i64::MAX as u64,
        1 << 63,
        u64::MAX - 1,
        u64::MAX,
    ];
    for ty in [Ty::I32, Ty::U32, Ty::I64, Ty::U64] {
        let mask = if matches!(ty, Ty::I32 | Ty::U32) {
            u32::MAX as u64
        } else {
            u64::MAX
        };
        for shape in SHAPES {
            let source = module(ty.clone(), shape);
            for level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
                let compiler = Compiler::new(CompilerConfig {
                    opt_level: level,
                    emit_proofs: true,
                    parallel: false,
                    ..CompilerConfig::jit_fast(Target::Aarch64)
                })
                .with_codegen_license(permit_unlicensed());
                let result = match compiler.compile_module_to_jit(&source, &HashMap::new()) {
                    Ok(result) => result,
                    Err(error) => {
                        refused += 1;
                        failures.push(format!("{ty:?}/{shape}/{level:?}: {error}"));
                        continue;
                    }
                };
                let validation = result.validation.as_ref().expect("required JIT validation");
                assert_eq!(validation.mode, JitValidationMode::AlwaysVerify);
                assert!(validation.every_function_semantics_verified());
                assert_eq!(validation.functions.len(), 1);
                assert_eq!(
                    validation.published_image_sha256,
                    format!("{:x}", Sha256::digest(result.buffer.code_slice()))
                );
                // The host's own publication: on Apple silicon a MAP_JIT
                // mapping written under per-thread write protection
                // (pthread_jit_write_protect_np) and sealed read-execute.
                let protection = result.buffer.executable_memory_protection();
                assert!(
                    protection.published_rx
                        && protection.mprotect_rx_ok
                        && protection.map_jit == cfg!(target_os = "macos")
                        && protection.write_protect_supported == cfg!(target_os = "macos"),
                    "{ty:?}/{shape}/{level:?}: {protection:?}"
                );
                assert!(
                    result
                        .buffer
                        .certificate("calculate")
                        .unwrap()
                        .is_verified()
                );
                let (lir, _) = trust_cg_lower::translate_function_with_license(
                    &source.functions[0],
                    &source,
                    &permit_unlicensed(),
                )
                .unwrap();
                trust_cg_verify::aarch64_affine_lowering::check_aarch64_trust_ir_affine_bytes(
                    &source,
                    0,
                    &lir,
                    result.buffer.code_slice(),
                )
                .unwrap_or_else(|error| panic!("{ty:?}/{shape}/{level:?}: final bytes: {error}"));
                let items = decode_items(&lir, level, result.buffer.code_slice());
                let decode = |bytes: &[u8]| {
                    trust_cg_codegen::decode_check::run_decode_check_with_allowlist_policy(
                        &trust_cg_codegen::aarch64::decode_check::A64DecodeCheck,
                        &items,
                        bytes,
                        trust_cg_codegen::decode_check::DecodeCheckMode::Enforce,
                        trust_cg_codegen::decode_check::AllowlistPolicy::Refuse,
                    )
                };
                assert!(decode(result.buffer.code_slice()).is_ok());
                for (index, word) in result
                    .buffer
                    .code_slice()
                    .as_chunks::<4>()
                    .0
                    .iter()
                    .enumerate()
                    .map(|(i, b)| (i, u32::from_le_bytes(*b)))
                    .filter(|(_, word)| word & 0x7fe0ffe0 == 0x2a0003e0)
                {
                    let mut wrong_route = result.buffer.code_slice().to_vec();
                    wrong_route[index * 4..index * 4 + 4]
                        .copy_from_slice(&(word ^ (1 << 16)).to_le_bytes());
                    assert!(
                        decode(&wrong_route).is_err(),
                        "copy encoding field must match the actual allocated source"
                    );
                    assert!(trust_cg_verify::aarch64_affine_lowering::check_aarch64_trust_ir_affine_bytes(&source, 0, &lir, &wrong_route).is_err(), "{ty:?}/{shape}/{level:?}: wrong live copy route passed the source/byte check");
                    copy_mutants += 1;
                }
                for (index, word) in result
                    .buffer
                    .code_slice()
                    .as_chunks::<4>()
                    .0
                    .iter()
                    .enumerate()
                    .map(|(i, b)| (i, u32::from_le_bytes(*b)))
                    .filter(|(_, word)| matches!(word & 0x7f800000, 0x52800000 | 0x12800000))
                {
                    // Change each end of imm16 in every published MOVZ/MOVN.
                    // The independent encoding gate covers live and dead
                    // materializations, even with warm proof caches. Count the
                    // separate, narrower return-value check honestly.
                    for bit in [5, 20] {
                        let mut changed = result.buffer.code_slice().to_vec();
                        changed[index * 4..index * 4 + 4]
                            .copy_from_slice(&(word ^ (1 << bit)).to_le_bytes());
                        assert!(
                            decode(&changed).is_err(),
                            "{ty:?}/{shape}/{level:?}: encoding gate accepted constant byte bit {bit}"
                        );
                        if trust_cg_verify::aarch64_affine_lowering::check_aarch64_trust_ir_affine_bytes(&source, 0, &lir, &changed).is_err() {
                            constant_return_mutants += 1;
                        } else {
                            assert_eq!(level, OptLevel::O0, "previously published live constant lost its source/byte control");
                            dead_constant_mutants += 1;
                        }
                        constant_mutants += 1;
                    }
                }
                if shape == "double" && level != OptLevel::O0 {
                    let bytes = result.buffer.code_slice();
                    let (index, word) = bytes
                        .as_chunks::<4>()
                        .0
                        .iter()
                        .enumerate()
                        .map(|(i, b)| (i, u32::from_le_bytes(*b)))
                        .find(|(_, word)| word & 0x7fe0fc00 == 0x0b000000)
                        .expect("source-attributed doubling ADD bytes");
                    assert_eq!((word >> 5) & 31, (word >> 16) & 31);
                    for bit in [0, 5, 10, 11, 16, 30, 31] {
                        let mut changed = bytes.to_vec();
                        changed[index * 4..index * 4 + 4]
                            .copy_from_slice(&(word ^ (1 << bit)).to_le_bytes());
                        assert!(trust_cg_verify::aarch64_affine_lowering::check_aarch64_trust_ir_affine_bytes(&source, 0, &lir, &changed).is_err(), "{ty:?}/{level:?}: accepted ADD byte bit {bit}");
                        add_mutants += 1;
                    }
                    // Preserve the independent checker's LSL coverage even
                    // while source-attributed ADD-to-LSL rewriting is disabled.
                    // These are `lsl w0, w0, #1; ret` and its x0 counterpart;
                    // they do not carry a forged machine-source proof stamp.
                    let shift: u32 = if mask == u32::MAX as u64 {
                        0x531f7800
                    } else {
                        0xd37ff800
                    };
                    let shifted: Vec<u8> = [shift, 0xd65f03c0]
                        .into_iter()
                        .flat_map(u32::to_le_bytes)
                        .collect();
                    trust_cg_verify::aarch64_affine_lowering::check_aarch64_trust_ir_affine_bytes(
                        &source, 0, &lir, &shifted,
                    )
                    .unwrap_or_else(|error| panic!("{ty:?}/{level:?}: explicit LSL: {error}"));
                    for bit in [0, 5, 10, 16, 22, 29, 31] {
                        let mut changed = shifted.clone();
                        changed[..4].copy_from_slice(&(shift ^ (1 << bit)).to_le_bytes());
                        assert!(trust_cg_verify::aarch64_affine_lowering::check_aarch64_trust_ir_affine_bytes(&source, 0, &lir, &changed).is_err(), "{ty:?}/{level:?}: accepted LSL byte bit {bit}");
                        shift_mutants += 1;
                    }
                }
                compiled += 1;
                for a in inputs {
                    for b in inputs {
                        // SAFETY: each arm uses the exact source scalar C ABI;
                        // proof-required compilation passed and the owner stays live.
                        let actual = unsafe {
                            match ty {
                                Ty::I32 => (result
                                    .buffer
                                    .get_fn_bound::<extern "C" fn(i32, i32) -> i32>("calculate")
                                    .unwrap()
                                    .as_ref())(
                                    a as i32, b as i32
                                ) as u32 as u64,
                                Ty::U32 => (result
                                    .buffer
                                    .get_fn_bound::<extern "C" fn(u32, u32) -> u32>("calculate")
                                    .unwrap()
                                    .as_ref())(
                                    a as u32, b as u32
                                ) as u64,
                                Ty::I64 => (result
                                    .buffer
                                    .get_fn_bound::<extern "C" fn(i64, i64) -> i64>("calculate")
                                    .unwrap()
                                    .as_ref())(
                                    a as i64, b as i64
                                ) as u64,
                                Ty::U64 => (result
                                    .buffer
                                    .get_fn_bound::<extern "C" fn(u64, u64) -> u64>("calculate")
                                    .unwrap()
                                    .as_ref())(a, b),
                                _ => unreachable!("closed type corpus"),
                            }
                        };
                        assert_eq!(
                            actual,
                            expected(shape, a, b) & mask,
                            "{ty:?}/{shape}/{level:?}/{a}/{b}"
                        );
                        calls += 1;
                    }
                }
            }
        }
    }
    println!(
        "SOURCE_BOUND_ARITHMETIC_NATIVE host={} compiled={compiled}/160 calls={calls}/23040 \
         refused={refused} failures={}",
        trust_cg_codegen::target::TargetSpec::host_for_architecture(Target::Aarch64).triple(),
        failures.len()
    );
    println!(
        "SOURCE_BOUND_ARITHMETIC_MUTANTS emitted_add={add_mutants} explicit_shift={shift_mutants} emitted_copy={copy_mutants} emitted_constant={constant_mutants} constant_return_refutations={constant_return_mutants} dead_constant_encoding_refutations={dead_constant_mutants}"
    );
    assert!(
        failures.is_empty(),
        "{} proof-required refusal(s); {}:\n{}",
        failures.len(),
        proof_tool_context(),
        failures.join("\n")
    );
    // The unchanged corpus now requires every row to publish and execute.
    assert_eq!((compiled, refused, calls), (160, 0, 23040));
    assert_eq!((add_mutants, shift_mutants), (84, 84));
    assert_eq!(copy_mutants, 78);
    assert_eq!(
        (
            constant_mutants,
            constant_return_mutants,
            dead_constant_mutants
        ),
        (124, 80, 44)
    );
}

#[test]
fn proof_required_arithmetic_executes_all_types_shapes_and_levels() {
    std::thread::Builder::new()
        .stack_size(16 * 1024 * 1024)
        .spawn(arithmetic_matrix)
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn raw_body_copy_exports_bind_exact_inputs_and_withdrawn_authority_refuses() {
    std::thread::Builder::new().stack_size(16 * 1024 * 1024).spawn(|| {
        use trust_cg_codegen::pipeline::{Pipeline, PipelineConfig};
        use trust_cg_ir::{AArch64Opcode as M, InstId, LoweringProvenance, MachInst, MachOperand as O};
        use trust_cg_ir::provenance::{SourceInstDigest, SourceInstId};
        use trust_cg_ir::regs::PReg;
        use trust_cg_verify::{FunctionVerifier, SourceBoundObligationKind, VerificationConfig};
        use trust_cg_verify::provenance_xcheck::ProvenanceXCheckMode;
        require_proof_tools();
        for (ty, bits) in [(Ty::I32, 32), (Ty::I64, 64)] {
            let source = module(ty, "sub");
            let (lir, _) = trust_cg_lower::translate_function_with_license(&source.functions[0], &source, &permit_unlicensed()).unwrap();
            let machine = Pipeline::new(PipelineConfig { opt_level: OptLevel::O0, verify: false, ..PipelineConfig::for_host_aarch64() })
                .with_proof_grade_aarch64_publication().prepare_function(&lir).unwrap();
            let verifier = FunctionVerifier::with_config(VerificationConfig::for_proof_promotion());
            let request = verifier.capture_request_with_mode(ProvenanceXCheckMode::Enforce);
            let (captured, exports) = verifier.verify_with_request_for_export(&machine, Some(&lir), &request);
            assert!(captured.report().emitted_opcode_inventory().is_promotable(), "i{bits}: {:?}; {}", captured.report(), proof_tool_context());
            let copies: Vec<_> = exports.iter().filter(|bound| bound.kind() == SourceBoundObligationKind::A64Body).collect();
            assert!(!copies.is_empty(), "O0 must exercise actual body-bound copy exports");
            for copy in &copies {
                assert!(matches!(machine.insts[copy.instruction_index()].opcode, M::MOVWrr | M::MOVXrr | M::MovR));
                assert!(copy.matches_aarch64_input(&machine, Some(&lir)));
                assert!(!copy.obligation().is_degenerate());
                assert_eq!(copy.query_sha256(), copies[0].query_sha256(), "one body theorem credits N live copies");
            }
            let copy_id = InstId(copies[0].instruction_index() as u32);
            for mutation in 0..2 {
                let mut wrong = machine.clone();
                if mutation == 0 {
                    let b = O::PReg(PReg::new(if bits == 32 { 33 } else { 1 }));
                    wrong.insts[copy_id.0 as usize].operands[1] = if wrong.insts[copy_id.0 as usize].operands[1] == b {
                        O::PReg(PReg::new(if bits == 32 { 32 } else { 0 }))
                    } else { b };
                } else {
                    wrong.set_inst_lowering_provenance(copy_id, LoweringProvenance::SourceInst {
                        id: SourceInstId { block: lir.entry_block.0, index: u32::MAX },
                        digest: SourceInstDigest(0), trust_ir_inst: None,
                    });
                }
                assert!(!captured.matches_aarch64_input(&wrong, Some(&lir)));
                assert!(!copies[0].matches_aarch64_input(&wrong, Some(&lir)));
                let (refused, exports) = verifier.verify_with_request_for_export(&wrong, Some(&lir), &request);
                assert!(!refused.report().emitted_opcode_inventory().is_promotable(), "i{bits} mutation{mutation}");
                assert!(exports.is_empty(), "TV-2 must precede body export retention");
            }
            let mut wrong_source = lir.clone();
            let op = wrong_source.blocks.get_mut(&wrong_source.entry_block).unwrap().instructions.iter_mut().find(|i| i.opcode == trust_cg_lower::instructions::Opcode::Isub).unwrap();
            op.opcode = trust_cg_lower::instructions::Opcode::Iadd;
            assert!(!copies[0].matches_aarch64_input(&machine, Some(&wrong_source)));
            let (refused, exports) = verifier.verify_with_request_for_export(&machine, Some(&wrong_source), &request);
            assert!(!refused.report().emitted_opcode_inventory().is_promotable() && exports.is_empty());
            let mut dead = machine.clone();
            let reg = |n: u16| O::PReg(PReg::new(n + if bits == 32 { 32 } else { 0 }));
            let id = dead.push_inst(MachInst::new(if bits == 32 { M::MOVWrr } else { M::MOVXrr }, vec![reg(11), reg(1)]));
            dead.blocks[0].insts.insert(2, id);
            let (refused, exports) = verifier.verify_with_request_for_export(&dead, Some(&lir), &request);
            assert!(!refused.report().emitted_opcode_inventory().is_promotable() && exports.is_empty(), "dead copy must remain uncredited");
            for (key, value) in [("TCG_REFINE_SOLVER", "0"), ("AY_SOLVER_PATH", "/nonexistent/body-export-ay"), ("TCG_EXTERNAL_CLEAN_CHECKER", "/nonexistent/body-export-clean")] {
                trust_cg_verify::env_lock::with_env_overrides(&[(key, value)], || {
                    let changed = verifier.capture_request_with_mode(ProvenanceXCheckMode::Enforce);
                    let (refused, exports) = verifier.verify_with_request_for_export(&machine, Some(&lir), &changed);
                    assert!(!refused.report().emitted_opcode_inventory().is_promotable() && exports.is_empty(), "withdrawn {key}");
                    let (retained, exports) = verifier.verify_with_request_for_export(&machine, Some(&lir), &request);
                    assert!(retained.report().emitted_opcode_inventory().is_promotable() && !exports.is_empty(), "immutable captured authority {key}");
                });
            }
            println!("SOURCE_BOUND_BODY_EXPORT bits={bits} live_copies={} wrong_route_and_stamp_refused=true wrong_source_and_dead_copy_refused=true missing_authorities=3", copies.len());
        }
    }).unwrap().join().unwrap();
}

fn request_controls() {
    use trust_cg_codegen::pipeline::{Pipeline, PipelineConfig};
    use trust_cg_ir::{AArch64Opcode, LoweringProvenance};
    use trust_cg_verify::provenance_xcheck::ProvenanceXCheckMode;
    use trust_cg_verify::{FunctionVerifier, VerificationConfig};
    let source = module(Ty::I64, "double");
    let (lir, _) = trust_cg_lower::translate_function_with_license(
        &source.functions[0],
        &source,
        &permit_unlicensed(),
    )
    .unwrap();
    // The host's own triple, prepared as the verifying JIT prepares it: a
    // proof-grade publication, which keeps the FP/LR envelope the
    // source-bound frame owner binds on aarch64-apple-darwin as on ELF.
    let pipeline = Pipeline::new(PipelineConfig {
        opt_level: OptLevel::O1,
        verify: false,
        ..PipelineConfig::for_host_aarch64()
    })
    .with_proof_grade_aarch64_publication();
    let machine = pipeline.prepare_function(&lir).unwrap();
    require_proof_tools();
    let id = machine
        .blocks
        .iter()
        .flat_map(|b| &b.insts)
        .copied()
        .find(|id| machine.insts[id.0 as usize].opcode == AArch64Opcode::AddRR)
        .expect("source-attributed doubling ADD");
    trust_cg_verify::env_lock::with_env_overrides(&[("TCG_BLOCKING_IDENTITY", "1")], || {
        let verifier = FunctionVerifier::with_config(VerificationConfig::for_proof_promotion());
        let request = verifier.capture_request_with_mode(ProvenanceXCheckMode::Enforce);
        let (captured, exported) =
            verifier.verify_with_request_for_export(&machine, Some(&lir), &request);
        assert_eq!(
            exported.len(),
            1,
            "the doubling ADD exports one replayed source-bound theorem; {}: {:?}",
            proof_tool_context(),
            captured.report()
        );
        assert_eq!(exported[0].instruction_index(), id.0 as usize);
        assert!(exported[0].matches_aarch64_input(&machine, Some(&lir)));
        assert!(exported[0].obligation().name.contains("AddRR i64"));
        assert!(
            captured.report().emitted_opcode_inventory().is_promotable(),
            "{}: {:?}",
            proof_tool_context(),
            captured.report()
        );
        assert!(captured.report().formally_credited_count() >= 4);
        assert!(captured.reusable_for(&request));
        assert!(captured.matches_aarch64_input(&machine, Some(&lir)));
        let warm = verifier.verify_with_request(&machine, Some(&lir), &request);
        assert!(warm.reusable_for(&request));
        for mutation in 0..3 {
            let mut changed = machine.clone();
            if mutation == 0 {
                changed.insts[id.0 as usize].opcode = AArch64Opcode::SubRR;
            } else {
                let mut stamp = changed.inst_lowering_provenance(id);
                let LoweringProvenance::SourceInst {
                    id: source_id,
                    digest,
                    ..
                } = &mut stamp
                else {
                    panic!("optimized ADD stamp must remain present")
                };
                if mutation == 1 {
                    digest.0 ^= 1;
                } else {
                    source_id.index = u32::MAX;
                }
                changed.set_inst_lowering_provenance(id, stamp);
            }
            assert!(!captured.matches_aarch64_input(&changed, Some(&lir)));
            assert!(!exported[0].matches_aarch64_input(&changed, Some(&lir)));
            let (rejected, exports) =
                verifier.verify_with_request_for_export(&changed, Some(&lir), &request);
            assert!(exports.is_empty());
            assert!(
                !rejected.report().emitted_opcode_inventory().is_promotable(),
                "machine mutation {mutation}"
            );
        }
        let mut changed = lir.clone();
        changed
            .blocks
            .get_mut(&changed.entry_block)
            .unwrap()
            .instructions[0]
            .args[1] = trust_cg_lower::instructions::Value(1);
        assert!(!captured.matches_aarch64_input(&machine, Some(&changed)));
        assert!(!exported[0].matches_aarch64_input(&machine, Some(&changed)));
        assert!(
            !verifier
                .verify_with_request(&machine, Some(&changed), &request)
                .report()
                .emitted_opcode_inventory()
                .is_promotable()
        );
        let (unbound, exports) = verifier.verify_with_request_for_export(&machine, None, &request);
        assert!(exports.is_empty());
        assert!(!unbound.report().emitted_opcode_inventory().is_promotable());
        trust_cg_verify::env_lock::with_env_overrides(&[("TCG_NO_PROOF_CACHE", "1")], || {
            let fresh_request = verifier.capture_request_with_mode(ProvenanceXCheckMode::Enforce);
            let (fresh, exports) =
                verifier.verify_with_request_for_export(&machine, Some(&lir), &fresh_request);
            assert_eq!(exports, exported);
            assert!(fresh.report().emitted_opcode_inventory().is_promotable());
            assert!(!fresh.reusable_for(&fresh_request));
            assert!(!captured.reusable_for(&fresh_request));
        });
        for (key, value) in [
            ("TCG_REFINE_SOLVER", "0"),
            (
                "TCG_EXTERNAL_CLEAN_CHECKER",
                "/nonexistent/trust-cg-required-clean-checker",
            ),
            ("AY_SOLVER_PATH", "/nonexistent/trust-cg-required-ay-solver"),
        ] {
            trust_cg_verify::env_lock::with_env_overrides(&[(key, value)], || {
                let denied = verifier.capture_request_with_mode(ProvenanceXCheckMode::Enforce);
                assert!(!captured.reusable_for(&denied));
                let (rejected, exports) =
                    verifier.verify_with_request_for_export(&machine, Some(&lir), &denied);
                assert!(exports.is_empty());
                assert!(
                    !rejected.report().emitted_opcode_inventory().is_promotable(),
                    "{key}"
                );
                // The earlier request retains the tools and policy it captured.
                let original = verifier.verify_with_request(&machine, Some(&lir), &request);
                assert!(original.report().emitted_opcode_inventory().is_promotable());
                assert!(original.reusable_for(&request));
            });
        }
    });
    println!(
        "SOURCE_BOUND_ARITHMETIC_AUTHORITY cache_and_no_cache=true changed_inputs_and_stamps_refused=true missing_authority_refused=true"
    );
}

#[test]
fn source_bound_arithmetic_preserves_request_authority_and_original_inputs() {
    std::thread::Builder::new()
        .stack_size(16 * 1024 * 1024)
        .spawn(request_controls)
        .unwrap()
        .join()
        .unwrap();
}

fn constant_controls() {
    use trust_cg_codegen::pipeline::{Pipeline, PipelineConfig};
    use trust_cg_ir::provenance::{SourceInstDigest, SourceInstId};
    use trust_cg_ir::regs::PReg;
    use trust_cg_ir::{AArch64Opcode, LoweringProvenance, MachInst, MachOperand};
    use trust_cg_lower::instructions::{Instruction, Opcode, Value};
    use trust_cg_verify::function_verifier::InstructionVerificationResult;
    use trust_cg_verify::provenance_xcheck::ProvenanceXCheckMode;
    use trust_cg_verify::{FunctionVerifier, VerificationConfig, VerificationStrength};

    require_proof_tools();
    trust_cg_verify::env_lock::with_env_overrides(&[("TCG_BLOCKING_IDENTITY", "1")], || {
        for (ty, lir_ty, dst) in [
            (Ty::I32, trust_cg_lower::Type::I32, 33),
            (Ty::I64, trust_cg_lower::Type::I64, 1),
        ] {
            let source = module(ty, "double");
            let (mut lir, _) = trust_cg_lower::translate_function_with_license(
                &source.functions[0],
                &source,
                &permit_unlicensed(),
            )
            .unwrap();
            let pipeline = Pipeline::new(PipelineConfig {
                opt_level: OptLevel::O1,
                verify: false,
                ..PipelineConfig::for_host_aarch64()
            })
            .with_proof_grade_aarch64_publication();
            let mut machine = pipeline.prepare_function(&lir).unwrap();
            let constant = Instruction {
                opcode: Opcode::Iconst {
                    ty: lir_ty.clone(),
                    imm: 3,
                },
                args: Vec::new(),
                results: vec![Value(90)],
            };
            let source_block = lir.blocks.get_mut(&lir.entry_block).unwrap();
            let source_id = SourceInstId {
                block: lir.entry_block.0,
                index: (source_block.instructions.len() - 1) as u32,
            };
            let digest = SourceInstDigest::compute_debug(&constant.opcode, 0, 1);
            assert!(matches!(
                source_block.instructions.last().unwrap().opcode,
                Opcode::Return
            ));
            source_block
                .instructions
                .insert(source_id.index as usize, constant);
            lir.value_types.insert(Value(90), lir_ty);
            // Inserting before Return shifts its source coordinates. Keep
            // each existing stamp's digest and source operation paired.
            for i in 0..machine.insts.len() {
                let inst_id = trust_cg_ir::InstId(i as u32);
                let mut stamp = machine.inst_lowering_provenance(inst_id);
                if let LoweringProvenance::SourceInst { id, .. } = &mut stamp
                    && id.block == source_id.block
                    && id.index >= source_id.index
                {
                    id.index += 1;
                    machine.set_inst_lowering_provenance(inst_id, stamp);
                }
            }
            let id = machine.push_inst(MachInst::new(
                AArch64Opcode::Movz,
                vec![
                    MachOperand::PReg(PReg::new(dst)),
                    MachOperand::Imm(3),
                    MachOperand::Imm(0),
                ],
            ));
            machine.blocks[0].insts.insert(2, id);
            machine.set_inst_lowering_provenance(
                id,
                LoweringProvenance::SourceInst {
                    id: source_id,
                    digest,
                    trust_ir_inst: None,
                },
            );
            let verifier = FunctionVerifier::with_config(VerificationConfig::for_proof_promotion());
            let request = verifier.capture_request_with_mode(ProvenanceXCheckMode::Enforce);
            let (captured, exports) =
                verifier.verify_with_request_for_export(&machine, Some(&lir), &request);
            assert!(
                captured.report().emitted_opcode_inventory().is_promotable(),
                "{}: {:?}",
                proof_tool_context(),
                captured.report()
            );
            let constant = exports
                .iter()
                .find(|bound| {
                    bound.kind() == trust_cg_verify::SourceBoundObligationKind::A64Constant
                })
                .expect("the dead Iconst needs its own exact replayed theorem");
            assert_eq!(constant.instruction_index(), id.0 as usize);
            assert!(constant.matches_aarch64_input(&machine, Some(&lir)));
            for (immediate, shift) in [(4, 0), (3, 16)] {
                let mut changed = machine.clone();
                changed.insts[id.0 as usize].operands[1] = MachOperand::Imm(immediate);
                changed.insts[id.0 as usize].operands[2] = MachOperand::Imm(shift);
                assert!(!constant.matches_aarch64_input(&changed, Some(&lir)));
                let (rejected, exports) =
                    verifier.verify_with_request_for_export(&changed, Some(&lir), &request);
                assert!(exports.is_empty());
                assert!(!rejected.report().emitted_opcode_inventory().is_promotable());
                // The body's returned result is unchanged. A Formal frame
                // cannot conceal the wrong dead constant's failed theorem.
                assert!(rejected.report().instructions.iter().any(|row| matches!(
                    row.result,
                    InstructionVerificationResult::Verified {
                        strength: VerificationStrength::Formal,
                        ..
                    }
                )));
                assert!(
                    matches!(rejected.report().instructions.iter().find(|row| row.inst_index == id.0 as usize).unwrap().result,
                        InstructionVerificationResult::Failed { ref proof_name, .. } if proof_name.starts_with("Source-bound AArch64 constant")
                    )
                );
            }
            for (key, value) in [
                ("TCG_REFINE_SOLVER", "0"),
                (
                    "TCG_EXTERNAL_CLEAN_CHECKER",
                    "/nonexistent/constant-owner-checker",
                ),
                ("AY_SOLVER_PATH", "/nonexistent/constant-owner-solver"),
            ] {
                trust_cg_verify::env_lock::with_env_overrides(&[(key, value)], || {
                    let denied = verifier.capture_request_with_mode(ProvenanceXCheckMode::Enforce);
                    let (rejected, exports) =
                        verifier.verify_with_request_for_export(&machine, Some(&lir), &denied);
                    assert!(exports.is_empty());
                    assert!(
                        !rejected.report().emitted_opcode_inventory().is_promotable(),
                        "{key}"
                    );
                    assert!(!captured.reusable_for(&denied));
                    let original = verifier.verify_with_request(&machine, Some(&lir), &request);
                    assert!(original.report().emitted_opcode_inventory().is_promotable());
                });
            }
        }
    });
    println!(
        "SOURCE_BOUND_CONSTANT_AUTHORITY correct_dead_constants=2 refuted_dead_constants=4 missing_authority_refusals=6"
    );
}

#[test]
fn source_bound_constants_refute_dead_writes_and_preserve_request_authority() {
    std::thread::Builder::new()
        .stack_size(16 * 1024 * 1024)
        .spawn(constant_controls)
        .unwrap()
        .join()
        .unwrap();
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
