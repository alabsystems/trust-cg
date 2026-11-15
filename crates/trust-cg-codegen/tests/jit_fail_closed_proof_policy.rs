// trust-cg-codegen/tests/jit_fail_closed_proof_policy.rs
//
// Regression coverage for #660 Phase 2: proof-required high-level JIT
// compilation must not silently lower to an unchecked executable buffer.

// Test fixture: the big `Err` is the compiler's own public error type, not this file's to shrink.
#![allow(clippy::result_large_err)]

#[cfg(target_arch = "aarch64")]
use std::collections::HashMap;

#[cfg(target_arch = "aarch64")]
use trust_cg_codegen::compiler::Compiler;
use trust_cg_codegen::compiler::CompilerConfig;
#[cfg(feature = "verify")]
use trust_cg_codegen::compiler::JitValidationMode;
use trust_cg_codegen::jit::ProfileHookMode;
#[cfg(target_arch = "aarch64")]
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::Target;
#[cfg(target_arch = "aarch64")]
use trust_ir::Ty;
#[cfg(target_arch = "aarch64")]
use trust_ir_build::ModuleBuilder;

#[cfg(all(target_arch = "aarch64", feature = "verify"))]
#[path = "common/source_bound_proof_tools.rs"]
mod source_bound_proof_tools;
#[cfg(all(target_arch = "aarch64", feature = "verify"))]
use source_bound_proof_tools::proof_tool_context;

#[cfg(target_arch = "aarch64")]
fn build_add_module() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("jit_fail_closed_proof_policy");
    let ty = mb.add_func_type(vec![Ty::I64, Ty::I64], vec![Ty::I64]);
    let mut fb = mb.function("proof_required_add", ty);
    let entry = fb.create_block();
    let a = fb.add_block_param(entry, Ty::I64);
    let b = fb.add_block_param(entry, Ty::I64);
    fb.switch_to_block(entry);
    let result = fb.add(Ty::I64, a, b);
    fb.ret(vec![result]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

#[cfg(all(target_arch = "aarch64", feature = "verify"))]
fn build_covered_call_module() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("jit_covered_call_proof");
    let identity_ty = mb.add_func_type(vec![Ty::I64], vec![Ty::I64]);
    let add_ty = mb.add_func_type(vec![Ty::I64, Ty::I64], vec![Ty::I64]);

    {
        let mut fb = mb.function("identity_fn", identity_ty);
        let entry = fb.create_block();
        let value = fb.add_block_param(entry, Ty::I64);
        fb.switch_to_block(entry);
        fb.ret(vec![value]);
        fb.build();
    }

    {
        let mut fb = mb.function("call_then_add", add_ty);
        let entry = fb.create_block();
        let a = fb.add_block_param(entry, Ty::I64);
        let b = fb.add_block_param(entry, Ty::I64);
        fb.switch_to_block(entry);
        let called = fb.call(trust_ir::FuncId::new(0), vec![a]);
        let result = fb.add(Ty::I64, called, b);
        fb.ret(vec![result]);
        fb.build();
    }

    mb.build().expect("ModuleBuilder::build: test fixture")
}

#[test]
#[cfg(feature = "verify")]
fn compiler_config_emit_proofs_maps_to_verifying_jit_config() {
    let config = CompilerConfig {
        emit_proofs: true,
        ..CompilerConfig::jit_fast(Target::Aarch64)
    };

    assert_eq!(
        config.jit_validation_mode(),
        JitValidationMode::AlwaysVerify
    );
    let jit_config = config
        .to_jit_config(ProfileHookMode::None)
        .expect("verify-enabled builds can request proof-required JIT");

    assert!(jit_config.verify);
    assert_eq!(jit_config.opt_level, config.opt_level);
    assert_eq!(jit_config.profile_hooks, ProfileHookMode::None);
}

#[test]
#[cfg(not(feature = "verify"))]
fn compiler_config_emit_proofs_rejects_no_verify_build() {
    let config = CompilerConfig {
        emit_proofs: true,
        ..CompilerConfig::jit_fast(Target::Aarch64)
    };

    match config.to_jit_config(ProfileHookMode::None) {
        Err(trust_cg_codegen::compiler::CompileError::ProofsUnsupportedForTarget {
            target: Target::Aarch64,
        }) => {}
        Err(other) => panic!("expected ProofsUnsupportedForTarget(Aarch64), got {other}"),
        Ok(_) => panic!("proof-required JIT config must fail without the verify feature"),
    }
}

#[test]
fn compiler_config_emit_proofs_rejects_riscv64_jit_policy() {
    let config = CompilerConfig {
        emit_proofs: true,
        ..CompilerConfig::jit_fast(Target::Riscv64)
    };

    match config.to_jit_config(ProfileHookMode::None) {
        Err(trust_cg_codegen::compiler::CompileError::ProofsUnsupportedForTarget {
            target: Target::Riscv64,
        }) => {}
        Err(other) => panic!("expected ProofsUnsupportedForTarget(Riscv64), got {other}"),
        Ok(_) => panic!("RISC-V proof-required JIT policy must fail closed"),
    }
}

#[test]
#[cfg(all(target_arch = "aarch64", feature = "verify"))]
fn compiler_jit_emit_proofs_checks_bound_add_in_object_compatibility_mode() {
    let child = std::thread::Builder::new()
        .stack_size(16 * 1024 * 1024)
        .spawn(|| {
            let module = build_add_module();
            let compiler = |opt_level| {
                Compiler::new(CompilerConfig {
                    opt_level,
                    emit_proofs: true,
                    parallel: false,
                    ..CompilerConfig::jit_fast(Target::Aarch64)
                })
                .with_codegen_license(permit_unlicensed())
            };

            // O0's live result copy now has a raw body theorem. Both
            // allocations still require independently replayed evidence.
            for level in [OptLevel::O0, OptLevel::O1] {
                let result = compiler(level)
                    .compile_module_to_jit(&module, &HashMap::new())
                    .unwrap_or_else(|error| {
                        panic!(
                            "independently checked source-bound ADD: {error}; {}",
                            proof_tool_context()
                        )
                    });
                assert!(
                    result
                        .validation
                        .as_ref()
                        .unwrap()
                        .every_function_semantics_verified()
                );
                assert!(
                    result
                        .buffer
                        .certificate("proof_required_add")
                        .unwrap()
                        .is_verified()
                );
                // SAFETY: exact source ABI, successful verifying JIT, live owner.
                let add = unsafe {
                    result
                        .buffer
                        .get_fn_bound::<extern "C" fn(i64, i64) -> i64>("proof_required_add")
                        .unwrap()
                };
                for (a, b) in [(0, 0), (1, -1), (i64::MAX, 1), (i64::MIN, -1)] {
                    assert_eq!(add.as_ref()(a, b), a.wrapping_add(b));
                }
            }
        })
        .expect("failed to spawn proof-policy test thread");

    child.join().expect("proof-policy test thread panicked");
}

#[test]
#[cfg(all(target_arch = "aarch64", feature = "verify"))]
fn compiler_jit_emit_proofs_rejects_unproved_calling_frame() {
    let child = std::thread::Builder::new()
        .stack_size(16 * 1024 * 1024)
        .spawn(|| {
            let module = build_covered_call_module();
            let compiler = Compiler::new(CompilerConfig {
                opt_level: OptLevel::O0,
                emit_proofs: true,
                parallel: false,
                ..CompilerConfig::jit_fast(Target::Aarch64)
            })
            .with_codegen_license(permit_unlicensed());

            let error = compiler
                .compile_module_to_jit(&module, &HashMap::new())
                .expect_err("unproved calling frame must block public proof-report promotion");
            assert_call_frame_inventory_refusal(error);
        })
        .expect("failed to spawn proof-policy test thread");

    child.join().expect("proof-policy test thread panicked");
}

/// The calling frame's refusal names every uncredited opcode exactly.
///
/// This helper used to end its pin in *"first in call_then_add[8] is
/// AArch64::StpPreIndex (no proof mapping for opcode StpPreIndex)"*, and then
/// in the prologue `STP`'s own sampled pair obligation (E0.2: sampling is
/// never credit). Since the owner's Formal-only ruling (2026-09-29,
/// `trust_cg_verify::bound_memory_authority`) each of the four pair rows is
/// credited `Formal` by the replayed committed certificate of its own pair
/// FORM theorem, after its concrete-word refutation check held — on a host
/// whose `drat-trim` bytes the bound-memory manifest qualifies. There the
/// frame is refused for its five other rows only (the frame ADD, the two
/// register copies, the BL and the body ADD, whose candidates were a registry
/// theorem found by name, an instruction-derived obligation or a sampled
/// reconstruction) and no pair opcode is named. On an unqualified host the
/// pair rows stay uncredited as a fail-closed checker-identity miss, so the
/// earlier nine-row refusal stands, its first row the prologue `STP` with its
/// own sampled obligation plus the Formal-only note, and last the word-bound
/// memory-effect decomposition of its word (X-OPCODES-P1: every part holds;
/// recorded, never credit).
#[cfg(all(target_arch = "aarch64", feature = "verify"))]
fn assert_call_frame_inventory_refusal(error: trust_cg_codegen::compiler::CompileError) {
    match error {
        trust_cg_codegen::compiler::CompileError::ProofPromotionRejected {
            target: Target::Aarch64,
            reason,
        } => {
            // A build that records an AY that cannot run here appends its
            // refusal; the substantive reason is pinned either way.
            let reason = trust_cg_verify::ay_bridge::without_solver_refusal_note(&reason);
            if trust_cg_verify::bound_memory_authority::bound_memory_checker_qualification()
                .is_err()
            {
                let prefix = format!(
                    "non_verified proof entry opcode_inventory_instruction_0 in call_then_add: \
                     emitted opcode inventory found 9 uncovered non-pseudo opcode(s) across \
                     8 distinct opcode(s) [AArch64::StpPreIndex, AArch64::StpRI, AArch64::AddRI, \
                     AArch64::MOVXrr, AArch64::Bl, AArch64::AddRR, AArch64::LdpRI, \
                     AArch64::LdpPostIndex]; first in \
                     call_then_add[8] is AArch64::StpPreIndex \
                     ({}: `RECONSTRUCTED PairMemory_STP_",
                    trust_cg_verify::function_verifier::STATISTICAL_EVIDENCE_IS_NOT_CREDIT
                );
                let first_row = reason.strip_prefix(&prefix).unwrap_or_else(|| {
                    panic!(
                        "expected the unqualified host's nine-row refusal, got {reason}; {}",
                        proof_tool_context()
                    )
                });
                assert!(
                    first_row.contains(" -> StpPreIndex (real-operand, ")
                        && first_row.contains(" sampled inputs; ")
                        && first_row.contains(
                            trust_cg_verify::bound_memory_authority::BOUND_MEMORY_FORMAL_ONLY
                        )
                        && first_row.contains(
                            trust_cg_verify::bound_memory_authority::CHECKER_IDENTITY_MISS
                        )
                        && first_row.contains(&format!(
                            "; {}: `A64 memory effect StpPreIndex 0x",
                            trust_cg_verify::function_verifier::MEMORY_EFFECT_IS_NOT_CREDIT
                        )),
                    "the first pair row must cite its own sampled obligation, the \
                     checker-identity miss and its memory-effect decomposition: {reason}"
                );
            } else {
                let prefix = format!(
                    "non_verified proof entry opcode_inventory_instruction_0 in call_then_add: \
                     emitted opcode inventory found 5 uncovered non-pseudo opcode(s) across \
                     4 distinct opcode(s) [AArch64::AddRI, AArch64::MOVXrr, AArch64::Bl, \
                     AArch64::AddRR]; first in call_then_add[10] is AArch64::AddRI \
                     ({}: `RECONSTRUCTED Iadd_64 -> AddRI (real-operand)`",
                    trust_cg_verify::function_verifier::STATISTICAL_EVIDENCE_IS_NOT_CREDIT
                );
                assert!(
                    reason.starts_with(&prefix) && reason.ends_with(" sampled inputs)"),
                    "expected the frame refused for its five non-pair rows only, got {reason}; {}",
                    proof_tool_context()
                );
                for pair in ["StpPreIndex", "StpRI", "LdpRI", "LdpPostIndex"] {
                    assert!(
                        !reason.contains(&format!("AArch64::{pair}")),
                        "a credited pair row {pair} is still named: {reason}"
                    );
                }
            }
            assert!(
                !reason.contains("no proof mapping for opcode"),
                "an opcode with no proof mapping reappeared in this module: {reason}"
            );
        }
        other => panic!("expected the calling frame's inventory refusal, got {other}"),
    }
}

#[cfg(all(target_arch = "aarch64", feature = "verify"))]
fn assert_jit_certificate_refusal(error: trust_cg_codegen::compiler::CompileError, name: &str) {
    match error {
        trust_cg_codegen::compiler::CompileError::ProofPromotionRejected {
            target: Target::Aarch64,
            reason,
        } => assert_eq!(
            trust_cg_verify::ay_bridge::without_solver_refusal_note(&reason),
            format!(
                "aarch64 JIT function {name} has no non-vacuous proof-grade machine-IR \
                 certificate under always-verify mode"
            ),
            "{}",
            proof_tool_context()
        ),
        other => panic!("expected exact independent JIT certificate refusal, got {other}"),
    }
}

#[test]
#[cfg(all(target_arch = "aarch64", feature = "verify"))]
fn compiler_jit_emit_proofs_executes_source_bound_identity_o0_through_o3() {
    use sha2::Digest;

    std::thread::Builder::new()
        .stack_size(16 * 1024 * 1024)
        .spawn(|| {
            let mut module = build_covered_call_module();
            // Retain the exact identity callee from the refused two-function
            // fixture. Only the caller is removed; its unused type is valid.
            assert_eq!(module.functions.pop().unwrap().name, "call_then_add");
            let mut native_calls = 0;
            for level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
                let compiler = Compiler::new(CompilerConfig {
                    opt_level: level,
                    emit_proofs: true,
                    parallel: false,
                    ..CompilerConfig::jit_fast(Target::Aarch64)
                })
                .with_codegen_license(permit_unlicensed());
                let result = compiler
                    .compile_module_to_jit(&module, &HashMap::new())
                    .unwrap_or_else(|error| {
                        panic!(
                            "source-bound identity must pass actual proof-required JIT at \
                             {level:?}: {error}; {}",
                            proof_tool_context()
                        )
                    });
                let validation = result.validation.as_ref().expect("JIT validation");
                assert_eq!(validation.mode, JitValidationMode::AlwaysVerify);
                assert!(validation.every_function_semantics_verified());
                assert_eq!(validation.functions.len(), 1);
                assert_eq!(
                    validation.published_image_sha256,
                    result.buffer.published_image_sha256()
                );
                assert_eq!(
                    validation.published_image_sha256,
                    format!("{:x}", sha2::Sha256::digest(result.buffer.code_slice()))
                );
                let certificate = result.buffer.certificate("identity_fn").unwrap();
                assert!(certificate.has_checked_semantics());
                assert!(!certificate.is_verified(), "RET-only structural evidence is not an instruction proof");
                assert!(certificate.to_json().contains("\"source_checked_structural_return\": true"));
                assert!(!certificate.chain().certificates.iter().any(|row|
                    row.obligation_name == trust_cg_verify::source_bound_frame::FRAME_OBLIGATION_NAME));
                assert!(!certificate.served_from_cache());
                // SAFETY: the retained source has this exact scalar C ABI.
                // Proof-required compilation succeeded and the buffer owns
                // the executable bytes throughout every call.
                let identity = unsafe {
                    result
                        .buffer
                        .get_fn_bound::<extern "C" fn(i64) -> i64>("identity_fn")
                }
                .unwrap();
                for value in [i64::MIN, i64::MIN + 1, -42, -1, 0, 1, 42, i64::MAX] {
                    assert_eq!((identity.as_ref())(value), value, "{level:?}");
                    native_calls += 1;
                }
            }
            assert_eq!(native_calls, 32);
            println!("SOURCE_BOUND_IDENTITY_NATIVE opt_levels=4 calls=32 structural_returns=4 formal_frame_rows=0");
        })
        .expect("spawn proof-policy thread")
        .join()
        .expect("proof-policy thread panicked");
}

// Default Darwin leaves publish without proof-only FP/LR records. Arithmetic
// still requires independently replayed instruction proofs; a RET-only identity
// carries its separately classified exact source/ABI structural check.

#[test]
#[cfg(all(target_arch = "aarch64", target_os = "macos", feature = "verify"))]
fn darwin_verifying_jit_leaves_publish_frameless_with_exact_source_evidence() {
    use trust_cg_verify::source_bound_frame::FRAME_OBLIGATION_NAME;
    use trust_cg_verify::verify::VerificationStrength;
    // stp x29, x30, [sp, #-16]! / ldp x29, x30, [sp], #16 / ret
    const SAVE_FP_LR: u32 = 0xa9bf_7bfd;
    const RESTORE_FP_LR: u32 = 0xa8c1_7bfd;
    const RET: u32 = 0xd65f_03c0;

    std::thread::Builder::new()
        .stack_size(16 * 1024 * 1024)
        .spawn(|| {
            let mut identity = build_covered_call_module();
            assert_eq!(identity.functions.pop().unwrap().name, "call_then_add");
            let mut shifted = ModuleBuilder::new("jit_frameless_add_shifted");
            let ty = shifted.add_func_type(vec![Ty::I64], vec![Ty::I64]);
            let mut fb = shifted.function("add_4096", ty);
            let entry = fb.create_block();
            let a = fb.add_block_param(entry, Ty::I64);
            fb.switch_to_block(entry);
            let c = fb.iconst(Ty::I64, 4096);
            let sum = fb.add(Ty::I64, a, c);
            fb.ret(vec![sum]);
            fb.build();
            let mut published = Vec::new();
            for (module, name, unary_offset) in [
                (build_add_module(), "proof_required_add", None),
                (identity, "identity_fn", Some(0)),
                (
                    shifted.build().expect("ModuleBuilder::build: test fixture"),
                    "add_4096",
                    Some(4096),
                ),
            ] {
                for level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
                    let compiler = Compiler::new(CompilerConfig {
                        opt_level: level,
                        emit_proofs: false,
                        jit_validation_mode_override: Some(JitValidationMode::AlwaysVerify),
                        parallel: false,
                        ..CompilerConfig::jit_fast(Target::Aarch64)
                    })
                    .with_codegen_license(permit_unlicensed());
                    let result = compiler
                        .compile_module_to_jit(&module, &HashMap::new())
                        .unwrap_or_else(|error| {
                            panic!("{name} {level:?}: {error}; {}", proof_tool_context())
                        });
                    let validation = result.validation.as_ref().expect("JIT validation");
                    assert_eq!(validation.mode, JitValidationMode::AlwaysVerify);
                    assert!(validation.every_function_semantics_verified());
                    let certificate = result.buffer.certificate(name).unwrap();
                    assert!(certificate.has_checked_semantics(), "{name} {level:?}");
                    assert_eq!(
                        certificate.is_verified(),
                        name != "identity_fn",
                        "{name} {level:?}"
                    );
                    let range = certificate.code_range();
                    let range =
                        usize::try_from(range.start).unwrap()..usize::try_from(range.end).unwrap();
                    let (words, rest) = result.buffer.code_slice()[range].as_chunks::<4>();
                    assert!(
                        rest.is_empty(),
                        "{name} {level:?}: partial instruction word"
                    );
                    let words: Vec<u32> = words.iter().copied().map(u32::from_le_bytes).collect();
                    assert_eq!(words.last(), Some(&RET));
                    assert!(
                        !words
                            .iter()
                            .any(|word| [SAVE_FP_LR, RESTORE_FP_LR].contains(word)),
                        "{name} {level:?} has an unnecessary frame: {words:08x?}"
                    );
                    let rows = &certificate.chain().certificates;
                    for row in rows {
                        assert!(row.result.is_verified(), "{name} {level:?}: {row:?}");
                        assert!(
                            !matches!(row.strength, VerificationStrength::Statistical { .. }),
                            "{name} {level:?} published on sampled evidence: {row:?}"
                        );
                    }
                    assert!(
                        !rows
                            .iter()
                            .any(|row| row.obligation_name == FRAME_OBLIGATION_NAME),
                        "{name} {level:?} unexpectedly relies on frame credit: {rows:?}"
                    );
                    let buffer = &result.buffer;
                    for value in [i64::MIN, -4096, -1, 0, 1, i64::MAX] {
                        // SAFETY: each fixture has exactly this scalar C ABI,
                        // the verifying JIT succeeded and `buffer` is live.
                        let (actual, expected) = unsafe {
                            match unary_offset {
                                Some(offset) => {
                                    let f = buffer
                                        .get_fn_bound::<extern "C" fn(i64) -> i64>(name)
                                        .unwrap();
                                    (f.as_ref()(value), value.wrapping_add(offset))
                                }
                                None => {
                                    let f = buffer
                                        .get_fn_bound::<extern "C" fn(i64, i64) -> i64>(name)
                                        .unwrap();
                                    (f.as_ref()(value, 7), value.wrapping_add(7))
                                }
                            }
                        };
                        assert_eq!(actual, expected, "{name} {level:?} {value}");
                    }
                    published.push((name, level));
                }
            }
            assert_eq!(published.len(), 12);
            println!(
                "DARWIN_VERIFYING_JIT_LEAF published={} refused=0",
                published.len()
            );
        })
        .expect("spawn proof-policy thread")
        .join()
        .expect("proof-policy thread panicked");
}

#[cfg(all(target_arch = "aarch64", feature = "verify"))]
mod independent_jit_certificate_gate {
    use super::*;
    use std::sync::Arc;
    use trust_cg_codegen::jit::{JitCompiler, JitConfig};
    use trust_cg_codegen::jit_cert::JitCertCache;
    use trust_cg_ir::function::{MachFunction, Signature, Type};
    use trust_cg_ir::inst::{AArch64Opcode, MachInst};
    use trust_cg_ir::operand::MachOperand;
    use trust_cg_ir::regs::{X0, X1};

    // Already-physical, pair-free trap-terminated fragments for the public raw
    // JIT API, never called. They do not run ISel/frame insertion. RET has its
    // own withdrawn proof mapping and cannot isolate sampling or non-vacuity.
    // A raw BRK has no replayed source to bind it to a `Trap` terminator, so
    // the verifier's trap-guard analysis refuses it by name (L04-P12).
    // The trap-only fragment is not an identity function or a returning API.
    fn raw_trap_fragment(add: bool) -> MachFunction {
        let mut function = MachFunction::new(
            if add {
                "raw_sampled_add_then_trap"
            } else {
                "raw_trap_only"
            }
            .into(),
            Signature::new(
                if add {
                    vec![Type::I64, Type::I64]
                } else {
                    vec![]
                },
                vec![],
            ),
        );
        if add {
            let instruction = function.push_inst(MachInst::new(
                AArch64Opcode::AddRR,
                vec![
                    MachOperand::PReg(X0),
                    MachOperand::PReg(X0),
                    MachOperand::PReg(X1),
                ],
            ));
            function.append_inst(function.entry, instruction);
        }
        let trap = function.push_inst(MachInst::new(AArch64Opcode::Brk, vec![]));
        function.append_inst(function.entry, trap);
        function
    }

    fn assert_pair_free_certificate_refuses(add: bool) {
        let function = raw_trap_fragment(add);
        let report = trust_cg_verify::verify_function(&function);
        assert!(report.precondition_failure.is_none(), "{report:?}");
        assert_eq!(report.total(), if add { 2 } else { 1 });
        assert_eq!(report.failed_count(), 0);
        // The 64-bit ADD discharges only by sampling: reported, never credited.
        // The unbound raw BRK is refused by name, not skipped (L04-P12), so
        // neither fragment is promotable; before, the trap-only fragment was
        // vacuously promotable.
        assert_eq!(report.unverified_count(), usize::from(add) + 1);
        assert_eq!(report.sampled_uncredited_count(), usize::from(add));
        assert_eq!(report.degenerate_verified_count(), 0);
        assert_eq!(report.skipped_count(), 0);
        assert_eq!(report.genuinely_verified_count(), 0);
        assert!(
            report.instructions.iter().any(|row| matches!(
                &row.result,
                trust_cg_verify::function_verifier::InstructionVerificationResult::Unverified {
                    reason
                } if reason.starts_with("[TCG-TRAP-GUARD] refused")
            )),
            "{report:?}"
        );
        assert!(
            !report.emitted_opcode_inventory().is_promotable(),
            "{report:?}"
        );

        let cache = Arc::new(JitCertCache::disabled());
        let jit = JitCompiler::new(JitConfig {
            verify: true,
            cache_certificates: false,
            ..JitConfig::default()
        })
        .with_certificate_cache(Arc::clone(&cache));
        let buffer = jit
            .compile_raw(std::slice::from_ref(&function), &HashMap::new())
            .expect("pair-free raw diagnostic compilation must reach certificate construction");
        assert_eq!(
            cache.verifier_runs(),
            1,
            "actual verifier ran, not a cache hit"
        );
        assert_eq!(buffer.function_ranges().len(), 1);
        assert_eq!(buffer.certificates().count(), 1);
        let certificate = buffer
            .certificate(&function.name)
            .expect("actual raw JIT certificate");
        assert_eq!(certificate.function(), function.name);
        assert_eq!(
            certificate.code_range().end - certificate.code_range().start,
            if add { 8 } else { 4 }
        );
        assert!(!certificate.served_from_cache());
        assert!(
            certificate.replay_check(),
            "chain integrity is not proof authority"
        );
        // An uncredited instruction contributes no verified chain row, so no
        // row can carry sampled strength.
        assert!(
            certificate.chain().certificates.is_empty(),
            "{:?}",
            certificate.chain().certificates
        );
        assert!(
            !certificate.is_verified(),
            "sampled or vacuous evidence is not proof-grade"
        );
        assert!(certificate.lowering_certificate().is_none());
        assert!(!buffer.all_function_semantics_verified());
    }

    fn assert_explicit_verifying_jit_refuses(module: trust_ir::Module, name: &str) {
        let config = CompilerConfig {
            opt_level: OptLevel::O0,
            emit_proofs: false,
            jit_validation_mode_override: Some(JitValidationMode::AlwaysVerify),
            parallel: false,
            ..CompilerConfig::jit_fast(Target::Aarch64)
        };
        assert_eq!(
            config.jit_validation_mode(),
            JitValidationMode::AlwaysVerify
        );
        let jit_config = config.to_jit_config(ProfileHookMode::None).unwrap();
        assert!(jit_config.verify);
        assert!(!jit_config.cache_certificates);
        let compiler = Compiler::new(config).with_codegen_license(permit_unlicensed());
        // Explicit AlwaysVerify is a public mode independent of optional
        // object reports. The raw controls above independently isolate
        // sampling/non-vacuity from the high-level compilation below.
        // The identity leaf can discharge; the caller still has frame debt.
        let error = compiler
            .compile_module_to_jit(&module, &HashMap::new())
            .expect_err("explicit AlwaysVerify must reject the actual per-buffer certificate");
        assert_jit_certificate_refusal(error, name);
    }

    #[test]
    fn compiler_jit_verify_override_proves_bound_add_and_rejects_raw_sampling() {
        std::thread::Builder::new()
            .stack_size(16 * 1024 * 1024)
            .spawn(|| {
                assert_pair_free_certificate_refuses(true);
                let compiler = |opt_level| {
                    Compiler::new(CompilerConfig {
                        opt_level,
                        emit_proofs: false,
                        jit_validation_mode_override: Some(JitValidationMode::AlwaysVerify),
                        parallel: false,
                        ..CompilerConfig::jit_fast(Target::Aarch64)
                    })
                    .with_codegen_license(permit_unlicensed())
                };
                // Report emission remains optional. O0 and O1 both need
                // a complete independently replayed function certificate.
                for level in [OptLevel::O0, OptLevel::O1] {
                    let result = compiler(level)
                        .compile_module_to_jit(&build_add_module(), &HashMap::new())
                        .unwrap_or_else(|error| {
                            panic!(
                                "explicit verifying mode accepts independently proved \
                             source-bound ADD: {error}; {}",
                                proof_tool_context()
                            )
                        });
                    let validation = result.validation.as_ref().unwrap();
                    assert_eq!(validation.mode, JitValidationMode::AlwaysVerify);
                    assert!(validation.every_function_semantics_verified());
                    assert!(
                        result.proofs.is_none(),
                        "report emission is independently optional"
                    );
                    assert!(
                        result
                            .buffer
                            .certificate("proof_required_add")
                            .unwrap()
                            .is_verified()
                    );
                    // SAFETY: exact source ABI, successful verifying JIT, live owner.
                    let add = unsafe {
                        result
                            .buffer
                            .get_fn_bound::<extern "C" fn(i64, i64) -> i64>("proof_required_add")
                            .unwrap()
                    };
                    assert_eq!(add.as_ref()(i64::MAX, 1), i64::MIN);
                }
            })
            .expect("spawn proof-policy thread")
            .join()
            .expect("proof-policy thread panicked");
    }

    #[test]
    fn compiler_jit_verify_override_rejects_calling_frame_and_raw_trap_only_certificate() {
        std::thread::Builder::new()
            .stack_size(16 * 1024 * 1024)
            .spawn(|| {
                assert_pair_free_certificate_refuses(false);
                assert_explicit_verifying_jit_refuses(build_covered_call_module(), "call_then_add");
            })
            .expect("spawn proof-policy thread")
            .join()
            .expect("proof-policy thread panicked");
    }
}

/// An installed AY that cannot run must not read as an ordinary proof gap.
/// Under umask 0002 `create_dir_all` left `<cache>/trust-cg` group-writable,
/// the AY private copy refuses any AY beneath it, and every proof-required
/// compile was refused naming only the unproved instruction (measured
/// 2026-09-26). The refusal now carries the `TCG-AY-IDENTITY-*` refusal of
/// the function-verification request the evidence came from: for a build that
/// records the toolchain AY, the directory, its mode and the remedy. The
/// directory is never changed. Runs in a child test process whose
/// `XDG_CACHE_HOME` holds such a directory.
#[test]
#[cfg(all(target_arch = "aarch64", feature = "verify", unix))]
fn proof_refusal_names_an_ay_refused_beneath_a_group_writable_cache() {
    use std::os::unix::fs::PermissionsExt;
    const CHILD: &str = "JIT_PROOF_POLICY_OPEN_CACHE_CHILD";
    const NAME: &str = "proof_refusal_names_an_ay_refused_beneath_a_group_writable_cache";
    let mode = |path: &std::path::Path| {
        std::fs::symlink_metadata(path)
            .unwrap()
            .permissions()
            .mode()
            & 0o7777
    };
    let Some(cache) = std::env::var_os(CHILD).map(std::path::PathBuf::from) else {
        let base = tempfile::tempdir().unwrap();
        std::fs::set_permissions(base.path(), std::fs::Permissions::from_mode(0o700)).unwrap();
        let cache = base.path().canonicalize().unwrap();
        let trust_cg = cache.join("trust-cg");
        std::fs::create_dir(&trust_cg).unwrap();
        std::fs::set_permissions(&trust_cg, std::fs::Permissions::from_mode(0o775)).unwrap();
        let output = std::process::Command::new(std::env::current_exe().unwrap())
            .args(["--exact", NAME, "--nocapture", "--test-threads=1"])
            .env(CHILD, &cache)
            .env("XDG_CACHE_HOME", &cache)
            // The toolchain route: the one a proof-required compile uses.
            .env_remove("AY_SOLVER_PATH")
            .output()
            .unwrap();
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        // Only the refusal line: a second libtest summary in this transcript
        // would make the floor's one-suite check reject the run.
        for line in stdout
            .lines()
            .filter(|line| line.contains("OPEN_CACHE_PROOF_REFUSAL"))
        {
            println!(
                "{}",
                &line[line.find("OPEN_CACHE_PROOF_REFUSAL").unwrap_or(0)..]
            );
        }
        assert!(
            output.status.success() && stdout.contains("1 passed"),
            "child: {}\n{stdout}\n{stderr}",
            output.status
        );
        assert_eq!(
            mode(&trust_cg),
            0o775,
            "an existing directory is never changed"
        );
        return;
    };
    let trust_cg = cache.join("trust-cg");
    std::thread::Builder::new()
        .stack_size(16 * 1024 * 1024)
        .spawn(move || {
            let compiler = Compiler::new(CompilerConfig {
                opt_level: OptLevel::O0,
                emit_proofs: true,
                parallel: false,
                ..CompilerConfig::jit_fast(Target::Aarch64)
            })
            .with_codegen_license(permit_unlicensed());
            let error = compiler
                .compile_module_to_jit(&build_add_module(), &HashMap::new())
                .expect_err("no solver-backed evidence can exist without an AY");
            let reason = match error {
                trust_cg_codegen::compiler::CompileError::ProofPromotionRejected {
                    target: Target::Aarch64,
                    reason,
                } => reason,
                other => panic!("expected a proof-promotion refusal, got {other}"),
            };
            println!("OPEN_CACHE_PROOF_REFUSAL {reason}");
            match trust_cg_verify::ay_identity::recorded_toolchain_ay_identity() {
                Ok(_) => {
                    for needed in [
                        format!(
                            "; {}",
                            trust_cg_verify::ay_bridge::REQUEST_REFUSAL_NOTE_HEAD
                        ),
                        "[TCG-AY-IDENTITY-UNMATERIALIZED]".to_owned(),
                        format!("{} has mode 0775", trust_cg.display()),
                        format!("`chmod go-w {}`", trust_cg.display()),
                    ] {
                        assert!(reason.contains(&needed), "{needed:?} missing from {reason}");
                    }
                    let substantive =
                        trust_cg_verify::ay_bridge::without_solver_refusal_note(&reason);
                    // Removing the appended request note preserves the actual
                    // body owner's replay diagnostic, which can itself name
                    // the same captured AY refusal. It must not remove that
                    // substantive diagnostic or resolve another solver.
                    assert!(!substantive.contains(trust_cg_verify::ay_bridge::REQUEST_REFUSAL_NOTE_HEAD), "{substantive}");
                    assert!(substantive.starts_with("non_verified proof entry opcode_inventory_instruction_0 in proof_required_add:"), "{substantive}");
                    assert!(substantive.contains("source-bound AArch64 body needs independently replayed proof"), "{substantive}");
                }
                // A build that records no AY admits none anywhere, and its
                // refusal text is unchanged.
                Err(_) => {
                    assert!(!reason.contains("TCG-AY-IDENTITY"), "{reason}");
                    assert_eq!(
                        trust_cg_verify::ay_bridge::without_solver_refusal_note(&reason),
                        reason
                    );
                }
            }
            assert_eq!(
                mode(&trust_cg),
                0o775,
                "an existing directory is never changed"
            );
        })
        .expect("spawn proof-policy thread")
        .join()
        .expect("proof-policy thread panicked");
}

#[test]
#[cfg(all(target_arch = "aarch64", not(feature = "verify")))]
fn compiler_jit_emit_proofs_rejects_no_verify_build() {
    let module = build_add_module();
    let compiler = Compiler::new(CompilerConfig {
        opt_level: OptLevel::O0,
        emit_proofs: true,
        parallel: false,
        ..CompilerConfig::jit_fast(Target::Aarch64)
    })
    .with_codegen_license(permit_unlicensed());

    match compiler.compile_module_to_jit(&module, &HashMap::new()) {
        Err(trust_cg_codegen::compiler::CompileError::ProofsUnsupportedForTarget {
            target: Target::Aarch64,
        }) => {}
        Err(other) => panic!("expected ProofsUnsupportedForTarget(Aarch64), got {other}"),
        Ok(_) => panic!("proof-required JIT must fail closed without the verify feature"),
    }
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
// Its callers are target-gated tests; on a host where none of them compiles
// the helper is unused.
#[allow(dead_code)]
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
