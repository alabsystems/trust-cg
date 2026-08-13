// trust-cg-codegen/tests/jit_fail_closed_proof_policy.rs
//
// Regression coverage for #660 Phase 2: proof-required high-level JIT
// compilation must not silently lower to an unchecked executable buffer.

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
    mb.build()
}

#[cfg(target_arch = "aarch64")]
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

    mb.build()
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
fn compiler_jit_emit_proofs_attaches_executable_buffer_certificate() {
    let child = std::thread::Builder::new()
        .stack_size(16 * 1024 * 1024)
        .spawn(|| {
            let module = build_add_module();
            let compiler = Compiler::new(CompilerConfig {
                opt_level: OptLevel::O0,
                emit_proofs: true,
                parallel: false,
                ..CompilerConfig::jit_fast(Target::Aarch64)
            });

            let result = compiler
                .compile_module_to_jit(&module, &HashMap::new())
                .expect("proof-required JIT compile should succeed on verify-enabled AArch64");

            let public_proofs = result
                .proofs
                .as_ref()
                .expect("emit_proofs=true must populate public proof reports");
            assert!(
                !public_proofs.is_empty(),
                "proof-required JIT must emit public proof reports"
            );

            let cert = result
                .buffer
                .certificate("proof_required_add")
                .expect("proof-required JIT must attach a buffer certificate");
            assert_eq!(cert.function(), "proof_required_add");
            assert!(
                !cert.trust_ir_pairs().is_empty(),
                "JIT certificate must include provenance entries"
            );
            assert_eq!(
                result.buffer.certificates().count(),
                result.metrics.function_count,
                "proof-required JIT must attach one certificate per compiled function"
            );

            if public_proofs.iter().any(|proof| !proof.verified) {
                assert!(
                    !result.buffer.all_verified(),
                    "unverified public proof reports must not be hidden by an empty certificate map"
                );
            }
        })
        .expect("failed to spawn proof-policy test thread");

    child.join().expect("proof-policy test thread panicked");
}

#[test]
#[cfg(all(target_arch = "aarch64", feature = "verify"))]
fn compiler_jit_emit_proofs_accepts_covered_call_proof_entries() {
    let child = std::thread::Builder::new()
        .stack_size(16 * 1024 * 1024)
        .spawn(|| {
            let module = build_covered_call_module();
            let compiler = Compiler::new(CompilerConfig {
                opt_level: OptLevel::O0,
                emit_proofs: true,
                parallel: false,
                ..CompilerConfig::jit_fast(Target::Aarch64)
            });

            let result = compiler
                .compile_module_to_jit(&module, &HashMap::new())
                .expect("the now-covered call fixture should pass proof promotion");
            let proofs = result
                .proofs
                .expect("emit_proofs must return public proof reports");
            assert!(!proofs.is_empty(), "fixture must exercise proof promotion");
            assert!(
                proofs.iter().all(|proof| proof.verified),
                "covered call fixture must not publish an unverified report: {proofs:?}"
            );
        })
        .expect("failed to spawn proof-policy test thread");

    child.join().expect("proof-policy test thread panicked");
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
    });

    match compiler.compile_module_to_jit(&module, &HashMap::new()) {
        Err(trust_cg_codegen::compiler::CompileError::ProofsUnsupportedForTarget {
            target: Target::Aarch64,
        }) => {}
        Err(other) => panic!("expected ProofsUnsupportedForTarget(Aarch64), got {other}"),
        Ok(_) => panic!("proof-required JIT must fail closed without the verify feature"),
    }
}
