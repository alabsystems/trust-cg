// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! The actual captured black_box body must promote through the real compiler.
//! The fixture's raw-body test licence is separate from proof promotion and
//! grants no Rust NoUB, frontend, installed-image or whole-compiler authority.

#![cfg(feature = "verify")]

use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::TargetSpec;
use trust_cg_codegen::{Compiler, CompilerConfig};

#[test]
fn captured_black_box_framed_control_requires_real_proof_promotion() {
    let module = trust_ir::binary::deserialize_module(include_bytes!(
        "fixtures/aarch64_framed_identity/black_box.trust_irbin"
    ))
    .expect("decode the unchanged module from the actual proof-required attempt");
    let compiler = Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level: OptLevel::O0,
            emit_proofs: true,
            aarch64_force_frame_pointers: true,
            parallel: false,
            eh_frames_cannot_unwind: true,
            ..Default::default()
        },
        TargetSpec::parse("aarch64-apple-darwin").unwrap(),
    )
    .with_codegen_license(
        trust_cg_lower::CodegenLicensePolicy::default()
            .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit),
    );
    let output = compiler
        .compile(&module)
        .expect("the actual framed identity must pass the unchanged certificate promotion policy");
    assert!(!output.object_code.is_empty());
    let proofs = output.proofs.as_ref().expect("proofs were requested");
    assert!(!proofs.is_empty());
    assert!(proofs.iter().all(|proof| proof.verified));
    let branch = proofs
        .iter()
        .find(|proof| {
            proof
                .rule_name
                .starts_with("Source-bound AArch64 framed control theorem")
        })
        .expect("a real independently replayed next-PC theorem must cover the branch");
    assert!(branch.strength.contains("Formal"), "{branch:?}");
    #[cfg(feature = "verify")]
    assert!(
        branch.source_bound_obligation.is_some(),
        "the final credited row must retain its request-bound export obligation"
    );
}

#[path = "common/function_words.rs"]
mod function_words;

#[test]
fn captured_black_box_proofs_preserve_the_frameless_output_at_every_level() {
    let module = trust_ir::binary::deserialize_module(include_bytes!(
        "fixtures/aarch64_framed_identity/black_box.trust_irbin"
    ))
    .unwrap();
    for level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
        let compile = |proofs| {
            Compiler::new_for_target_spec(
                CompilerConfig {
                    opt_level: level,
                    emit_proofs: proofs,
                    parallel: false,
                    eh_frames_cannot_unwind: true,
                    ..Default::default()
                },
                TargetSpec::parse("aarch64-apple-darwin").unwrap(),
            )
            .with_codegen_license(
                trust_cg_lower::CodegenLicensePolicy::default()
                    .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit),
            )
            .compile(&module)
            .unwrap()
        };
        let diagnostic = compile(false);
        let checked = compile(true);
        let reference = function_words::function_words(&diagnostic.object_code);
        let words = function_words::function_words(&checked.object_code);
        assert_eq!(
            words, reference,
            "proof mode must not add a frame: {level:?}"
        );
        assert_eq!(words.len(), 1);
        let (name, body) = words.first_key_value().unwrap();
        println!(
            "FRAMELESS_BLACK_BOX {level:?} function={name} words={body:x?} object_bytes={}",
            checked.object_code.len()
        );
        assert!(
            body.len() <= 2,
            "the original storage-free identity needs at most B;RET"
        );
        assert_eq!(body.last(), Some(&0xd65f03c0));
        let branches = body
            .iter()
            .filter(|word| **word & 0xfc00_0000 == 0x1400_0000)
            .count();
        let proofs = checked.proofs.as_ref().unwrap();
        assert!(proofs.iter().all(|proof| proof.verified));
        let controls: Vec<_> = proofs
            .iter()
            .filter(|proof| {
                proof
                    .rule_name
                    .starts_with("Source-bound AArch64 frameless control theorem")
            })
            .collect();
        assert_eq!(controls.len(), branches);
        for proof in controls {
            assert_eq!(proof.strength, "Formal");
            assert!(proof.source_bound_obligation.is_some());
        }
        assert!(!proofs.iter().any(|proof| {
            proof
                .rule_name
                .starts_with("Source-bound AArch64 leaf: FP/LR frame")
        }));
        #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
        {
            let dir = tempfile::tempdir().unwrap();
            let object = dir.path().join("leaf.o");
            let caller = dir.path().join("caller.c");
            let binary = dir.path().join("caller");
            std::fs::write(&object, &checked.object_code).unwrap();
            std::fs::write(&caller, format!(r#"extern unsigned long long leaf(unsigned long long) __asm__("_{name}");
int main(void) {{ const unsigned long long values[] = {{0,1,0x7fffffffffffffffULL,0x8000000000000000ULL,~0ULL}};
for (unsigned i=0;i<5;i++) if(leaf(values[i])!=values[i]) return 1; return 0; }}
"#)).unwrap();
            let linked = std::process::Command::new("cc")
                .arg("-O2")
                .arg(&caller)
                .arg(&object)
                .arg("-o")
                .arg(&binary)
                .output()
                .unwrap();
            assert!(
                linked.status.success(),
                "{}",
                String::from_utf8_lossy(&linked.stderr)
            );
            assert!(
                std::process::Command::new(&binary)
                    .status()
                    .unwrap()
                    .success()
            );
            println!("FRAMELESS_BLACK_BOX_NATIVE {level:?} calls=5 exit=0");
        }
    }
}

#[test]
fn captured_frameless_branch_cannot_promote_without_independent_replay() {
    let module = trust_ir::binary::deserialize_module(include_bytes!(
        "fixtures/aarch64_framed_identity/black_box.trust_irbin"
    ))
    .unwrap();
    trust_cg_verify::env_lock::with_env_overrides(&[("TCG_REFINE_SOLVER", "0")], || {
        let error = Compiler::new_for_target_spec(
            CompilerConfig {
                opt_level: OptLevel::O0,
                emit_proofs: true,
                parallel: false,
                eh_frames_cannot_unwind: true,
                ..Default::default()
            },
            TargetSpec::parse("aarch64-apple-darwin").unwrap(),
        )
        .with_codegen_license(
            trust_cg_lower::CodegenLicensePolicy::default()
                .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit),
        )
        .compile(&module)
        .expect_err("a real emitted B still needs independent next-PC replay");
        assert!(matches!(
            error,
            trust_cg_codegen::CompileError::ProofPromotionRejected { .. }
        ));
        assert!(
            error
                .to_string()
                .contains("source-bound frameless control needs independently replayed proof"),
            "{error}"
        );
    });
}

#[test]
fn default_linear_leaf_proofs_are_frameless_and_serial_parallel_identical() {
    use trust_ir::Ty;
    use trust_ir_build::ModuleBuilder;
    let mut mb = ModuleBuilder::new("frameless_linear_determinism");
    for index in 0..20 {
        let ty = if index % 2 == 0 { Ty::I32 } else { Ty::I64 };
        let signature = mb.add_func_type(vec![ty.clone(); 2], vec![ty.clone()]);
        let mut fb = mb.function(format!("linear_{index}"), signature);
        let entry = fb.create_block();
        let exit = fb.create_block();
        let a = fb.add_block_param(entry, ty.clone());
        let b = fb.add_block_param(entry, ty.clone());
        fb.switch_to_block(entry);
        let result = if index / 2 % 2 == 0 {
            a
        } else {
            fb.add(ty, a, b)
        };
        fb.br(exit, vec![]);
        fb.switch_to_block(exit);
        fb.ret(vec![result]);
        fb.build();
    }
    let module = mb.build().unwrap();
    for triple in ["aarch64-apple-darwin", "aarch64-unknown-linux-gnu"] {
        let compile = |parallel| {
            Compiler::new_for_target_spec(
                CompilerConfig {
                    opt_level: OptLevel::O0,
                    emit_proofs: true,
                    parallel,
                    eh_frames_cannot_unwind: true,
                    ..Default::default()
                },
                TargetSpec::parse(triple).unwrap(),
            )
            .with_codegen_license(
                trust_cg_lower::CodegenLicensePolicy::default()
                    .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit),
            )
            .compile(&module)
            .unwrap()
        };
        let serial = compile(false);
        let parallel = compile(true);
        assert_eq!(serial.object_code, parallel.object_code, "{triple}");
        assert_eq!(serial.proofs, parallel.proofs, "{triple}");
        let functions = function_words::function_words(&serial.object_code);
        assert_eq!(functions.len(), 20);
        let proofs = serial.proofs.as_ref().unwrap();
        assert!(proofs.iter().all(|proof| proof.verified));
        assert!(!proofs.iter().any(|proof| {
            proof
                .rule_name
                .starts_with("Source-bound AArch64 leaf: FP/LR frame")
        }));
        for (name, words) in functions {
            assert!(
                !words
                    .iter()
                    .any(|word| [0xa9bf7bfd, 0x910003fd, 0xa8c17bfd].contains(word)),
                "{triple}/{name}: {words:x?}"
            );
            assert!(proofs.iter().any(|proof| proof.function_name == name));
            for payload in proofs
                .iter()
                .filter(|proof| proof.function_name == name)
                .filter_map(|proof| proof.source_bound_obligation.as_ref())
            {
                assert_eq!(payload.function_name(), name);
            }
        }
        println!("FRAMELESS_LINEAR_DETERMINISM {triple} functions=20 serial_parallel=identical");
    }
}

#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
#[test]
fn direct_identity_and_add_leaves_publish_and_execute_without_jit_frames() {
    use trust_ir::Ty;
    use trust_ir_build::ModuleBuilder;
    for add in [false, true] {
        let mut mb = ModuleBuilder::new("direct_frameless_jit");
        let signature = mb.add_func_type(vec![Ty::I64; 2], vec![Ty::I64]);
        let mut fb = mb.function("leaf", signature);
        let entry = fb.create_block();
        let a = fb.add_block_param(entry, Ty::I64);
        let b = fb.add_block_param(entry, Ty::I64);
        fb.switch_to_block(entry);
        let result = if add { fb.add(Ty::I64, a, b) } else { a };
        fb.ret(vec![result]);
        fb.build();
        let module = mb.build().unwrap();
        let compiled = Compiler::new(CompilerConfig {
            emit_proofs: true,
            opt_level: OptLevel::O0,
            ..Default::default()
        })
        .with_codegen_license(
            trust_cg_lower::CodegenLicensePolicy::default()
                .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit),
        )
        .compile_module_to_jit(&module, &std::collections::HashMap::new())
        .expect("a direct source leaf needs neither a call contract nor a manufactured frame");
        assert_eq!(compiled.per_function_metrics.len(), 1);
        let bytes = compiled.per_function_metrics[0].code_size_bytes;
        let (words, trailing) = compiled.buffer.code_slice()[..bytes].as_chunks::<4>();
        assert!(trailing.is_empty(), "partial instruction word");
        let words: Vec<_> = words.iter().copied().map(u32::from_le_bytes).collect();
        assert!(
            !words
                .iter()
                .any(|word| [0xa9bf7bfd, 0x910003fd, 0xa8c17bfd].contains(word)),
            "{words:x?}"
        );
        assert_eq!(words.last(), Some(&0xd65f03c0));
        assert!(
            compiled
                .proofs
                .as_ref()
                .unwrap()
                .iter()
                .all(|proof| proof.verified)
        );
        let certificate = compiled.buffer.certificate("leaf").unwrap();
        assert!(certificate.has_checked_semantics());
        assert!(
            compiled
                .validation
                .as_ref()
                .unwrap()
                .every_function_semantics_verified()
        );
        assert!(compiled.buffer.all_function_semantics_verified());

        assert_eq!(certificate.is_verified(), add);
        assert!(
            certificate
                .to_json()
                .contains(&format!("\"source_checked_structural_return\": {}", !add))
        );
        compiled.buffer.verify_published_code_integrity().unwrap();
        let pointer = compiled.buffer.get_fn_ptr_bound("leaf").unwrap();
        // The constructed C ABI signature is exactly (u64,u64)->u64 and the
        // lifetime-bound executable buffer stays alive through every call.
        let call: unsafe extern "C" fn(u64, u64) -> u64 =
            unsafe { std::mem::transmute(pointer.as_ptr()) };
        for (a, b) in [
            (0, 0),
            (1, 2),
            (u64::MAX, 1),
            (1 << 63, 1 << 63),
            (0x12345678, 0x9abcdef0),
        ] {
            assert_eq!(
                unsafe { call(a, b) },
                if add { a.wrapping_add(b) } else { a }
            );
        }
        println!("FRAMELESS_JIT add={add} words={words:x?} calls=5 exit=0");
    }
}

/// A branch proof cannot supply value credit for an unrelated dead ADD. These
/// shapes must continue refusing rather than turning source equality into an
/// instruction-proof waiver (including a void return).
#[test]
fn frameless_control_does_not_credit_dead_value_instructions() {
    use trust_ir::Ty;
    use trust_ir_build::ModuleBuilder;
    for ty in [Ty::I32, Ty::I64] {
        for returns_value in [false, true] {
            let mut mb = ModuleBuilder::new("dead_value_refusal");
            let signature = mb.add_func_type(
                vec![ty.clone(); 2],
                if returns_value {
                    vec![ty.clone()]
                } else {
                    vec![]
                },
            );
            let mut fb = mb.function("dead_add", signature);
            let entry = fb.create_block();
            let exit = fb.create_block();
            let a = fb.add_block_param(entry, ty.clone());
            let b = fb.add_block_param(entry, ty.clone());
            fb.switch_to_block(entry);
            let _dead = fb.add(ty.clone(), a, b);
            fb.br(exit, vec![]);
            fb.switch_to_block(exit);
            fb.ret(if returns_value { vec![a] } else { vec![] });
            fb.build();
            let module = mb.build().unwrap();
            for triple in ["aarch64-apple-darwin", "aarch64-unknown-linux-gnu"] {
                let reject = |parallel| {
                    Compiler::new_for_target_spec(
                        CompilerConfig {
                            opt_level: OptLevel::O0,
                            emit_proofs: true,
                            parallel,
                            eh_frames_cannot_unwind: true,
                            ..Default::default()
                        },
                        TargetSpec::parse(triple).unwrap(),
                    )
                    .with_codegen_license(
                        trust_cg_lower::CodegenLicensePolicy::default()
                            .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit),
                    )
                    .compile(&module)
                    .unwrap_err()
                    .to_string()
                };
                let serial = reject(false);
                assert!(serial.contains("AArch64::AddRR"), "{serial}");
                assert_eq!(serial, reject(true));
            }
        }
    }
}
