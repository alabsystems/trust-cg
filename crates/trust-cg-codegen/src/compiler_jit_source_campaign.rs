//! Opt-in real-tool native campaign. A printed SKIP is not qualification.
//! Require both positive markers and exact native-call/cache counters.
//!
//! The final test runs by default on AArch64: the campaign's stale-source and
//! raw-None negatives over an exhaustively checked `zext i8 -> i32`, which
//! needs no external certificate (only the discovered verification authority
//! that outer-cache identity requires).

use super::*;
use crate::jit::{JitCompiler, ProfileHookMode};
use crate::jit_cert::{
    JitCertCache, aarch64_verifier_input_digest_with_lir,
    aarch64_verifier_input_digest_with_modules,
};
use sha2::{Digest, Sha256};
use std::io::Read;
use std::os::unix::fs::{PermissionsExt, symlink};
use std::path::{Path, PathBuf};
use std::sync::Arc;
use trust_cg_lower::{Function, ProofContext};
use trust_ir_build::ModuleBuilder;

const TOOL_INPUTS: [(&str, &str, &str); 2] = [
    (
        "ay",
        "TCG_JIT_REQUEST_CACHE_AY",
        "TCG_JIT_REQUEST_CACHE_AY_SHA256",
    ),
    (
        "clean",
        "TCG_JIT_REQUEST_CACHE_CLEAN",
        "TCG_JIT_REQUEST_CACHE_CLEAN_SHA256",
    ),
];

fn file_digest(path: &Path) -> String {
    let mut file = std::fs::File::open(path).expect("open exact campaign tool");
    let mut hash = Sha256::new();
    let mut chunk = [0u8; 64 * 1024];
    loop {
        let count = file.read(&mut chunk).expect("read exact campaign tool");
        if count == 0 {
            break;
        }
        hash.update(&chunk[..count]);
    }
    format!("{:x}", hash.finalize())
}

fn with_real_tools(run: impl FnOnce()) {
    // Host gate, constant by design: `cfg!` fixes the compile target, so clippy sees a
    // constant where the campaign needs a runtime refusal (a const block would fail the build).
    #[allow(clippy::assertions_on_constants)]
    {
        assert!(
            cfg!(all(
                target_arch = "aarch64",
                any(target_os = "macos", target_os = "linux")
            )),
            "requested campaign requires native AArch64 Mac/Linux, never emulation"
        );
    }
    let directory = tempfile::Builder::new()
        .prefix("trust-cg-jit-source-")
        .tempdir()
        .unwrap();
    let prefix = directory.path().join("packages");
    std::fs::create_dir_all(prefix.join("bin")).unwrap();
    let mut tools = Vec::new();
    for (name, path_key, hash_key) in TOOL_INPUTS {
        let path = PathBuf::from(std::env::var_os(path_key).expect(path_key))
            .canonicalize()
            .expect("exact campaign tool must exist");
        let expected = std::env::var(hash_key).expect(hash_key);
        assert!(
            expected.len() == 64
                && expected
                    .bytes()
                    .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
        );
        let metadata = path.metadata().unwrap();
        assert!(metadata.is_file(), "{name} tool must be a regular file");
        assert_ne!(metadata.permissions().mode() & 0o111, 0);
        assert_eq!(file_digest(&path), expected, "{name} tool bytes");
        // AY is never discovered from a package store: the verifier admits only
        // its toolchain's identity-checked `bin/ay` (trust_cg_verify::ay_identity).
        // The campaign's AY input must therefore BE that binary's bytes.
        if name != "ay" {
            let package = prefix.join("store").join(name).join("current/bin");
            std::fs::create_dir_all(&package).unwrap();
            symlink(&path, package.join(name)).unwrap();
        }
        tools.push((path, expected));
    }
    let pinned_ay = trust_cg_verify::ay_identity::resolve_for_process()
        .unwrap_or_else(|refusal| panic!("the campaign requires the toolchain AY: {refusal}"));
    assert_eq!(
        file_digest(pinned_ay.path()),
        tools[0].1,
        "the campaign AY input must be the toolchain's admitted AY ({})",
        pinned_ay.describe()
    );
    let path = std::env::join_paths(std::iter::once(prefix.join("bin")).chain(
        std::env::split_paths(&std::env::var_os("PATH").unwrap_or_default()),
    ))
    .unwrap();
    trust_cg_process_env::with_env_edits(|env| {
        env.set("PATH", path);
        env.set("TCG_BLOCKING_IDENTITY", "1");
        env.set(
            "TCG_PROOF_CERT_STORE",
            directory.path().join("certificates"),
        );
        env.set("TCG_PROOF_CACHE_DIR", directory.path().join("proof-cache"));
        for key in [
            "AY_SOLVER_PATH",
            "TCG_EXTERNAL_CLEAN_CHECKER",
            "TCG_CLEAN_CHECKER",
            "TCG_NO_VERDICT_DB",
            "TCG_NO_PROOF_CACHE",
            "TCG_NO_SOLVER_SERVER",
            "TCG_PRECISE_CITATIONS",
            "TCG_NO_JIT_CERT_CACHE",
            "TCG_PROVENANCE_XCHECK",
            "TCG_CANARY_NO_CACHE",
            "TCG_NO_CERT_STORE",
            "TCG_REFINE_SOLVER",
            "TCG_RECON_SOLVER_MS",
            "TRUST_CG_AY_TIMEOUT_MS",
            "TCG_JIT_UNCHECKED",
            "TCG_JIT_VERIFY",
        ] {
            env.remove(key);
        }
        for (_, path_key, hash_key) in TOOL_INPUTS {
            env.remove(path_key);
            env.remove(hash_key);
        }
        assert!(!crate::jit_cert::deep_verifier_override_disables_outer_cache());
        let verifier = shared_aarch64_function_verifier();
        let mode = trust_cg_verify::provenance_xcheck::ProvenanceXCheckMode::Enforce;
        let discovered = verifier
            .capture_request_with_mode(mode)
            .reuse_identity()
            .expect("real discovered proof tools must have reusable authority");
        let explicit = trust_cg_process_env::with_env_edits(|reference| {
            reference.set("AY_SOLVER_PATH", pinned_ay.path());
            reference.set("TCG_EXTERNAL_CLEAN_CHECKER", &tools[1].0);
            verifier.capture_request_with_mode(mode).reuse_identity()
        });
        assert_eq!(
            explicit,
            Some(discovered),
            "discovery must select the exact hashed tools"
        );
        assert!(!crate::jit_cert::deep_verifier_override_disables_outer_cache());
        run();
    });
    for (path, expected) in tools {
        assert_eq!(file_digest(&path), expected);
    }
}

fn source_module() -> trust_ir::Module {
    let mut builder = ModuleBuilder::new("jit_source_campaign");
    let constant_ty = builder.add_func_type(vec![], vec![trust_ir::Ty::I64]);
    let identity_ty = builder.add_func_type(vec![trust_ir::Ty::I64], vec![trust_ir::Ty::I64]);
    let mut function = builder.function("answer", constant_ty);
    let entry = function.create_block();
    function.switch_to_block(entry);
    let value = function.iconst(trust_ir::Ty::I64, 42);
    function.ret(vec![value]);
    function.build();
    let mut function = builder.function("identity", identity_ty);
    let entry = function.create_block();
    let value = function.add_block_param(entry, trust_ir::Ty::I64);
    function.switch_to_block(entry);
    function.ret(vec![value]);
    function.build();
    builder.build().expect("ModuleBuilder::build: test fixture")
}

/// Independently reconstruct the exact ordinary preparation inputs. Equality
/// with the high-level result is asserted, never assumed as a cache authority.
fn preparation(
    compiler: &Compiler,
    module: &trust_ir::Module,
) -> (
    Vec<(Function, ProofContext)>,
    Vec<trust_cg_ir::MachFunction>,
) {
    let tls =
        if crate::pipeline::target_triple_uses_elf(&compiler_target_triple(compiler.target_spec)) {
            trust_cg_lower::TlsDialect::ElfLocalExec
        } else {
            trust_cg_lower::TlsDialect::MachOTlv
        };
    let (sources, replay) =
        trust_cg_lower::translate_module_for_arch_with_tls_and_validation_with_license(
            module,
            guard_carrier_arch_for_target(Target::Aarch64),
            tls,
            &compiler.codegen_license,
        )
        .unwrap();
    replay.replay_exact_module_bindings(&sources).unwrap();
    let pipeline = compiler.build_pipeline(compiler.effective_aarch64_jit_isa_profile());
    let machines = sources
        .iter()
        .zip(&module.functions)
        .map(|((lir, proofs), function)| {
            pipeline
                .prepare_function_with_metrics_and_trust_ir_module(
                    lir,
                    Some(proofs),
                    module,
                    function,
                )
                .unwrap()
                .0
        })
        .collect::<Vec<_>>();
    assert_eq!(sources.len(), 2);
    assert_eq!(machines.len(), 2);
    (sources, machines)
}

fn check_result(
    module: &trust_ir::Module,
    result: &JitCompilationResult,
    mode: JitValidationMode,
    hit: bool,
    sources: &[(Function, ProofContext)],
    machines: &[trust_cg_ir::MachFunction],
) {
    let validation = result
        .validation
        .as_ref()
        .expect("actual JIT validation required");
    assert_eq!(validation.mode, mode);
    assert!(validation.every_function_semantics_verified());
    assert_eq!(validation.functions.len(), 2);
    assert_eq!(validation.cache_hits(), if hit { 1 } else { 0 });
    assert_eq!(
        validation.published_image_sha256,
        format!("{:x}", Sha256::digest(result.buffer.code_slice()))
    );
    assert_eq!(
        validation.published_image_sha256,
        result.buffer.published_image_sha256()
    );
    for (machine, (source, _)) in machines.iter().zip(sources) {
        let certificate = result
            .buffer
            .certificate(&source.name)
            .expect("real certificate");
        assert!(certificate.has_checked_semantics() && certificate.replay_check());
        assert_eq!(certificate.is_verified(), source.name != "identity");
        assert_eq!(
            certificate.served_from_cache(),
            hit && source.name != "identity"
        );
        assert!(
            certificate.lowering_certificate().is_none(),
            "do not invent an exported lowering proof"
        );
        let expected = crate::jit_cert::digest_hex(
            &aarch64_verifier_input_digest_with_modules(
                machine,
                Some(source),
                &trust_cg_verify::FunctionSourceModules::capture(module, module).unwrap(),
            )
            .unwrap(),
        );
        assert_eq!(certificate.verifier_input_sha256(), expected);
        assert_ne!(
            expected,
            crate::jit_cert::digest_hex(
                &aarch64_verifier_input_digest_with_lir(machine, None).unwrap()
            )
        );
        let range = certificate.code_range();
        let bytes = &result.buffer.code_slice()[range.start as usize..range.end as usize];
        let bytes_hash = format!("{:x}", Sha256::digest(bytes));
        assert_eq!(
            certificate.normalized_machine_code_sha256(),
            bytes_hash,
            "these leaf fixtures have no relocations, profiling prefix, or external binding"
        );
        let row = validation
            .functions
            .iter()
            .find(|row| row.function == source.name)
            .unwrap();
        assert_eq!(row.verifier_input_sha256, expected);
        assert_eq!(row.bytes_sha256, bytes_hash);
        let frame = certificate
            .chain()
            .certificates
            .iter()
            .filter(|proof| {
                proof.obligation_name == trust_cg_verify::source_bound_frame::FRAME_OBLIGATION_NAME
            })
            .collect::<Vec<_>>();
        assert!(
            frame.is_empty(),
            "default leaves must not gain proof-only frames"
        );
    }
}

fn call_native(result: &JitCompilationResult) -> usize {
    // SAFETY: the source module above fixes these exact native C signatures.
    // Compilation and all proof/byte checks succeeded; the owning executable
    // buffer outlives both borrowed callable handles and all calls. This is
    // finite ABI evidence, not a product manifest/installed-artifact claim.
    let answer = unsafe {
        result
            .buffer
            .get_fn_bound::<extern "C" fn() -> i64>("answer")
    }
    .unwrap();
    let identity = unsafe {
        result
            .buffer
            .get_fn_bound::<extern "C" fn(i64) -> i64>("identity")
    }
    .unwrap();
    assert_eq!((answer.as_ref())(), 42);
    let inputs = [i64::MIN, i64::MIN + 1, -42, -1, 0, 1, 42, i64::MAX];
    for value in inputs {
        assert_eq!((identity.as_ref())(value), value);
    }
    1 + inputs.len()
}

fn run_campaign(mode: JitValidationMode) {
    let module = source_module();
    let cache = Arc::new(JitCertCache::new());
    let compiler = Compiler::new(CompilerConfig {
        opt_level: OptLevel::O0,
        emit_proofs: false,
        parallel: false,
        jit_validation_mode_override: Some(mode),
        ..CompilerConfig::jit_fast(Target::Aarch64)
    })
    .with_codegen_license(permit_unlicensed())
    .with_jit_cert_cache(Arc::clone(&cache));
    let (sources, machines) = preparation(&compiler, &module);
    let cold = compiler
        .compile_module_to_jit(&module, &HashMap::new())
        .unwrap_or_else(|error| {
            panic!("required {mode:?} source-bound native cold compile refused: {error}")
        });
    check_result(&module, &cold, mode, false, &sources, &machines);
    let mut native_calls = call_native(&cold);
    assert_eq!(
        cache.stats(),
        if mode == JitValidationMode::CachedVerified {
            (0, 2, 0, 2)
        } else {
            (0, 0, 0, 2)
        }
    );
    let warm = compiler
        .compile_module_to_jit(&module, &HashMap::new())
        .unwrap_or_else(|error| {
            panic!("required {mode:?} source-bound native repeat refused: {error}")
        });
    check_result(
        &module,
        &warm,
        mode,
        mode == JitValidationMode::CachedVerified,
        &sources,
        &machines,
    );
    assert_eq!(cold.buffer.code_slice(), warm.buffer.code_slice());
    drop(cold);
    native_calls += call_native(&warm);
    assert_eq!(native_calls, 18);
    assert_eq!(
        cache.stats(),
        if mode == JitValidationMode::CachedVerified {
            (1, 3, 0, 3)
        } else {
            (0, 0, 0, 4)
        }
    );
    let positive_stats = cache.stats();
    if mode == JitValidationMode::CachedVerified {
        // Same prepared machine/bytes and policy, but an incompatible LIR
        // constant. An old source-bound receipt must not satisfy this request.
        let mut changed = sources.clone();
        let constant = changed[0]
            .0
            .blocks
            .values_mut()
            .flat_map(|b| &mut b.instructions)
            .find(|i| {
                matches!(
                    i.opcode,
                    trust_cg_lower::instructions::Opcode::Iconst { .. }
                )
            })
            .unwrap();
        let trust_cg_lower::instructions::Opcode::Iconst { imm, .. } = &mut constant.opcode else {
            unreachable!()
        };
        *imm = 43;
        let jit_config = compiler
            .config
            .to_jit_config_with_validation_mode(ProfileHookMode::None, mode)
            .unwrap();
        let jit = JitCompiler::new_with_aarch64_isa_profile(
            jit_config,
            compiler.effective_aarch64_jit_isa_profile(),
        )
        .with_certificate_cache(Arc::clone(&cache));
        let (stale, _) = jit
            .compile_with_lir_and_encoding_metrics(
                &machines,
                &changed,
                &module,
                &module,
                &HashMap::new(),
                false,
                None,
            )
            .unwrap();
        assert!(!stale.certificate("answer").unwrap().is_verified());
        assert!(!stale.certificate("answer").unwrap().served_from_cache());
        assert!(
            stale
                .certificate("identity")
                .unwrap()
                .has_checked_semantics()
        );
        assert!(!stale.certificate("identity").unwrap().served_from_cache());
        assert_eq!(cache.stats(), (1, 5, 0, 5));
        // Raw None retains its independent diagnostic policy, not the typed
        // source credit. Never invoke either unverified diagnostic buffer.
        let raw = jit.compile_raw(&machines, &HashMap::new()).unwrap();
        for name in ["answer", "identity"] {
            assert!(!raw.certificate(name).unwrap().is_verified());
            assert!(!raw.certificate(name).unwrap().served_from_cache());
        }
        assert_eq!(cache.stats(), (1, 7, 0, 7));
        println!(
            "JIT_SOURCE_CACHE_NEGATIVES stale_source=1 raw_none=2 native_calls=0 cumulative_cache_hits={} cumulative_verifier_runs={}",
            cache.stats().0,
            cache.stats().3
        );
        // Same prepared machine/LIR, but a different original module. An
        // accurate readnone annotation changes custody identity without
        // changing these constant/identity functions' machine behavior.
        let mut changed_module = module.clone();
        changed_module.functions[0].attrs.readnone = true;
        for (original, expected_hit, expected_stats) in [
            (&changed_module, false, (1, 9, 0, 9)),
            (&changed_module, true, (2, 10, 0, 10)),
            (&module, true, (3, 11, 0, 11)),
        ] {
            let (rebound, _) = jit
                .compile_with_lir_and_encoding_metrics(
                    &machines,
                    &sources,
                    original,
                    &module,
                    &HashMap::new(),
                    false,
                    None,
                )
                .unwrap();
            for name in ["answer", "identity"] {
                let certificate = rebound.certificate(name).unwrap();
                assert!(certificate.has_checked_semantics() && certificate.replay_check());
                assert_eq!(certificate.is_verified(), name != "identity");
                assert_eq!(
                    certificate.served_from_cache(),
                    expected_hit && name != "identity"
                );
            }
            assert_eq!(cache.stats(), expected_stats);
        }
        println!(
            "JIT_SOURCE_MODULE_CACHE_BOUND changed_original_misses=2 unchanged_hits=1 restored_original_hits=1 structural_return_rechecks=3 native_calls=0"
        );
    }
    println!(
        "JIT_SOURCE_NATIVE_ACCEPTED mode={mode:?} functions=2 compiles=2 native_calls={native_calls} positive_cache_hits={} positive_verifier_runs={}",
        positive_stats.0, positive_stats.3
    );
}

fn campaign(mode: JitValidationMode) {
    if std::env::var("TRUST_CG_RUN_EXTERNAL_CERT_TESTS").as_deref() != Ok("1") {
        eprintln!(
            "SKIP JIT_SOURCE_NATIVE {mode:?}: external certificate campaign not requested; no proof/native/cache qualification"
        );
        return;
    }
    with_real_tools(|| run_campaign(mode));
}

#[test]
fn high_level_source_bound_always_verify_native_campaign() {
    campaign(JitValidationMode::AlwaysVerify);
}

#[test]
fn high_level_source_bound_cached_verify_native_campaign() {
    campaign(JitValidationMode::CachedVerified);
}

/// One-function `zext i8 -> i32` source, whose obligation is exhaustive.
#[cfg(target_arch = "aarch64")]
fn exhaustive_module() -> trust_ir::Module {
    let mut builder = ModuleBuilder::new("jit_source_exhaustive_controls");
    let signature = builder.add_func_type(vec![trust_ir::Ty::I8], vec![trust_ir::Ty::I32]);
    let mut function = builder.function("widen", signature);
    let entry = function.create_block();
    let value = function.add_block_param(entry, trust_ir::Ty::I8);
    function.switch_to_block(entry);
    let widened = function.zext(trust_ir::Ty::I8, trust_ir::Ty::I32, value);
    function.ret(vec![widened]);
    function.build();
    builder.build().expect("ModuleBuilder::build: test fixture")
}

/// The private-continuation stale-source and raw-None negatives of the
/// campaign above, on a function whose only obligation is exhaustive, so they
/// need no external certificate and run by default. Discovered AY/Clean
/// verification authority is still required for outer-cache identity; its
/// absence fails this test.
#[cfg(target_arch = "aarch64")]
#[test]
fn exhaustive_stale_source_and_raw_none_never_reuse_a_source_bound_verdict() {
    trust_cg_process_env::with_env_edits(|env| {
        env.set("TCG_BLOCKING_IDENTITY", "1");
        for key in [
            "AY_SOLVER_PATH",
            "TCG_EXTERNAL_CLEAN_CHECKER",
            "TCG_CLEAN_CHECKER",
            "TCG_NO_VERDICT_DB",
            "TCG_NO_PROOF_CACHE",
            "TCG_NO_SOLVER_SERVER",
            "TCG_PRECISE_CITATIONS",
            "TCG_NO_JIT_CERT_CACHE",
            "TCG_PROVENANCE_XCHECK",
            "TCG_JIT_UNCHECKED",
            "TCG_JIT_VERIFY",
        ] {
            env.remove(key);
        }
        assert!(
            trust_cg_verify::jit_verification_authority_id_if_ready().is_some(),
            "outer-cache controls require the discovered verification authority"
        );
        let module = exhaustive_module();
        let mode = JitValidationMode::CachedVerified;
        let cache = Arc::new(JitCertCache::new());
        let compiler = Compiler::new(CompilerConfig {
            opt_level: OptLevel::O1,
            emit_proofs: false,
            parallel: false,
            jit_validation_mode_override: Some(mode),
            ..CompilerConfig::jit_fast(Target::Aarch64)
        })
        .with_codegen_license(permit_unlicensed())
        .with_jit_cert_cache(Arc::clone(&cache));
        let tls = if crate::pipeline::target_triple_uses_elf(&compiler_target_triple(
            compiler.target_spec,
        )) {
            trust_cg_lower::TlsDialect::ElfLocalExec
        } else {
            trust_cg_lower::TlsDialect::MachOTlv
        };
        let (sources, replay) =
            trust_cg_lower::translate_module_for_arch_with_tls_and_validation_with_license(
                &module,
                guard_carrier_arch_for_target(Target::Aarch64),
                tls,
                &compiler.codegen_license,
            )
            .unwrap();
        replay.replay_exact_module_bindings(&sources).unwrap();
        let pipeline = compiler.build_pipeline(compiler.effective_aarch64_jit_isa_profile());
        let machines = vec![
            pipeline
                .prepare_function_with_metrics_and_trust_ir_module(
                    &sources[0].0,
                    Some(&sources[0].1),
                    &module,
                    &module.functions[0],
                )
                .unwrap()
                .0,
        ];

        let cold = compiler
            .compile_module_to_jit(&module, &HashMap::new())
            .expect("the exhaustive source-bound compile certifies");
        let certificate = cold.buffer.certificate("widen").unwrap();
        assert!(certificate.is_verified() && !certificate.served_from_cache());
        assert_eq!(
            certificate.verifier_input_sha256(),
            crate::jit_cert::digest_hex(
                &aarch64_verifier_input_digest_with_modules(
                    &machines[0],
                    Some(&sources[0].0),
                    &trust_cg_verify::FunctionSourceModules::capture(&module, &module).unwrap(),
                )
                .unwrap()
            ),
            "the independent preparation reproduces the certified (source-module-bound) input"
        );
        assert_eq!(cache.stats(), (0, 1, 0, 1));

        let jit_config = compiler
            .config
            .to_jit_config_with_validation_mode(ProfileHookMode::None, mode)
            .unwrap();
        let jit = JitCompiler::new_with_aarch64_isa_profile(
            jit_config,
            compiler.effective_aarch64_jit_isa_profile(),
        )
        .with_certificate_cache(Arc::clone(&cache));
        // The unchanged source through the private continuation is the
        // positive control that this is one shared cache.
        let (same, _) = jit
            .compile_with_lir_and_encoding_metrics(
                &machines,
                &sources,
                &module,
                &module,
                &HashMap::new(),
                false,
                None,
            )
            .unwrap();
        assert!(same.certificate("widen").unwrap().served_from_cache());
        assert_eq!(cache.stats(), (1, 1, 0, 1));

        // Stale source: identical machine bytes, but the LIR now claims a
        // sign extension. The stored verdict must not be served and the new
        // request must not verify.
        let mut stale_sources = sources.clone();
        let extension = stale_sources[0]
            .0
            .blocks
            .values_mut()
            .flat_map(|block| &mut block.instructions)
            .find(|instruction| {
                matches!(
                    instruction.opcode,
                    trust_cg_lower::instructions::Opcode::Uextend { .. }
                )
            })
            .expect("the source holds one zero extension");
        let trust_cg_lower::instructions::Opcode::Uextend { from_ty, to_ty } =
            extension.opcode.clone()
        else {
            unreachable!()
        };
        extension.opcode = trust_cg_lower::instructions::Opcode::Sextend { from_ty, to_ty };
        let (stale, _) = jit
            .compile_with_lir_and_encoding_metrics(
                &machines,
                &stale_sources,
                &module,
                &module,
                &HashMap::new(),
                false,
                None,
            )
            .unwrap();
        let stale_certificate = stale.certificate("widen").unwrap();
        assert!(!stale_certificate.is_verified());
        assert!(!stale_certificate.served_from_cache());
        assert_eq!(stale.code_slice(), cold.buffer.code_slice());
        assert_eq!(cache.stats(), (1, 2, 0, 2));

        // Raw None: the same bytes without source never reuse the
        // source-bound verdict.
        let raw = jit.compile_raw(&machines, &HashMap::new()).unwrap();
        assert!(!raw.certificate("widen").unwrap().served_from_cache());
        assert_eq!(cache.stats(), (1, 3, 0, 3));
        println!(
            "JIT_SOURCE_EXHAUSTIVE_NEGATIVES stale_source=1 raw_none=1 positive_hits=1 verifier_runs={}",
            cache.stats().3
        );
    });
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> crate::CodegenLicensePolicy {
    crate::CodegenLicensePolicy::default().with_unlicensed(crate::UnlicensedBodyPolicy::Permit)
}
