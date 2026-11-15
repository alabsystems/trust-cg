// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
//! Captured narrow-return source/body binding and proof-required compilation.
//! The core checks run on every host; native Mach-O execution is arm64 Mac only.
#![cfg(feature = "verify")]

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::TargetSpec;
use trust_cg_ir::InstId;
use trust_cg_verify::source_bound_a64_body::{
    A64_BODY_NEEDS_REPLAY, diagnostic_a64_body_obligation, source_bound_a64_body,
};
#[path = "common/source_bound_body_cases.rs"]
mod cases;
#[path = "common/function_words.rs"]
mod function_words;
use cases::{PREPS, on_big_stack, prepare_as};

/// Original captured zero-return leaf: the adapter keeps an I8 signature and
/// returns an I32 zero-extension carrier. It must reach a source-bound body
/// obligation, while withdrawing replay must still prevent proof promotion.
#[test]
fn captured_narrow_termination_leaf_requires_its_own_body_replay() {
    use trust_cg_verify::function_verifier::InstructionVerificationResult as R;
    use trust_cg_verify::provenance_xcheck::ProvenanceXCheckMode;
    use trust_cg_verify::{FunctionVerifier, VerificationConfig};
    on_big_stack(|| {
        let source = cases::captured_narrow_leaf();
        assert_eq!(source.signature.returns, vec![trust_cg_lower::Type::I8]);
        trust_cg_verify::env_lock::with_env_overrides(&[("TCG_REFINE_SOLVER", "0")], || {
            for prep in PREPS {
                for level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
                    let machine = prepare_as(prep, &source, level);
                    let owner = source_bound_a64_body(&source, &machine).unwrap();
                    assert!(
                        !owner.covered().is_empty() || !owner.copies_and_constants().is_empty()
                    );
                    assert!(!owner.copies_and_constants().is_empty());
                    assert!(!owner.obligation().is_degenerate());
                    let verifier =
                        FunctionVerifier::with_config(VerificationConfig::for_proof_promotion());
                    let request = verifier.capture_request_with_mode(ProvenanceXCheckMode::Enforce);
                    let (captured, exported) =
                        verifier.verify_with_request_for_export(&machine, Some(&source), &request);
                    let report = captured.report();
                    assert!(report.precondition_failure.is_none(), "{report:?}");
                    assert!(exported.is_empty());
                    assert_eq!(
                        report
                            .instructions
                            .iter()
                            .filter(|row| owner.covers(InstId(row.inst_index as u32)))
                            .count(),
                        owner.covered().len() + owner.copies_and_constants().len(),
                        "every bound row must actually appear in the refusal report",
                    );
                    for row in &report.instructions {
                        if owner.covers(InstId(row.inst_index as u32)) {
                            assert!(
                                matches!(&row.result, R::Unverified { reason }
                            if reason.starts_with(A64_BODY_NEEDS_REPLAY)),
                                "{row:?}"
                            );
                        }
                    }
                    assert!(!report.emitted_opcode_inventory().is_promotable());
                }
            }
        });
    });
}

/// Independently checked body proofs, corrupt-immediate counterexamples,
/// proof-required production object emission, and a native caller on arm64 Mac.
#[test]
fn captured_narrow_leaf_compiles_with_checked_proofs() {
    use trust_cg_verify::ay_bridge::{AYConfig, AYResult, verify_with_cli_raw_attributed};
    on_big_stack(|| {
        trust_cg_verify::env_lock::with_env_overrides(&[], || {
            if let Some(reason) = trust_cg_verify::ay_bridge::proof_toolchain_unavailable_reason() {
                panic!("PROOF_TOOLS_MISSING: {reason}");
            }
            let source = cases::captured_narrow_leaf();
            for prep in PREPS {
                let machine = prepare_as(prep, &source, trust_cg_codegen::pipeline::OptLevel::O0);
                let owner = source_bound_a64_body(&source, &machine).unwrap();
                let config = AYConfig::default();
                let query = trust_cg_verify::ay_bridge::generate_smt2_query_raw(
                    owner.obligation(),
                    &config,
                );
                println!(
                    "A64_NARROW_LEAF_QUERY {prep:?}: bytes={} sha256={:x}",
                    query.len(),
                    <sha2::Sha256 as sha2::Digest>::digest(query.as_bytes())
                );
                let verdict = verify_with_cli_raw_attributed(owner.obligation(), &config);
                println!(
                    "A64_NARROW_LEAF_QUALIFY {prep:?}: {} {}",
                    verdict.result,
                    verdict.provenance()
                );
                assert!(
                    matches!(verdict.result, AYResult::Verified),
                    "{prep:?}: {verdict:?}"
                );
                let mut wrong = machine.clone();
                let constant = wrong
                    .insts
                    .iter_mut()
                    .find(|inst| inst.opcode == trust_cg_ir::AArch64Opcode::Movz)
                    .unwrap();
                assert_eq!(constant.operands[1], trust_cg_ir::MachOperand::Imm(0));
                constant.operands[1] = trust_cg_ir::MachOperand::Imm(1);
                assert!(source_bound_a64_body(&source, &wrong).is_err());
                let problem = diagnostic_a64_body_obligation(&source, &wrong).unwrap();
                let verdict = verify_with_cli_raw_attributed(&problem, &AYConfig::default());
                println!(
                    "A64_NARROW_LEAF_MUTANT {prep:?}: {} {}",
                    verdict.result,
                    verdict.provenance()
                );
                assert!(
                    matches!(verdict.result, AYResult::CounterExample(_)),
                    "{prep:?}: {verdict:?}"
                );
            }
            for level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
                let module = trust_ir::binary::deserialize_module(include_bytes!(
                    "fixtures/aarch64_nonleaf_frame/termination_report.trust_irbin"
                ))
                .unwrap();
                let compiled = Compiler::new_for_target_spec(
                    CompilerConfig {
                        opt_level: level,
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
                .expect("the original leaf must pass proof-required production compilation");
                assert!(!compiled.object_code.is_empty());
                let certificates = compiled.proofs.as_ref().expect("emit_proofs certificates");
                let body: Vec<_> = certificates
                    .iter()
                    .filter(|certificate| {
                        certificate.rule_name
                            == trust_cg_verify::source_bound_a64_body::A64_BODY_OBLIGATION_NAME
                    })
                    .collect();
                let expected = match level {
                    OptLevel::O0 => 3,
                    OptLevel::O1 => 2,
                    OptLevel::O2 | OptLevel::O3 => 1,
                };
                assert_eq!(
                    body.len(),
                    expected,
                    "every live value row needs an exported body certificate: {level:?}: {certificates:?}"
                );
                for certificate in body {
                    assert!(
                        certificate.verified && certificate.strength == "Formal",
                        "{certificate:?}"
                    );
                    let payload = certificate
                        .source_bound_obligation
                        .as_ref()
                        .expect("exported body theorem");
                    assert_eq!(
                        payload.kind(),
                        trust_cg_verify::SourceBoundObligationKind::A64Body
                    );
                    assert_eq!(payload.function_name(), source.name);
                }
                println!(
                    "A64_NARROW_LEAF_EXPORTED_BODY_CERTIFICATES level={level:?} count={expected} strength=Formal"
                );
                let functions = function_words::function_words(&compiled.object_code);
                assert_eq!(functions.len(), 1);
                let words = functions.get(&source.name).expect("original source symbol");
                println!("A64_NARROW_LEAF_EMITTED level={level:?} words={words:x?}");
                if matches!(level, OptLevel::O2 | OptLevel::O3) {
                    assert_eq!(words.len(), 2, "folded body must emit two words");
                    assert_eq!(words[1], 0xd65f03c0, "RET X30");
                }
                println!(
                    "A64_NARROW_LEAF_PROOF_REQUIRED object_bytes={} object_sha256={:x}",
                    compiled.object_code.len(),
                    <sha2::Sha256 as sha2::Digest>::digest(&compiled.object_code),
                );
                #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
                {
                    let dir = tempfile::tempdir().unwrap();
                    let object = dir.path().join("leaf.o");
                    let caller = dir.path().join("caller.c");
                    let executable = dir.path().join("caller");
                    std::fs::write(&object, &compiled.object_code).unwrap();
                    std::fs::write(
                        &caller,
                        format!(
                            r#"extern unsigned char leaf(void) __asm__("_{}");
int main(void) {{ return leaf() != 0; }}
"#,
                            source.name,
                        ),
                    )
                    .unwrap();
                    let linked = std::process::Command::new("cc")
                        .arg("-O2")
                        .arg(&caller)
                        .arg(&object)
                        .arg("-o")
                        .arg(&executable)
                        .output()
                        .unwrap();
                    assert!(
                        linked.status.success(),
                        "{}",
                        String::from_utf8_lossy(&linked.stderr)
                    );
                    let executed = std::process::Command::new(&executable).status().unwrap();
                    assert!(
                        executed.success(),
                        "the native ABI caller must observe zero: {executed}"
                    );
                    println!("A64_NARROW_LEAF_NATIVE_CALL level={level:?} exit=0");
                }
            }
        });
    });
}
