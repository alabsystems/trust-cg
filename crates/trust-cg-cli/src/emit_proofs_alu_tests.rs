// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
//! Exact arithmetic export, publication and independently replayed authority.

use super::*;
use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::{OptLevel, encode_tmbc};
use trust_cg_codegen::target::TargetSpec;
use trust_ir::Ty;
use trust_ir_build::ModuleBuilder;

fn arithmetic_exports() {
    let mut builder = ModuleBuilder::new("arithmetic_export");
    // The 32-bit ingress/return path retains live W copies at O0, alongside
    // two distinct SUB immediates and two dead constant materializations.
    let signature = builder.add_func_type(vec![Ty::U32], vec![Ty::U32]);
    let mut f = builder.function("calculate", signature);
    let entry = f.create_block();
    let a = f.add_block_param(entry, Ty::U32);
    f.switch_to_block(entry);
    let three = f.iconst(Ty::U32, 3);
    let seven = f.iconst(Ty::U32, 7);
    let a = f.sub(Ty::U32, a, three);
    let a = f.sub(Ty::U32, a, seven);
    f.ret(vec![a]);
    f.build();
    let module = builder.build().expect("ModuleBuilder::build: test fixture");
    let bytes = encode_tmbc(&module).unwrap();
    let compiler = Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level: OptLevel::O0,
            emit_proofs: true,
            parallel: false,
            enable_jit_fast_regalloc: true,
            ..Default::default()
        },
        TargetSpec::parse("aarch64-unknown-linux-gnu").unwrap(),
    )
    .with_codegen_license(permit_unlicensed());
    let result = compiler
        .compile(&module)
        .expect("proof-required arithmetic object");
    let mut certs = result.proofs.unwrap();
    let dynamic: Vec<_> = certs
        .iter()
        .filter(|c| {
            c.source_bound_obligation.as_ref().is_some_and(|bound| {
                bound.kind() == trust_cg_verify::SourceBoundObligationKind::A64Alu
            })
        })
        .cloned()
        .collect();
    assert_eq!(
        dynamic.len(),
        2,
        "both actual SUB immediates must survive O0"
    );
    let constants: Vec<_> = certs
        .iter()
        .filter(|c| {
            c.source_bound_obligation.as_ref().is_some_and(|bound| {
                bound.kind() == trust_cg_verify::SourceBoundObligationKind::A64Constant
            })
        })
        .cloned()
        .collect();
    assert_eq!(
        constants.len(),
        2,
        "both dead O0 materializations need source-bound proofs"
    );
    assert!(
        constants
            .iter()
            .all(|cert| cert.verified && cert.strength == "Formal")
    );
    let bodies: Vec<_> = certs
        .iter()
        .filter(|cert| {
            cert.source_bound_obligation.as_ref().is_some_and(|bound| {
                bound.kind() == trust_cg_verify::SourceBoundObligationKind::A64Body
            })
        })
        .cloned()
        .collect();
    assert!(
        !bodies.is_empty(),
        "O0 fast allocation must retain a return copy"
    );
    assert!(
        bodies
            .iter()
            .all(|cert| cert.verified && cert.strength == "Formal")
    );
    let body_stems: std::collections::HashSet<_> = bodies.iter().map(rule_file_stem).collect();
    assert_eq!(
        body_stems.len(),
        1,
        "N credited copies share one exact theorem file"
    );
    assert_eq!(dynamic[0].rule_name, dynamic[1].rule_name);
    assert_ne!(rule_file_stem(&dynamic[0]), rule_file_stem(&dynamic[1]));
    certs.push(dynamic[0].clone()); // Exact duplicates may be shared.
    certs.push(bodies[0].clone());
    let input = LoweringSidecarInputs {
        target: "aarch64-unknown-linux-gnu",
        trust_ir_bytes: &bytes,
        machine_code_bytes: &result.object_code,
        compiler_config_bytes: b"arithmetic-export-test/O0",
        protected_paths: &[],
    };
    let dir = tempfile::tempdir().unwrap();
    let out = dir.path().join("proofs");
    let summary = emit_proof_files_with_lowering_sidecars(&out, &certs, input).unwrap();
    assert_eq!(summary.lowering_written, 1);
    assert_eq!(summary.trust_proof_cert_written, 1);
    let lowering = trust_cg_verify::proof_certificate::LoweringCertificate::from_json(
        &fs::read_to_string(out.join("calculate.lowering.json")).unwrap(),
    )
    .unwrap();
    let rules: Vec<_> = lowering
        .rule_proofs
        .iter()
        .filter(|p| p.rule_name == dynamic[0].rule_name)
        .collect();
    assert_eq!(
        rules.len(),
        2,
        "a display name cannot collapse different theorems"
    );
    assert_ne!(rules[0].obligation_hash, rules[1].obligation_hash);
    assert_eq!(
        lowering
            .rule_proofs
            .iter()
            .filter(|proof| proof.rule_name == bodies[0].rule_name)
            .count(),
        1,
        "one body theorem is retained once in the lowering sidecar"
    );
    for cert in dynamic.iter().chain(&constants).chain(&bodies) {
        let path = out
            .join(sanitize_path(&cert.category))
            .join(format!("{}.smt2", rule_file_stem(cert)));
        assert_eq!(
            fs::read_to_string(path).unwrap(),
            serialize_to_smt2(cert.source_bound_obligation.as_ref().unwrap().obligation())
        );
    }
    for (kind, cert) in
        ["alu", "constant", "body"]
            .into_iter()
            .zip([&dynamic[0], &constants[0], &bodies[0]])
    {
        for mutation in 0..6 {
            let mut forged = cert.clone();
            match mutation {
                0 => forged.function_name.push_str("_other"),
                1 => forged.rule_name.push_str("_other"),
                2 => forged.category = "covered_elsewhere".into(),
                3 => forged.strength = "Statistical".into(),
                4 => forged.verified = false,
                _ => forged.source_bound_obligation = None,
            }
            let dest = dir.path().join(format!("forged-{kind}-{mutation}"));
            let err = emit_proof_files_with_lowering_sidecars(&dest, &[forged], input).unwrap_err();
            assert_eq!(err.kind(), io::ErrorKind::InvalidData);
            assert!(!dest.exists(), "forged metadata published files");
        }
    }
    // A successful compile and warm proof caches cannot authorize an export
    // after its independent checker has been withdrawn.
    trust_cg_verify::env_lock::with_env_overrides(
        &[(
            "TCG_EXTERNAL_CLEAN_CHECKER",
            "/nonexistent/arithmetic-export-checker",
        )],
        || {
            let dest = dir.path().join("checker-withdrawn");
            let err = emit_proof_files_with_lowering_sidecars(&dest, &certs, input).unwrap_err();
            assert!(
                err.to_string()
                    .contains("failed to generate lowering certificate"),
                "{err}"
            );
            assert!(!dest.exists());
        },
    );
    println!(
        "ARITHMETIC_EXPORT alu_queries=2 constant_queries=2 body_queries=1 live_copies={} metadata_refusals=18 withdrawn_checker_refused=true",
        bodies.len()
    );
}

#[test]
fn exact_arithmetic_queries_survive_export_and_metadata_cannot_grant_authority() {
    std::thread::Builder::new()
        .stack_size(16 * 1024 * 1024)
        .spawn(arithmetic_exports)
        .unwrap()
        .join()
        .unwrap();
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_codegen::CodegenLicensePolicy {
    trust_cg_codegen::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit)
}
