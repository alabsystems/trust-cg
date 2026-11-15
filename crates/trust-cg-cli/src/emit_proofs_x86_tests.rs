// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
//! x86-64 whole-body theorem export: publication, the payload's category
//! binding, and forged-metadata refusal.
//!
//! A body payload exists only after the identity-admitted AY and a capable
//! Clean/Carcara checker replayed the theorem during the compile, so this
//! test SKIPS, printing why, where either is absent.

use super::*;
use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::{OptLevel, encode_tmbc};
use trust_cg_codegen::target::TargetSpec;
use trust_ir::Ty;
use trust_ir_build::ModuleBuilder;

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_codegen::CodegenLicensePolicy {
    trust_cg_codegen::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit)
}

const TEST: &str = "x86_body_queries_survive_export_and_metadata_cannot_grant_authority";

fn module() -> trust_ir::Module {
    let mut builder = ModuleBuilder::new("x86_body_export");
    let binary = builder.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::U64]);
    let unary = builder.add_func_type(vec![Ty::U64], vec![Ty::U64]);

    let mut f = builder.function("add", binary);
    let entry = f.create_block();
    let a = f.add_block_param(entry, Ty::U64);
    let b = f.add_block_param(entry, Ty::U64);
    f.switch_to_block(entry);
    let sum = f.add(Ty::U64, a, b);
    f.ret(vec![sum]);
    let add = f.build();

    let mut f = builder.function("ident", unary);
    let entry = f.create_block();
    let x = f.add_block_param(entry, Ty::U64);
    f.switch_to_block(entry);
    f.ret(vec![x]);
    f.build();

    // Slice-2 widths: a bool identity (walked under both caller conventions:
    // EAX = 0/1 for a clean-bool caller, AL = 0/1 for a psABI caller) and a
    // zero-extended narrow parameter.
    let bool_ident = builder.add_func_type(vec![Ty::Bool], vec![Ty::Bool]);
    let mut f = builder.function("bool_ident", bool_ident);
    let entry = f.create_block();
    let b = f.add_block_param(entry, Ty::Bool);
    f.switch_to_block(entry);
    f.ret(vec![b]);
    f.build();

    let widen = builder.add_func_type(vec![Ty::U8], vec![Ty::U64]);
    let mut f = builder.function("widen_u8", widen);
    let entry = f.create_block();
    let x = f.add_block_param(entry, Ty::U8);
    f.switch_to_block(entry);
    let wide = f.zext(Ty::U8, Ty::U64, x);
    f.ret(vec![wide]);
    f.build();

    // Slice 3: a direct call to a function of this module (exact-module
    // binding), whose theorem shares the callee's result and observes its
    // arguments.
    let mut f = builder.function("twice", unary);
    let entry = f.create_block();
    let x = f.add_block_param(entry, Ty::U64);
    f.switch_to_block(entry);
    let doubled = f.call(add, vec![x, x]);
    f.ret(vec![doubled]);
    f.build();

    builder.build().expect("ModuleBuilder::build: test fixture")
}

/// Why the body theorem cannot replay here, or `None` when it can.
fn replay_unavailable() -> Option<String> {
    if std::env::var_os("TCG_REFINE_SOLVER").is_some_and(|value| value == "0") {
        return Some("TCG_REFINE_SOLVER=0 refuses live replay".into());
    }
    let Some(ay) = trust_cg_verify::ay_bridge::admitted_proof_solver() else {
        return Some(
            trust_cg_verify::ay_bridge::proof_toolchain_unavailable_reason()
                .unwrap_or_else(|| "no admitted AY with a capable checker".into()),
        );
    };
    eprintln!("X86_BODY_EXPORT_REPLAY_IDENTITY ay=[{}]", ay.describe());
    None
}

fn body_exports() {
    if let Some(reason) = replay_unavailable() {
        eprintln!("SKIP {TEST}: {reason}");
        return;
    }
    const TARGET: &str = "x86_64-apple-darwin";
    let module = module();
    let bytes = encode_tmbc(&module).unwrap();
    let compiler = Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level: OptLevel::O0,
            emit_proofs: true,
            parallel: false,
            ..Default::default()
        },
        TargetSpec::parse(TARGET).unwrap(),
    )
    .with_codegen_license(permit_unlicensed());
    let result = compiler
        .compile(&module)
        .expect("replayed body theorems promote the body-lane functions");
    let certs = result.proofs.unwrap();
    let bodies: Vec<_> = certs
        .iter()
        .filter(|cert| cert.source_bound_obligation.is_some())
        .cloned()
        .collect();
    for function in ["add", "ident", "bool_ident", "widen_u8", "twice"] {
        assert!(
            bodies.iter().any(|cert| cert.function_name == function),
            "{function}: no exported body theorem"
        );
    }
    for cert in &bodies {
        let payload = cert.source_bound_obligation.as_ref().unwrap();
        assert_eq!(
            payload.kind(),
            trust_cg_verify::SourceBoundObligationKind::X86Body
        );
        assert_eq!(
            cert.category,
            trust_cg_verify::ProofCategory::X8664Lowering.to_string()
        );
        assert_eq!(cert.strength, "Formal");
        assert!(cert.verified);
    }

    let input = LoweringSidecarInputs {
        target: TARGET,
        trust_ir_bytes: &bytes,
        machine_code_bytes: &result.object_code,
        compiler_config_bytes: b"x86-body-export-test/O0",
        protected_paths: &[],
    };
    let dir = tempfile::tempdir().unwrap();
    let out = dir.path().join("proofs");
    let summary = emit_proof_files_with_lowering_sidecars(&out, &certs, input).unwrap();
    assert_eq!(
        summary.lowering_written, 5,
        "one lowering sidecar per function"
    );
    for cert in &bodies {
        let path = out
            .join(sanitize_path(&cert.category))
            .join(format!("{}.smt2", rule_file_stem(cert)));
        assert_eq!(
            fs::read_to_string(&path).unwrap(),
            serialize_to_smt2(cert.source_bound_obligation.as_ref().unwrap().obligation()),
            "{}",
            path.display()
        );
    }

    // Metadata cannot grant authority: every forged row is refused before
    // anything is published. Mutation 2 carries the x86-64 body payload on
    // an Arithmetic (AArch64 ALU) row; 3 claims sampled strength.
    let forgeries = 7;
    for mutation in 0..forgeries {
        let mut forged = bodies[0].clone();
        match mutation {
            0 => forged.function_name.push_str("_other"),
            1 => forged.rule_name.push_str("_other"),
            2 => forged.category = trust_cg_verify::ProofCategory::Arithmetic.to_string(),
            3 => forged.strength = "Statistical".into(),
            4 => forged.verified = false,
            5 => forged.category = "covered_elsewhere".into(),
            _ => forged.source_bound_obligation = None,
        }
        let dest = dir.path().join(format!("forged-{mutation}"));
        let err = emit_proof_files_with_lowering_sidecars(&dest, &[forged], input).unwrap_err();
        assert_eq!(
            err.kind(),
            io::ErrorKind::InvalidData,
            "mutation {mutation}"
        );
        assert!(!dest.exists(), "forged metadata {mutation} published files");
    }

    // The export is re-checked against the replay authority before
    // publication: with the independent checker withdrawn, nothing publishes.
    trust_cg_verify::env_lock::with_env_overrides(
        &[(
            "TCG_EXTERNAL_CLEAN_CHECKER",
            "/nonexistent/x86-body-export-checker",
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
        "X86_BODY_EXPORT bodies={} metadata_refusals={forgeries} withdrawn_checker_refused=true",
        bodies.len()
    );
}

#[test]
fn x86_body_queries_survive_export_and_metadata_cannot_grant_authority() {
    std::thread::Builder::new()
        .stack_size(16 * 1024 * 1024)
        .spawn(body_exports)
        .unwrap()
        .join()
        .unwrap();
}
