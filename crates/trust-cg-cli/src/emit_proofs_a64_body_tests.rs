// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
//! AArch64 whole-body theorem export: publication under each credited row's
//! role category, the payload's category binding, and forged-metadata
//! refusal.
//!
//! A body payload exists only after the identity-admitted AY and a capable
//! Clean/Carcara checker replayed the theorem during the compile. This test
//! SKIPS, printing why, where either is absent or where no candidate body's
//! theorem replays with this host's AY (pack 9192's AY certifies few of these
//! theorems; the overlay pair of `reports/2026-10-01-aarch64-source-bound-body`
//! certifies both candidates).

use super::*;
use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::{OptLevel, encode_tmbc};
use trust_cg_codegen::target::TargetSpec;
use trust_cg_verify::source_bound_a64_body::{
    A64_BODY_NEEDS_REPLAY, A64_BODY_OBLIGATION_NAME, a64_body_row_categories,
};
use trust_ir::Ty;
use trust_ir_build::ModuleBuilder;

const TEST: &str = "a64_body_queries_survive_export_and_metadata_cannot_grant_authority";
const TARGET: &str = "aarch64-apple-darwin";

/// `select(c, a, b)` over a Boolean parameter: UXTB, CMP and CSEL.
fn bool_select() -> trust_ir::Module {
    let mut builder = ModuleBuilder::new("a64_body_export");
    let signature = builder.add_func_type(vec![Ty::Bool, Ty::U64, Ty::U64], vec![Ty::U64]);
    let mut f = builder.function("bool_select", signature);
    let entry = f.create_block();
    let c = f.add_block_param(entry, Ty::Bool);
    let a = f.add_block_param(entry, Ty::U64);
    let b = f.add_block_param(entry, Ty::U64);
    f.switch_to_block(entry);
    let selected = f.select(Ty::U64, c, a, b);
    f.ret(vec![selected]);
    f.build();
    builder.build().expect("ModuleBuilder::build: test fixture")
}

/// Rust's masked shift `x << (y & 63)`: LSLV alone at O1.
fn shl_masked() -> trust_ir::Module {
    let mut builder = ModuleBuilder::new("a64_body_export");
    let signature = builder.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::U64]);
    let mut f = builder.function("shl_masked", signature);
    let entry = f.create_block();
    let x = f.add_block_param(entry, Ty::U64);
    let y = f.add_block_param(entry, Ty::U64);
    f.switch_to_block(entry);
    let mask = f.iconst(Ty::U64, 63);
    let amount = f.binop(trust_ir::inst::BinOp::And, Ty::U64, y, mask);
    let shifted = f.binop(trust_ir::inst::BinOp::Shl, Ty::U64, x, amount);
    f.ret(vec![shifted]);
    f.build();
    builder.build().expect("ModuleBuilder::build: test fixture")
}

/// Why no body theorem can replay here, or `None` when one can.
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
    eprintln!("A64_BODY_EXPORT_REPLAY_IDENTITY ay=[{}]", ay.describe());
    None
}

/// Export one proof-required object's certificates and check the A64 body
/// payloads, the forgeries and the withdrawn checker. Returns the number of
/// body certificates exported.
fn export(
    name: &str,
    module: &trust_ir::Module,
    compiled: &trust_cg_codegen::compiler::CompilationResult,
) -> usize {
    let bytes = encode_tmbc(module).unwrap();
    let certs = compiled.proofs.clone().unwrap();
    let bodies: Vec<_> = certs
        .iter()
        .filter(|cert| {
            cert.source_bound_obligation
                .as_ref()
                .is_some_and(|payload| {
                    payload.kind() == trust_cg_verify::SourceBoundObligationKind::A64Body
                })
        })
        .cloned()
        .collect();
    assert!(
        !bodies.is_empty(),
        "{name}: no exported body theorem: {certs:?}"
    );
    for cert in &bodies {
        let payload = cert.source_bound_obligation.as_ref().unwrap();
        assert_eq!(cert.function_name, name);
        assert_eq!(cert.rule_name, A64_BODY_OBLIGATION_NAME);
        assert_eq!(payload.obligation().name, A64_BODY_OBLIGATION_NAME);
        assert!(
            a64_body_row_categories()
                .iter()
                .any(|category| category.to_string() == cert.category),
            "{cert:?}"
        );
        assert_eq!(cert.strength, "Formal");
        assert!(cert.verified);
    }

    let input = LoweringSidecarInputs {
        target: TARGET,
        trust_ir_bytes: &bytes,
        machine_code_bytes: &compiled.object_code,
        compiler_config_bytes: b"a64-body-export-test/O1",
        protected_paths: &[],
    };
    let dir = tempfile::tempdir().unwrap();
    let out = dir.path().join("proofs");
    let summary = emit_proof_files_with_lowering_sidecars(&out, &certs, input).unwrap();
    assert_eq!(
        summary.lowering_written, 1,
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
    // anything is published. Mutation 2 carries the body payload on a
    // category no body row takes; 3 claims sampled strength.
    let forgeries = 7;
    for mutation in 0..forgeries {
        let mut forged = bodies[0].clone();
        match mutation {
            0 => forged.function_name.push_str("_other"),
            1 => forged.rule_name.push_str("_other"),
            2 => forged.category = trust_cg_verify::ProofCategory::X8664Lowering.to_string(),
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
            "{name}: mutation {mutation}"
        );
        assert!(
            !dest.exists(),
            "{name}: forged metadata {mutation} published files"
        );
    }

    // The export is re-checked against the replay authority before
    // publication: with the independent checker withdrawn, nothing publishes.
    trust_cg_verify::env_lock::with_env_overrides(
        &[(
            "TCG_EXTERNAL_CLEAN_CHECKER",
            "/nonexistent/a64-body-export-checker",
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
        "A64_BODY_EXPORT function={name} bodies={} categories={:?} metadata_refusals={forgeries} \
         withdrawn_checker_refused=true",
        bodies.len(),
        bodies
            .iter()
            .map(|cert| cert.category.as_str())
            .collect::<Vec<_>>()
    );
    bodies.len()
}

fn body_exports() {
    if let Some(reason) = replay_unavailable() {
        eprintln!("SKIP {TEST}: {reason}");
        return;
    }
    let mut exported = 0usize;
    let mut unreplayed = Vec::new();
    for (name, module) in [("bool_select", bool_select()), ("shl_masked", shl_masked())] {
        let compiler = Compiler::new_for_target_spec(
            CompilerConfig {
                opt_level: OptLevel::O1,
                emit_proofs: true,
                parallel: false,
                ..Default::default()
            },
            TargetSpec::parse(TARGET).unwrap(),
        )
        .with_codegen_license(crate::license_test_support::permit_unlicensed());
        match compiler.compile(&module) {
            Ok(compiled) => exported += export(name, &module, &compiled),
            // Only this AY's failure to certify the body theorem may refuse
            // these copy- and constant-free bodies.
            Err(error) => {
                let text = error.to_string();
                assert!(text.contains(A64_BODY_NEEDS_REPLAY), "{name}: {text}");
                unreplayed.push(name);
            }
        }
    }
    if exported == 0 {
        eprintln!(
            "SKIP {TEST}: this AY's proof of no candidate body theorem replays ({unreplayed:?})"
        );
        return;
    }
    println!("A64_BODY_EXPORT_SUMMARY exported={exported} unreplayed={unreplayed:?}");
}

#[test]
fn a64_body_queries_survive_export_and_metadata_cannot_grant_authority() {
    std::thread::Builder::new()
        .stack_size(16 * 1024 * 1024)
        .spawn(body_exports)
        .unwrap()
        .join()
        .unwrap();
}
