// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
//! Required ordinary Trust comparison export; no unavailable-proof skip.
//! The separate native test executes explicitly uncertified bytes and grants
//! no proof credit to this required AY/Clean publication gate.

use super::*;
use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::{OptLevel, encode_tmbc};
use trust_cg_codegen::target::TargetSpec;
use trust_cg_verify::{ProofCategory, SourceBoundObligationKind};
use trust_ir::{ICmpOp, Ty};
use trust_ir_build::ModuleBuilder;

const TARGET: &str = "aarch64-apple-darwin";
const COMPARISONS: [ICmpOp; 10] = [
    ICmpOp::Eq,
    ICmpOp::Ne,
    ICmpOp::Slt,
    ICmpOp::Sle,
    ICmpOp::Sgt,
    ICmpOp::Sge,
    ICmpOp::Ult,
    ICmpOp::Ule,
    ICmpOp::Ugt,
    ICmpOp::Uge,
];

fn function_name(bits: u32, comparison: ICmpOp) -> String {
    format!("cmp_i{bits}_{comparison:?}")
}

fn comparison_module() -> trust_ir::Module {
    let mut builder = ModuleBuilder::new("ordinary_comparison_export");
    for (bits, ty) in [(32, Ty::I32), (64, Ty::I64)] {
        let signature = builder.add_func_type(vec![ty.clone(); 2], vec![Ty::Bool]);
        for comparison in COMPARISONS {
            let name = function_name(bits, comparison);
            let mut f = builder.function(&name, signature);
            let entry = f.create_block();
            let a = f.add_block_param(entry, ty.clone());
            let b = f.add_block_param(entry, ty.clone());
            f.switch_to_block(entry);
            let result = f.icmp(comparison, ty.clone(), a, b);
            f.ret(vec![result]);
            f.build();
        }
    }
    builder.build().expect("ModuleBuilder::build: test fixture")
}

fn forged_refuses(
    destination: &Path,
    forged: CodegenCertificate,
    input: LoweringSidecarInputs<'_>,
) {
    let error = emit_proof_files_with_lowering_sidecars(destination, &[forged], input).unwrap_err();
    assert_eq!(error.kind(), io::ErrorKind::InvalidData, "{error}");
    assert!(!destination.exists(), "forged metadata published files");
}

fn comparison_exports() {
    let module = comparison_module();
    let bytes = encode_tmbc(&module).unwrap();
    let result = Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level: OptLevel::O0,
            emit_proofs: true,
            parallel: false,
            enable_jit_fast_regalloc: true,
            ..Default::default()
        },
        TargetSpec::parse(TARGET).unwrap(),
    )
    .with_codegen_license(crate::license_test_support::permit_unlicensed())
    .compile(&module)
    .expect("all twenty Darwin comparison objects require independently replayed certificates");
    let mut certs = result
        .proofs
        .expect("proof-required compile reports certificates");
    let bodies: Vec<_> = certs
        .iter()
        .filter(|cert| {
            cert.source_bound_obligation
                .as_ref()
                .is_some_and(|bound| bound.kind() == SourceBoundObligationKind::A64Body)
        })
        .cloned()
        .collect();
    let mut exact_queries = HashSet::new();
    for bits in [32, 64] {
        for comparison in COMPARISONS {
            let name = function_name(bits, comparison);
            let rows: Vec<_> = bodies
                .iter()
                .filter(|cert| cert.function_name == name)
                .collect();
            assert!(
                rows.len() >= 2,
                "{name}: live CMP/CSET exports are required"
            );
            let mut instructions = HashSet::new();
            let mut queries = HashSet::new();
            let mut stems = HashSet::new();
            for cert in rows {
                let bound = cert.source_bound_obligation.as_ref().unwrap();
                assert_eq!(bound.proof_category(), ProofCategory::Comparison);
                assert_eq!(cert.category, ProofCategory::Comparison.to_string());
                assert_eq!(bound.function_name(), name);
                assert!(cert.verified && cert.strength == "Formal", "{cert:?}");
                assert!(!bound.obligation().is_degenerate());
                assert!(instructions.insert(bound.instruction_index()));
                let query = serialize_to_smt2(bound.obligation());
                assert!(query.contains("bvsub"), "{name}: raw CMP flags disappeared");
                assert!(
                    query.contains("zero_extend 63"),
                    "{name}: canonical B1 carrier lost"
                );
                queries.insert(query.clone());
                exact_queries.insert(query);
                stems.insert(rule_file_stem(cert));
            }
            assert_eq!(
                queries.len(),
                1,
                "{name}: live rows must share one exact query"
            );
            assert_eq!(
                stems.len(),
                1,
                "{name}: live rows must share one theorem file"
            );
        }
    }
    assert_eq!(
        exact_queries.len(),
        20,
        "widths and conditions retain distinct queries"
    );
    certs.push(bodies[0].clone()); // Exact duplicate rows must not multiply query files.
    let input = LoweringSidecarInputs {
        target: TARGET,
        trust_ir_bytes: &bytes,
        machine_code_bytes: &result.object_code,
        compiler_config_bytes: b"ordinary-comparison-export/O0/proof-required",
        protected_paths: &[],
    };
    let dir = tempfile::tempdir().unwrap();
    let out = dir.path().join("proofs");
    let summary = emit_proof_files_with_lowering_sidecars(&out, &certs, input).unwrap();
    assert_eq!(summary.lowering_written, 20);
    assert_eq!(summary.trust_proof_cert_written, 20);
    let stems: HashSet<_> = bodies.iter().map(rule_file_stem).collect();
    assert_eq!(stems.len(), 20);
    let comparison_dir = out.join(sanitize_path(&ProofCategory::Comparison.to_string()));
    let smt_files = fs::read_dir(&comparison_dir)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .filter(|path| {
            path.extension()
                .is_some_and(|extension| extension == "smt2")
        })
        .count();
    assert_eq!(
        smt_files, 20,
        "live CMP/CSET/copy rows deduplicate exact theorems"
    );
    for cert in &bodies {
        let bound = cert.source_bound_obligation.as_ref().unwrap();
        let path = comparison_dir.join(format!("{}.smt2", rule_file_stem(cert)));
        assert_eq!(
            fs::read_to_string(path).unwrap(),
            serialize_to_smt2(bound.obligation())
        );
        let lowering = trust_cg_verify::proof_certificate::LoweringCertificate::from_json(
            &fs::read_to_string(out.join(format!("{}.lowering.json", cert.function_name))).unwrap(),
        )
        .unwrap();
        assert_eq!(
            lowering
                .rule_proofs
                .iter()
                .filter(|proof| proof.rule_name == cert.rule_name)
                .count(),
            1,
            "one exact comparison body theorem per function sidecar"
        );
    }
    // Every condition/width's immutable category must reject alternate report
    // categories, not just one representative comparison's display name.
    for bits in [32, 64] {
        for comparison in COMPARISONS {
            let name = function_name(bits, comparison);
            let cert = bodies
                .iter()
                .find(|cert| cert.function_name == name)
                .unwrap();
            for category in [ProofCategory::Arithmetic, ProofCategory::Branch] {
                let mut forged = cert.clone();
                forged.category = category.to_string();
                forged_refuses(
                    &dir.path().join(format!("forged-{name}-{category}")),
                    forged,
                    input,
                );
            }
        }
    }
    for mutation in 0..6 {
        let mut forged = bodies[0].clone();
        match mutation {
            0 => forged.function_name.push_str("_other"),
            1 => forged.rule_name.push_str("_other"),
            2 => forged.strength = "Statistical".into(),
            3 => forged.verified = false,
            4 => forged.category = "covered_elsewhere".into(),
            _ => forged.source_bound_obligation = None,
        }
        forged_refuses(
            &dir.path().join(format!("forged-other-{mutation}")),
            forged,
            input,
        );
    }
    trust_cg_verify::env_lock::with_env_overrides(
        &[(
            "TCG_EXTERNAL_CLEAN_CHECKER",
            "/nonexistent/comparison-export-checker",
        )],
        || {
            let destination = dir.path().join("checker-withdrawn");
            let error =
                emit_proof_files_with_lowering_sidecars(&destination, &certs, input).unwrap_err();
            assert!(
                error
                    .to_string()
                    .contains("failed to generate lowering certificate"),
                "{error}"
            );
            assert!(!destination.exists());
        },
    );
    println!(
        "COMPARISON_EXPORT target={TARGET} functions=20 exact_queries=20 live_rows={} metadata_refusals=46 withdrawn_checker_refused=true",
        bodies.len()
    );
}

#[test]
fn exact_comparison_queries_survive_export_and_categories_cannot_grant_authority() {
    std::thread::Builder::new()
        .stack_size(16 * 1024 * 1024)
        .spawn(comparison_exports)
        .unwrap()
        .join()
        .unwrap();
}

#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
fn reference(comparison: ICmpOp, bits: u32, a: u64, b: u64) -> bool {
    let (a, b) = if bits == 32 {
        (u64::from(a as u32), u64::from(b as u32))
    } else {
        (a, b)
    };
    let (signed_a, signed_b) = if bits == 32 {
        (a as i32 as i64, b as i32 as i64)
    } else {
        (a as i64, b as i64)
    };
    match comparison {
        ICmpOp::Eq => a == b,
        ICmpOp::Ne => a != b,
        ICmpOp::Slt => signed_a < signed_b,
        ICmpOp::Sle => signed_a <= signed_b,
        ICmpOp::Sgt => signed_a > signed_b,
        ICmpOp::Sge => signed_a >= signed_b,
        ICmpOp::Ult => a < b,
        ICmpOp::Ule => a <= b,
        ICmpOp::Ugt => a > b,
        ICmpOp::Uge => a >= b,
    }
}

#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
#[test]
fn ordinary_comparisons_execute_in_explicit_unchecked_native_lane() {
    let compiler = Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level: OptLevel::O0,
            ..CompilerConfig::for_host_jit_unchecked()
        },
        TargetSpec::parse(TARGET).unwrap(),
    )
    .with_codegen_license(crate::license_test_support::permit_unlicensed());
    let result = compiler
        .compile_module_to_jit(&comparison_module(), &HashMap::new())
        .expect("explicitly uncertified native comparison code must execute");
    assert!(
        result.proofs.is_none(),
        "unchecked native controls grant no certificate credit"
    );
    let inputs = [
        0,
        1,
        2,
        4095,
        (1 << 31) - 1,
        1 << 31,
        u32::MAX as u64,
        1 << 32,
        i64::MAX as u64,
        1 << 63,
        u64::MAX,
    ];
    let mut calls = 0;
    for bits in [32, 64] {
        for comparison in COMPARISONS {
            let name = function_name(bits, comparison);
            for a in inputs {
                for b in inputs {
                    // SAFETY: these are the exact scalar C ABI signatures of
                    // the corresponding source leaves; result owns their code.
                    let actual = unsafe {
                        if bits == 32 {
                            result
                                .buffer
                                .get_fn_bound::<unsafe extern "C" fn(i32, i32) -> bool>(&name)
                                .unwrap()
                                .as_ref()(a as i32, b as i32)
                        } else {
                            result
                                .buffer
                                .get_fn_bound::<unsafe extern "C" fn(i64, i64) -> bool>(&name)
                                .unwrap()
                                .as_ref()(a as i64, b as i64)
                        }
                    };
                    assert_eq!(actual, reference(comparison, bits, a, b), "{name}/{a}/{b}");
                    calls += 1;
                }
            }
        }
    }
    assert_eq!(calls, 2420);
    println!(
        "COMPARISON_NATIVE target={TARGET} validation=Unchecked proof_credit=false functions=20 calls={calls}"
    );
}
