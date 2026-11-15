// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
//! Required ordinary Trust selection export, separately from explicitly
//! unchecked native execution. An unavailable positive AY/Clean replay fails
//! before any metadata or withdrawal control is counted.

use super::*;
#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
use trust_cg_codegen::compiler::JitValidationMode;
use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::{OptLevel, encode_tmbc};
use trust_cg_codegen::target::TargetSpec;
use trust_cg_verify::smt::SmtSort;
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
    format!("select_i{bits}_{comparison:?}")
}

fn select_module() -> trust_ir::Module {
    let mut builder = ModuleBuilder::new("ordinary_select_export");
    for (bits, ty) in [(32, Ty::I32), (64, Ty::I64)] {
        let signature = builder.add_func_type(vec![ty.clone(); 4], vec![ty.clone()]);
        for comparison in COMPARISONS {
            let name = function_name(bits, comparison);
            let mut f = builder.function(&name, signature);
            let entry = f.create_block();
            let a = f.add_block_param(entry, ty.clone());
            let b = f.add_block_param(entry, ty.clone());
            let c = f.add_block_param(entry, ty.clone());
            let d = f.add_block_param(entry, ty.clone());
            f.switch_to_block(entry);
            let condition = f.icmp(comparison, ty.clone(), a, b);
            let selected = f.select(ty.clone(), condition, c, d);
            f.ret(vec![selected]);
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

fn select_exports() {
    let module = select_module();
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
    .expect("all twenty Darwin selects require independently replayed frame/body certificates");
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
                "{name}: live CMP/select exports are required"
            );
            let mut instructions = HashSet::new();
            let mut queries = HashSet::new();
            let mut stems = HashSet::new();
            for cert in rows {
                let bound = cert.source_bound_obligation.as_ref().unwrap();
                assert_eq!(bound.proof_category(), ProofCategory::Arithmetic);
                assert_eq!(cert.category, ProofCategory::Arithmetic.to_string());
                assert_eq!(bound.function_name(), name);
                assert!(cert.verified && cert.strength == "Formal", "{cert:?}");
                let obligation = bound.obligation();
                assert!(!obligation.is_degenerate());
                assert_eq!(obligation.trust_ir_expr.sort(), SmtSort::BitVec(bits));
                assert_eq!(obligation.aarch64_expr.sort(), SmtSort::BitVec(bits));
                assert_eq!(
                    obligation.inputs,
                    (0..4)
                        .map(|i| (format!("abi_x{i}"), 64))
                        .collect::<Vec<_>>()
                );
                let source = obligation.trust_ir_expr.to_smt2_expr();
                let machine = obligation.aarch64_expr.to_smt2_expr();
                for expr in [&source, &machine] {
                    assert!(expr.contains("(ite "), "{name}: selection disappeared");
                    assert!(
                        expr.contains("abi_x2") && expr.contains("abi_x3"),
                        "{name}: actual selection arms disappeared"
                    );
                }
                assert!(
                    machine.contains("bvsub"),
                    "{name}: raw CMP flags disappeared"
                );
                if bits == 32 {
                    assert!(
                        machine.contains("zero_extend 32"),
                        "{name}: W writes must retain upper-half clearing"
                    );
                }
                assert!(instructions.insert(bound.instruction_index()));
                let query = serialize_to_smt2(obligation);
                queries.insert(query.clone());
                exact_queries.insert(query);
                stems.insert(rule_file_stem(cert));
            }
            assert_eq!(
                queries.len(),
                1,
                "{name}: one exact theorem for its live rows"
            );
            assert_eq!(stems.len(), 1, "{name}: one theorem file for its live rows");
        }
    }
    assert_eq!(
        exact_queries.len(),
        20,
        "all conditions and widths stay distinct"
    );
    certs.push(bodies[0].clone()); // Duplicate rows must not duplicate theorem files.
    let input = LoweringSidecarInputs {
        target: TARGET,
        trust_ir_bytes: &bytes,
        machine_code_bytes: &result.object_code,
        compiler_config_bytes: b"ordinary-select-export/O0/proof-required",
        protected_paths: &[],
    };
    let dir = tempfile::tempdir().unwrap();
    let out = dir.path().join("proofs");
    let summary = emit_proof_files_with_lowering_sidecars(&out, &certs, input).unwrap();
    assert_eq!(summary.lowering_written, 20);
    assert_eq!(summary.trust_proof_cert_written, 20);
    let arithmetic_dir = out.join(sanitize_path(&ProofCategory::Arithmetic.to_string()));
    let smt_files = fs::read_dir(&arithmetic_dir)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .filter(|path| {
            path.extension()
                .is_some_and(|extension| extension == "smt2")
        })
        .count();
    assert_eq!(
        smt_files, 20,
        "live CMP/select/copy rows deduplicate exact theorems"
    );
    for cert in &bodies {
        let bound = cert.source_bound_obligation.as_ref().unwrap();
        let path = arithmetic_dir.join(format!("{}.smt2", rule_file_stem(cert)));
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
            "one exact selection body theorem per function sidecar"
        );
    }

    // Positive compilation and publication must complete before these controls.
    let mut metadata_refusals = 0;
    for bits in [32, 64] {
        for comparison in COMPARISONS {
            let name = function_name(bits, comparison);
            let cert = bodies
                .iter()
                .find(|cert| cert.function_name == name)
                .unwrap();
            for category in [ProofCategory::Comparison, ProofCategory::Branch] {
                let mut forged = cert.clone();
                forged.category = category.to_string();
                forged_refuses(
                    &dir.path().join(format!("forged-{name}-{category}")),
                    forged,
                    input,
                );
                metadata_refusals += 1;
            }
            let other_name = function_name(if bits == 32 { 64 } else { 32 }, comparison);
            let other = bodies
                .iter()
                .find(|cert| cert.function_name == other_name)
                .unwrap();
            let mut forged = cert.clone();
            forged.source_bound_obligation = other.source_bound_obligation.clone();
            forged_refuses(
                &dir.path().join(format!("forged-width-{name}")),
                forged,
                input,
            );
            metadata_refusals += 1;
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
        metadata_refusals += 1;
    }
    assert_eq!(metadata_refusals, 66);
    trust_cg_verify::env_lock::with_env_overrides(
        &[(
            "TCG_EXTERNAL_CLEAN_CHECKER",
            "/nonexistent/select-export-checker",
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
        "SELECT_EXPORT target={TARGET} functions=20 exact_queries=20 live_rows={} metadata_refusals={metadata_refusals} withdrawn_checker_refused=true",
        bodies.len()
    );
}

#[test]
fn exact_select_queries_survive_export_and_metadata_cannot_grant_authority() {
    std::thread::Builder::new()
        .stack_size(16 * 1024 * 1024)
        .spawn(select_exports)
        .unwrap()
        .join()
        .unwrap();
}

#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
fn reference(comparison: ICmpOp, bits: u32, [a, b, c, d]: [u64; 4]) -> u64 {
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
    let predicate = match comparison {
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
    };
    let result = if predicate { c } else { d };
    if bits == 32 {
        u64::from(result as u32)
    } else {
        result
    }
}

#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
fn native_vectors() -> Vec<[u64; 4]> {
    let edges = [
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
    let arms = [
        (0, 1),
        (1, u64::MAX),
        (1 << 31, (1 << 31) - 1),
        (0x0123_4567_89ab_cdef, 0xfedc_ba98_7654_3210),
    ];
    let mut vectors = Vec::new();
    for a in edges {
        for b in edges {
            for (c, d) in arms {
                vectors.push([a, b, c, d]);
            }
        }
    }
    let mut seed = 0x4f44_3837_7365_6c65_u64;
    for _ in 0..128 {
        let tuple = std::array::from_fn(|_| {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        });
        vectors.push(tuple);
    }
    assert_eq!(vectors.len(), 612);
    vectors
}

#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
#[test]
fn ordinary_selects_execute_in_explicit_unchecked_native_lane() {
    let module = select_module();
    let vectors = native_vectors();
    let mut calls = 0;
    for level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
        let config = CompilerConfig {
            opt_level: level,
            jit_validation_mode_override: Some(JitValidationMode::Unchecked),
            ..CompilerConfig::for_host_jit_unchecked()
        };
        assert_eq!(config.jit_validation_mode(), JitValidationMode::Unchecked);
        let result = Compiler::new_for_target_spec(config, TargetSpec::parse(TARGET).unwrap())
            .with_codegen_license(crate::license_test_support::permit_unlicensed())
            .compile_module_to_jit(&module, &HashMap::new())
            .expect(
                "explicitly uncertified native selects must execute at each optimization level",
            );
        assert!(
            result.proofs.is_none(),
            "unchecked controls grant no certificate credit"
        );
        for bits in [32, 64] {
            for comparison in COMPARISONS {
                let name = function_name(bits, comparison);
                if bits == 32 {
                    // SAFETY: the source leaf has exactly this scalar C ABI;
                    // the bound function borrows result.buffer through every call.
                    let function = unsafe {
                        result
                            .buffer
                            .get_fn_bound::<unsafe extern "C" fn(i32, i32, i32, i32) -> i32>(&name)
                    }
                    .unwrap();
                    for &input in &vectors {
                        let [a, b, c, d] = input;
                        // SAFETY: the lifetime-bound handle retains the code and
                        // all four arguments match the source's I32 signature.
                        let actual =
                            unsafe { function.as_ref()(a as i32, b as i32, c as i32, d as i32) };
                        assert_eq!(
                            u64::from(actual as u32),
                            reference(comparison, bits, input),
                            "{level:?}/{name}/{input:?}"
                        );
                        calls += 1;
                    }
                } else {
                    // SAFETY: the source leaf has exactly this scalar C ABI;
                    // the bound function borrows result.buffer through every call.
                    let function = unsafe {
                        result
                            .buffer
                            .get_fn_bound::<unsafe extern "C" fn(i64, i64, i64, i64) -> i64>(&name)
                    }
                    .unwrap();
                    for &input in &vectors {
                        let [a, b, c, d] = input;
                        // SAFETY: the lifetime-bound handle retains the code and
                        // all four arguments match the source's I64 signature.
                        let actual =
                            unsafe { function.as_ref()(a as i64, b as i64, c as i64, d as i64) };
                        assert_eq!(
                            actual as u64,
                            reference(comparison, bits, input),
                            "{level:?}/{name}/{input:?}"
                        );
                        calls += 1;
                    }
                }
            }
        }
    }
    assert_eq!(calls, 48_960);
    println!(
        "SELECT_NATIVE target={TARGET} validation=Unchecked proof_credit=false functions=20 compiled_functions=80 levels=4 vectors={} calls={calls}",
        vectors.len()
    );
}
