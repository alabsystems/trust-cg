// Production-path coverage that producer-owned alignment claims remain
// report-only until an independent, obligation-bound replay capability exists.

use trust_cg_codegen::compiler::{CompilationResult, Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::{OptLevel, ProofOptimizationCertificateCitation};
use trust_cg_codegen::target::TargetSpec;
use trust_ir::{ProofAnnotation, Ty, ValueId};
use trust_ir_build::{FunctionBuilder, ModuleBuilder};

const ENTRY_NAME: &str = "trust_ir_aligned_pair_production";

fn store_slot(fb: &mut FunctionBuilder<'_>, out: ValueId, slot: u64, value: ValueId) {
    let slot = fb.iconst(Ty::U64, i128::from(slot));
    let ptr = fb.gep(Ty::U64, out, vec![slot]);
    fb.store(Ty::U64, ptr, value);
}

fn load_slot_aligned(fb: &mut FunctionBuilder<'_>, out: ValueId, slot: u64, align: u64) -> ValueId {
    let slot = fb.iconst(Ty::U64, i128::from(slot));
    let ptr = fb.gep(Ty::U64, out, vec![slot]);
    fb.load_aligned(Ty::U64, ptr, align)
}

fn aligned_pair_module() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("trust_ir_aligned_pair_production");
    let entry_ty = mb.add_func_type(vec![Ty::Ptr, Ty::U64, Ty::U64], vec![Ty::U64]);

    {
        let mut fb = mb.function(ENTRY_NAME, entry_ty);
        let entry = fb.create_block();
        let out = fb.add_block_param(entry, Ty::Ptr);
        let lo = fb.add_block_param(entry, Ty::U64);
        let hi = fb.add_block_param(entry, Ty::U64);

        fb.switch_to_block(entry);
        fb.store_proven(Ty::U64, out, lo, vec![ProofAnnotation::Aligned(16)]);
        store_slot(&mut fb, out, 1, hi);
        fb.ret(vec![lo]);

        fb.build();
    }

    mb.build()
}

fn aligned_pair_citations(
    certs: &[ProofOptimizationCertificateCitation],
) -> Vec<&ProofOptimizationCertificateCitation> {
    applied_aligned_pair_citations(certs, ENTRY_NAME, 16)
}

fn applied_aligned_pair_citations<'a>(
    certs: &'a [ProofOptimizationCertificateCitation],
    function_name: &str,
    align: u64,
) -> Vec<&'a ProofOptimizationCertificateCitation> {
    let align = align.to_string();
    certs
        .iter()
        .filter(|cert| {
            cert.function_name == function_name
                && cert.transform_name == "proof-opts.aligned.pair-combined"
                && cert.kind == "PairCombined"
                && cert.status == "applied"
                && cert.admission == "proof-facts"
                && cert.consumed_facts.iter().any(|fact| {
                    fact.name == "Aligned" && fact.payload.as_deref() == Some(align.as_str())
                })
        })
        .collect()
}

fn compile_with_opt(module: &trust_ir::Module, opt_level: OptLevel) -> CompilationResult {
    let compiler = Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level,
            parallel: false,
            ..CompilerConfig::default()
        },
        TargetSpec::parse("aarch64-unknown-linux-gnu").expect("test target spec parses"),
    );
    compiler
        .compile(module)
        .expect("production compiler pipeline should accept trust_ir aligned-pair fixture")
}

fn explicit_aligned_store_pair_module(name: &'static str, align: u64) -> trust_ir::Module {
    let mut mb = ModuleBuilder::new(name);
    let entry_ty = mb.add_func_type(vec![Ty::Ptr, Ty::U64, Ty::U64], vec![Ty::U64]);

    {
        let mut fb = mb.function(name, entry_ty);
        let entry = fb.create_block();
        let out = fb.add_block_param(entry, Ty::Ptr);
        let lo = fb.add_block_param(entry, Ty::U64);
        let hi = fb.add_block_param(entry, Ty::U64);

        fb.switch_to_block(entry);
        fb.store_aligned(Ty::U64, out, lo, align);
        store_slot(&mut fb, out, 1, hi);
        fb.ret(vec![lo]);

        fb.build();
    }

    mb.build()
}

fn explicit_aligned_load_pair_module(name: &'static str, align: u64) -> trust_ir::Module {
    let mut mb = ModuleBuilder::new(name);
    let entry_ty = mb.add_func_type(vec![Ty::Ptr], vec![Ty::U64]);

    {
        let mut fb = mb.function(name, entry_ty);
        let entry = fb.create_block();
        let out = fb.add_block_param(entry, Ty::Ptr);

        fb.switch_to_block(entry);
        let lo = fb.load_aligned(Ty::U64, out, align);
        let hi = load_slot_aligned(&mut fb, out, 1, align);
        let sum = fb.add(Ty::U64, lo, hi);
        fb.ret(vec![sum]);

        fb.build();
    }

    mb.build()
}

#[test]
fn compiler_pipeline_does_not_consume_aligned_claim_without_replay_authority() {
    let module = aligned_pair_module();
    let lowered = trust_cg_lower::adapter::translate_module(&module).expect("trust_ir lowers");
    assert_eq!(lowered.len(), 1);
    assert_eq!(
        lowered[0]
            .1
            .alignment_for(&trust_cg_lower::instructions::Value(0)),
        Some(16),
        "adapter must bind the source trust_ir Aligned(16) proof to the output pointer"
    );

    let compiler = Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level: OptLevel::O2,
            parallel: false,
            ..CompilerConfig::default()
        },
        TargetSpec::parse("aarch64-unknown-linux-gnu").expect("test target spec parses"),
    );
    let result = compiler
        .compile(&module)
        .expect("production compiler pipeline should accept aligned-pair trust_ir");

    assert!(
        !result.object_code.is_empty(),
        "compile must run through object emission, not only lowering or pass helpers"
    );
    assert_eq!(
        result.metrics.proof_optimizations.certificate_count,
        result.proof_optimization_certificates.len()
    );

    let pair_certs = aligned_pair_citations(&result.proof_optimization_certificates);
    assert!(
        pair_certs.is_empty(),
        "a public Aligned claim must not mint an applied pair-combine citation; got {:#?}",
        result.proof_optimization_certificates
    );
}

#[test]
fn compiler_pipeline_keeps_explicit_aligned_store_pair_without_replay_authority() {
    const NAME: &str = "trust_ir_explicit_aligned_store_pair";
    let module = explicit_aligned_store_pair_module(NAME, 16);
    let lowered = trust_cg_lower::adapter::translate_module(&module).expect("trust_ir lowers");
    assert_eq!(
        lowered[0]
            .1
            .alignment_for(&trust_cg_lower::instructions::Value(0)),
        None,
        "explicit Load/Store align must not masquerade as a pointer-wide ProofContext fact"
    );

    for opt_level in [OptLevel::O2, OptLevel::O3] {
        let result = compile_with_opt(&module, opt_level);
        let pair_certs =
            applied_aligned_pair_citations(&result.proof_optimization_certificates, NAME, 16);
        assert!(
            pair_certs.is_empty(),
            "constructible Store.align metadata must not drive pair combine at {opt_level:?}; got {:#?}",
            result.proof_optimization_certificates
        );
    }
}

#[test]
fn compiler_pipeline_keeps_explicit_aligned_load_pair_without_replay_authority() {
    const NAME: &str = "trust_ir_explicit_aligned_load_pair";
    let module = explicit_aligned_load_pair_module(NAME, 16);
    let lowered = trust_cg_lower::adapter::translate_module(&module).expect("trust_ir lowers");
    assert_eq!(
        lowered[0]
            .1
            .alignment_for(&trust_cg_lower::instructions::Value(0)),
        None,
        "explicit Load/Store align must remain instruction-local metadata"
    );

    for opt_level in [OptLevel::O2, OptLevel::O3] {
        let result = compile_with_opt(&module, opt_level);
        let pair_certs =
            applied_aligned_pair_citations(&result.proof_optimization_certificates, NAME, 16);
        assert!(
            pair_certs.is_empty(),
            "constructible Load.align metadata must not drive pair combine at {opt_level:?}; got {:#?}",
            result.proof_optimization_certificates
        );
    }
}

#[test]
fn compiler_pipeline_does_not_combine_weak_explicit_aligned_store_pair_at_o2_o3() {
    const NAME: &str = "trust_ir_weak_explicit_aligned_store_pair";
    let module = explicit_aligned_store_pair_module(NAME, 8);

    for opt_level in [OptLevel::O2, OptLevel::O3] {
        let result = compile_with_opt(&module, opt_level);
        let pair_certs =
            applied_aligned_pair_citations(&result.proof_optimization_certificates, NAME, 16);
        assert!(
            pair_certs.is_empty(),
            "weak explicit Store.align must not drive pair combine at {opt_level:?}; got {:#?}",
            result.proof_optimization_certificates
        );
    }
}

#[test]
fn compiler_pipeline_does_not_combine_weak_explicit_aligned_load_pair_at_o2_o3() {
    const NAME: &str = "trust_ir_weak_explicit_aligned_load_pair";
    let module = explicit_aligned_load_pair_module(NAME, 8);

    for opt_level in [OptLevel::O2, OptLevel::O3] {
        let result = compile_with_opt(&module, opt_level);
        let pair_certs =
            applied_aligned_pair_citations(&result.proof_optimization_certificates, NAME, 16);
        assert!(
            pair_certs.is_empty(),
            "weak explicit Load.align must not drive pair combine at {opt_level:?}; got {:#?}",
            result.proof_optimization_certificates
        );
    }
}
