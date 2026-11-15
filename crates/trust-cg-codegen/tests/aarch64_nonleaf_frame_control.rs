// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! A captured nonleaf wrapper cannot borrow the leaf frame's proof authority.
//! Raw-body permission admits this diagnostic input, not its proof promotion.

use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::TargetSpec;
use trust_cg_codegen::{CompileError, Compiler, CompilerConfig};

fn compiler(emit_proofs: bool) -> Compiler {
    Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level: OptLevel::O0,
            emit_proofs,
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
}

fn assert_call_requires_evidence(bytes: &[u8]) {
    let module = trust_ir::binary::deserialize_module(bytes)
        .expect("decode the unchanged compiler-captured module");
    let diagnostic = compiler(false)
        .compile(&module)
        .expect("the same original input must pass diagnostic admission and lowering");
    assert!(!diagnostic.object_code.is_empty());

    let error = compiler(true)
        .compile(&module)
        .expect_err("a call without bound callee evidence must not inherit a leaf frame proof");
    let CompileError::ProofPromotionRejected { reason, .. } = error else {
        panic!("expected a proof-promotion refusal, not another admission failure: {error}");
    };
    assert!(
        reason.contains("AArch64::Bl"),
        "the actual call must remain unproved: {reason}"
    );
}

#[test]
fn captured_nonleaf_wrapper_cannot_borrow_leaf_frame_authority() {
    assert_call_requires_evidence(include_bytes!(
        "fixtures/aarch64_nonleaf_frame/main.trust_irbin"
    ));
}

#[test]
fn captured_lang_start_cannot_borrow_leaf_frame_authority() {
    assert_call_requires_evidence(include_bytes!(
        "fixtures/aarch64_nonleaf_frame/lang_start.trust_irbin"
    ));
}
