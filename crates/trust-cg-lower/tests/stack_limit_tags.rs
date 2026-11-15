// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! U10 stack-limit request tags through the real trust-ir adapter
//! (`docs/u10-prologue-stack-limit.md` §1-§2): decoding, handler binding, and
//! every canonical-encoding refusal, before any lowering.

use trust_cg_lower::adapter::GuardCarrierArch;
use trust_cg_lower::function::{StackLimitOverflow, StackLimitRequest, StackLimitSource};
use trust_cg_lower::stack_limit::{
    STACK_LIMIT_HANDLER_TAG, STACK_LIMIT_REQUEST_TAG_BASE, STACK_LIMIT_TRAP_TAG, encode_request_tag,
};

fn request(param: u8, source: StackLimitSource) -> u32 {
    encode_request_tag(param, source).expect("representable request")
}

/// A module of `fn @f(i64, i64) -> i64` (returning its first argument) with
/// `f_proofs` on `f`, plus, when `handler_proofs` is given, a same-typed
/// handler `@h` carrying them. `conv` prefixes `f` (and `h`).
fn module_text(conv: &str, f_proofs: &[u32], handler_proofs: Option<&[u32]>) -> String {
    let proofs = |tags: &[u32]| {
        if tags.is_empty() {
            String::new()
        } else {
            let list: Vec<String> = tags.iter().map(|tag| format!("custom({tag})")).collect();
            format!("    ; #proof: {}\n", list.join(", "))
        }
    };
    let mut text = String::from(
        "module \"u10_tags\"\n\nfuncty.0 = (i64, i64) -> (i64)\nfuncty.1 = (f64, i64) -> (i64)\n\n",
    );
    text.push_str(&format!(
        "{conv}fn @f(functy.0) {{\n{}bb0(%0: i64, %1: i64):\n    ret %0\n}}\n",
        proofs(f_proofs)
    ));
    if let Some(handler) = handler_proofs {
        text.push_str(&format!(
            "\n{conv}fn @h(functy.0) {{\n{}bb0(%0: i64, %1: i64):\n    ret %1\n}}\n",
            proofs(handler)
        ));
    }
    text
}

fn translate(text: &str, arch: GuardCarrierArch) -> Result<Vec<Option<StackLimitRequest>>, String> {
    let module = trust_ir::parser::parse_module(text).map_err(|error| format!("parse: {error}"))?;
    trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        &module,
        arch,
        trust_cg_lower::TlsDialect::default(),
        &permit_unlicensed(),
    )
    .map(|functions| {
        functions
            .into_iter()
            .map(|(function, _)| function.stack_limit)
            .collect()
    })
    .map_err(|error| error.to_string())
}

fn refusal(text: &str) -> String {
    let error = translate(text, GuardCarrierArch::AArch64).expect_err("the tags must be refused");
    assert!(
        error.contains("[TCG-STACK-LIMIT-REQUEST]"),
        "refusal must be the typed stack-limit diagnostic: {error}"
    );
    error
}

#[test]
fn trap_request_decodes_onto_the_lir_function() {
    let text = module_text(
        "",
        &[request(1, StackLimitSource::Value), STACK_LIMIT_TRAP_TAG],
        None,
    );
    let limits = translate(&text, GuardCarrierArch::AArch64).unwrap();
    assert_eq!(
        limits,
        vec![Some(StackLimitRequest {
            param: 1,
            source: StackLimitSource::Value,
            overflow: StackLimitOverflow::Trap,
        })]
    );
}

#[test]
fn handler_request_binds_the_unique_same_typed_handler() {
    let text = module_text(
        "fastcc ",
        &[request(0, StackLimitSource::Pointee { offset: 24 })],
        Some(&[STACK_LIMIT_HANDLER_TAG]),
    );
    let limits = translate(&text, GuardCarrierArch::AArch64).unwrap();
    assert_eq!(
        limits,
        vec![
            Some(StackLimitRequest {
                param: 0,
                source: StackLimitSource::Pointee { offset: 24 },
                overflow: StackLimitOverflow::Handler {
                    symbol: "h".to_string(),
                },
            }),
            // The handler itself requests nothing.
            None,
        ]
    );
}

#[test]
fn untagged_module_carries_no_request() {
    let text = module_text("", &[], None);
    assert_eq!(
        translate(&text, GuardCarrierArch::AArch64).unwrap(),
        vec![None]
    );
}

#[test]
fn non_canonical_and_conflicting_tags_are_refused() {
    let value = request(0, StackLimitSource::Value);
    // Kind 0 (Value) with a nonzero offset field.
    let error = refusal(&module_text(
        "",
        &[STACK_LIMIT_REQUEST_TAG_BASE | 3, STACK_LIMIT_TRAP_TAG],
        None,
    ));
    assert!(error.contains("nonzero offset"), "{error}");
    // Two request tags, duplicate or conflicting.
    for second in [value, request(1, StackLimitSource::Value)] {
        let error = refusal(&module_text(
            "",
            &[value, second, STACK_LIMIT_TRAP_TAG],
            None,
        ));
        assert!(error.contains("two request tags"), "{error}");
    }
    // A request and the handler tag on one function.
    let error = refusal(&module_text("", &[value, STACK_LIMIT_HANDLER_TAG], None));
    assert!(error.contains("both request"), "{error}");
    // Trap without a request.
    let error = refusal(&module_text("", &[STACK_LIMIT_TRAP_TAG], None));
    assert!(error.contains("needs a request"), "{error}");
    // The trap tag twice.
    let error = refusal(&module_text(
        "",
        &[value, STACK_LIMIT_TRAP_TAG, STACK_LIMIT_TRAP_TAG],
        None,
    ));
    assert!(error.contains("more than once"), "{error}");
}

#[test]
fn handler_binding_is_exact() {
    let value = request(0, StackLimitSource::Value);
    // No handler and no Trap tag.
    let error = refusal(&module_text("", &[value], None));
    assert!(error.contains("no function in the module"), "{error}");
    // Two handlers for one function type.
    let mut text = module_text("", &[value], Some(&[STACK_LIMIT_HANDLER_TAG]));
    text.push_str(&format!(
        "\nfn @h2(functy.0) {{\n    ; #proof: custom({STACK_LIMIT_HANDLER_TAG})\nbb0(%0: i64, %1: i64):\n    ret %0\n}}\n"
    ));
    let error = refusal(&text);
    assert!(error.contains("more than one overflow handler"), "{error}");
    // A handler of another function type does not bind.
    let mut text = module_text("", &[value], None);
    text.push_str(&format!(
        "\nfn @h_other(functy.1) {{\n    ; #proof: custom({STACK_LIMIT_HANDLER_TAG})\nbb0(%0: f64, %1: i64):\n    ret %1\n}}\n"
    ));
    let error = refusal(&text);
    assert!(error.contains("no function in the module"), "{error}");
}

#[test]
fn limit_parameter_and_convention_are_checked() {
    // A parameter index the function does not have.
    let error = refusal(&module_text(
        "",
        &[request(2, StackLimitSource::Value), STACK_LIMIT_TRAP_TAG],
        None,
    ));
    assert!(error.contains("parameter 2"), "{error}");
    // An f64 parameter is not one 64-bit integer value.
    let text = format!(
        "module \"u10_fp\"\n\nfuncty.0 = (f64, i64) -> (i64)\n\nfn @f(functy.0) {{\n    ; #proof: custom({}), custom({STACK_LIMIT_TRAP_TAG})\nbb0(%0: f64, %1: i64):\n    ret %1\n}}\n",
        request(0, StackLimitSource::Value)
    );
    let error = refusal(&text);
    assert!(error.contains("lowers to F64"), "{error}");
    // Swift is outside v1.
    let error = refusal(&module_text(
        "swiftcc ",
        &[request(0, StackLimitSource::Value), STACK_LIMIT_TRAP_TAG],
        None,
    ));
    assert!(error.contains("calling convention"), "{error}");
}

#[test]
fn backends_without_the_check_refuse_the_request() {
    let text = module_text(
        "",
        &[request(0, StackLimitSource::Value), STACK_LIMIT_TRAP_TAG],
        None,
    );
    for arch in [GuardCarrierArch::X86_64, GuardCarrierArch::Riscv64] {
        let error = translate(&text, arch).expect_err("no stack-limit lowering");
        assert!(
            error.contains("[TCG-STACK-LIMIT-REQUEST]") && error.contains("AArch64 only"),
            "{arch:?}: {error}"
        );
    }
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes (or is refused) because the license silently refused it.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
