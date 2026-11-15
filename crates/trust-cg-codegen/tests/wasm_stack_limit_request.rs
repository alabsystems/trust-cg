// trust-cg-codegen/tests/wasm_stack_limit_request.rs - wasm32 lanes refuse U10 stack-limit requests
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The wasm32 lane has no prologue stack-limit lowering, so a function that
//! carries a U10 stack-limit tag must be refused by name by the closed-module
//! lane AND the relocatable-object lane, never compiled without its check.
//! The untagged control compiles on both lanes.

use trust_cg_codegen::wasm;
use trust_cg_lower::function::StackLimitSource;
use trust_cg_lower::stack_limit::{STACK_LIMIT_TRAP_TAG, encode_request_tag};
use trust_ir::{Module, parser};

/// `fn @f(i64, i64) -> i64` returning its first argument, with `tags` as
/// custom proof annotations on `f`.
fn module(tags: &[u32]) -> Module {
    let proofs = if tags.is_empty() {
        String::new()
    } else {
        let list: Vec<String> = tags.iter().map(|tag| format!("custom({tag})")).collect();
        format!("    ; #proof: {}\n", list.join(", "))
    };
    let text = format!(
        "module \"u10_wasm\"\ntarget \"wasm32-unknown-unknown\" 4 little\n\n\
         functy.0 = (i64, i64) -> (i64)\n\n\
         fn @f(functy.0) {{\n{proofs}bb0(%0: i64, %1: i64):\n    ret %0\n}}\n"
    );
    parser::parse_module(&text).unwrap_or_else(|e| panic!("parse: {e}\n{text}"))
}

#[test]
fn both_wasm_lanes_refuse_a_stack_limit_request() {
    let request = encode_request_tag(0, StackLimitSource::Value).expect("representable request");
    let tagged = module(&[request, STACK_LIMIT_TRAP_TAG]);
    for (lane, result) in [
        (
            "closed module",
            wasm::compile_module_with_license(&tagged, &permit_unlicensed()),
        ),
        (
            "object",
            wasm::compile_object_with_license(&tagged, &permit_unlicensed()),
        ),
    ] {
        let error = result
            .expect_err("a stack-limit request must be refused")
            .to_string();
        assert!(
            error.contains("[TCG-STACK-LIMIT-REQUEST]") && error.contains("AArch64 only"),
            "{lane}: {error}"
        );
    }
}

#[test]
fn the_untagged_control_compiles_on_both_lanes() {
    let plain = module(&[]);
    wasm::compile_module_with_license(&plain, &permit_unlicensed()).expect("closed module control");
    wasm::compile_object_with_license(&plain, &permit_unlicensed()).expect("object control");
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes (or is refused) because the license silently refused it.
fn permit_unlicensed() -> trust_cg_codegen::CodegenLicensePolicy {
    trust_cg_codegen::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit)
}
