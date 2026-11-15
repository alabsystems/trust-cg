// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#[path = "../../trust-cg-lower/tests/common/runtime_closure.rs"]
mod fixture;

use trust_cg_codegen::{CodegenLicensePolicy, UnlicensedBodyPolicy, wasm};

#[test]
fn runtime_closure_refuses_wasm_module_and_object_without_emitting_bytes() {
    let permit = CodegenLicensePolicy::default().with_unlicensed(UnlicensedBodyPolicy::Permit);
    let mut module = fixture::runtime_closure_module(true);
    module.target_info = Some(wasm::wasm32_target_info());
    assert!(trust_ir_build::validate_module(&module).is_empty());
    for result in [
        wasm::compile_module_with_license(&module, &permit).map(drop),
        wasm::compile_object_with_license(&module, &permit).map(drop),
    ] {
        let error = result.unwrap_err();
        let wasm::WasmLowerError::ContractSurface(detail) = error else {
            panic!("the shared closure floor must refuse before emission: {error:?}");
        };
        assert!(detail.contains("Inst::MakeClosure"), "{detail}");
        assert!(detail.contains("runtime closure ABI"), "{detail}");
    }
    let mut scalar = fixture::runtime_closure_module(false);
    scalar.target_info = Some(wasm::wasm32_target_info());
    wasm::compile_module_with_license(&scalar, &permit).unwrap();
}
