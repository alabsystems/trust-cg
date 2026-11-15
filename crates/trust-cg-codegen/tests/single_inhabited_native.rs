// Copyright 2026 Andrew Yates. Apache-2.0.
//! Actual reference execution and native calls; no source or proof-grade claim.
#![cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
#[path = "../../trust-cg-lower/tests/common/single_inhabited.rs"]
mod fixture;
use std::collections::HashMap;
use trust_cg_codegen::{
    CodegenLicensePolicy, Compiler, CompilerConfig, CoreHostJitTarget, Target,
    UnlicensedBodyPolicy, pipeline::OptLevel,
};
use trust_ir::{FuncId, interpret::Interpreter};

#[test]
fn original_selected_zero_and_nonzero_constant_and_store_load_execute_o0_through_o3() {
    let host = CoreHostJitTarget::detect().expect("required native host");
    for active in 0..2 {
        for memory in [false, true] {
            let module = fixture::module(active, memory);
            assert!(trust_ir_build::validate_module(&module).is_empty());
            let reference = Interpreter::with_module(&module)
                .execute_func(FuncId::new(0), [])
                .unwrap();
            assert_eq!(reference.host_calls, 0);
            assert_eq!(reference.returns.len(), 1);
            assert_eq!(
                reference.returns[0].as_int().unwrap().as_unsigned(),
                u128::from(fixture::expected(active))
            );
            for opt in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
                let mut config = CompilerConfig::jit_fast(Target::host());
                config.opt_level = opt;
                let compiler = Compiler::new_for_target_spec(config, host.target_spec())
                    .with_codegen_license(
                        CodegenLicensePolicy::default()
                            .with_unlicensed(UnlicensedBodyPolicy::Permit),
                    );
                let output = compiler
                    .compile_module_to_jit(&module, &HashMap::new())
                    .unwrap_or_else(|error| {
                        panic!("selected={active}, memory={memory}, {opt:?}: {error}")
                    });
                // The complete validated function takes no arguments and returns
                // exactly one u64. The executable owner outlives this call.
                let function =
                    unsafe { output.buffer.get_fn_bound::<extern "C" fn() -> u64>("run") }.unwrap();
                assert_eq!(
                    function.as_ref()(),
                    fixture::expected(active),
                    "selected={active}, memory={memory}, {opt:?}"
                );
            }
        }
    }
}
