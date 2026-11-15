// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Execute the unchanged captured TY Second predicate on AArch64/macOS.
//! The compatibility compiler is explicitly Unchecked and emits no proofs.
//! Concrete pending-query evaluation and native results are separate tests,
//! not machine correspondence, independent replay, a private-frame proof or
//! caller permission derived from Ptr. Actual live arrays supply these calls.
//! Literal word 9 is the original configured source's integer one; other
//! contents exercise the retained unit ABI, not different TLA+ source literals.

use super::ty_tests::{case, instantiate, targeted};
use super::*;
use std::collections::HashMap;
use trust_cg_codegen::CoreHostJitTarget;
use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;
use trust_ir::{CallingConv, Linkage, Ty};

type Predicate = unsafe extern "C" fn(*const u64, *const u64, *const u64, *const u64) -> u64;

const TRUE: u64 = 1 << 32;
const ERROR: u64 = (3 << 32) | 1;
const FALLBACK: u64 = (3 << 32) | 4;

fn integer(value: i64) -> u64 {
    (value as u64).wrapping_shl(3) | 1
}

fn samples() -> Vec<(u64, u64, u64)> {
    let mut cases = vec![
        (integer(i64::from(i32::MIN)), 9, TRUE),
        (integer(i64::from(i32::MIN) + 1), 9, TRUE),
        (integer(-1), 9, TRUE),
        (integer(0), 9, TRUE),
        (integer(1), 9, 0),
        (integer(2), 9, 0),
        (integer(i64::from(i32::MAX) - 1), 9, 0),
        (integer(i64::from(i32::MAX)), 9, 0),
        (integer(0), integer(-1), 0),
        (integer(0), integer(0), 0),
        (integer(0), integer(i64::from(i32::MAX)), TRUE),
        (
            integer(i64::from(i32::MIN)),
            integer(i64::from(i32::MIN)),
            0,
        ),
        (
            integer(i64::from(i32::MAX)),
            integer(i64::from(i32::MAX)),
            0,
        ),
    ];
    for value in [
        i64::from(i32::MIN) - 1,
        i64::from(i32::MAX) + 1,
        -(1i64 << 60),
        (1i64 << 60) - 1,
    ] {
        cases.push((integer(value), 9, ERROR));
        cases.push((integer(0), integer(value), ERROR));
    }
    // Tag 4 has fallback precedence even when the other operand has an
    // invalid integer tag. Every other noninteger tag produces unit-3 error.
    for tag in [0, 2, 3, 4, 5, 6, 7] {
        let expected = if tag == 4 { FALLBACK } else { ERROR };
        cases.push((tag, 9, expected));
        cases.push((1, tag, expected));
    }
    cases.extend([
        (4, 2, FALLBACK),
        (2, 4, FALLBACK),
        (4, integer(i64::from(i32::MAX) + 1), FALLBACK),
        (integer(i64::from(i32::MIN) - 1), 4, FALLBACK),
        (u64::MAX - 3, 2, FALLBACK),
        (u64::MAX, 9, ERROR),
    ]);
    cases
}

#[derive(Clone, Copy, Debug)]
enum Aliases {
    Separate,
    ParentInContext,
    UnusedInContext,
    UnusedInParent,
}

#[test]
fn unchecked_mac_actual_ty_read_only_predicate_preserves_full_status_and_aliases() {
    let module = targeted();
    let source = &module.functions[0];
    let signature = &module.func_types[source.ty.index() as usize];
    assert_eq!(signature.params, [Ty::Ptr, Ty::Ptr, Ty::Ptr, Ty::Ptr]);
    assert_eq!(signature.returns, [Ty::U64]);
    assert!(!signature.is_vararg);
    assert_eq!(source.calling_conv, CallingConv::C);
    assert_eq!(source.linkage, Linkage::Internal);
    assert_eq!(source.name, "tyw1_u3");
    let original = serde_json::to_value(&module).unwrap();

    // BOTH observations below retain this exact host-bound original module.
    // Pending queries do not acquire native/Checked credit when execution
    // agrees, and this public compatibility compile is not Core admission.
    let (lowering, _proof_context) = trust_cg_lower::translate_function_with_license(
        source,
        &module,
        &crate::license_test_support::permit_unlicensed(),
    )
    .unwrap();
    let queries = bind_read_only_source(&module, 0, &lowering).unwrap();
    assert!(std::ptr::eq(queries.module(), &module));
    assert!(std::ptr::eq(queries.source(), source));
    assert!(std::ptr::eq(queries.lir(), &lowering));
    assert_eq!(queries.read_requirements().len(), 3);
    assert_eq!(queries.lowering_reads().len(), 3);
    assert_eq!(queries.load_obligations().len(), 3);
    let host = CoreHostJitTarget::detect().expect("exact supported executing host");
    assert_eq!(
        module.target_info.as_ref(),
        Some(host.trust_ir_target_info())
    );

    let samples = samples();
    let mut compiled = 0;
    let mut calls = 0;
    for level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
        let compiler = Compiler::new_for_target_spec(
            CompilerConfig {
                opt_level: level,
                emit_proofs: false,
                ..CompilerConfig::for_host_jit_unchecked()
            },
            host.target_spec(),
        )
        .with_codegen_license(crate::license_test_support::permit_unlicensed());
        assert!(!compiler.config().emit_proofs);
        assert!(compiler.config().jit_validation_mode().is_unchecked());
        let result = compiler
            .compile_module_to_jit(&module, &HashMap::new())
            .unwrap_or_else(|error| panic!("UNCHECKED original TY predicate {level:?}: {error}"));
        assert_eq!(result.metrics.function_count, 1);
        assert!(!result.buffer.code_slice().is_empty());
        assert_eq!(serde_json::to_value(&module).unwrap(), original);
        // SAFETY: the retained original signature is exactly four Ptr C
        // parameters and a U64 result. Lookup is low-level compatibility,
        // not product dispatch; the wrapper stays borrowed from this buffer.
        let function = unsafe {
            result
                .buffer
                .get_fn_bound::<Predicate>(&source.name)
                .unwrap()
        };
        compiled += 1;
        for &(state, literal, expected) in &samples {
            for aliases in [
                Aliases::Separate,
                Aliases::ParentInContext,
                Aliases::UnusedInContext,
                Aliases::UnusedInParent,
            ] {
                // Mutable backing storage permits observation of accidental
                // writes without manufacturing a caller readonly/noalias claim.
                // Every pointer passed below addresses live initialized u64s.
                let mut pool = [0x0123_4567_89ab_cdef, 9, 2, literal];
                let pool_ptr = pool.as_mut_ptr().cast_const();
                let mut ctx = [state, pool_ptr as u64];
                let mut parent = [state];
                let mut next = [0x7654_3210_fedc_ba98];
                let mut scratch = [0xf0e1_d2c3_b4a5_9687];
                let ctx_ptr = ctx.as_mut_ptr().cast_const();
                let separate_parent = parent.as_mut_ptr().cast_const();
                let parent_ptr = if matches!(aliases, Aliases::ParentInContext) {
                    ctx_ptr
                } else {
                    separate_parent
                };
                let (next_ptr, scratch_ptr) = match aliases {
                    Aliases::Separate => (
                        next.as_mut_ptr().cast_const(),
                        scratch.as_mut_ptr().cast_const(),
                    ),
                    Aliases::ParentInContext | Aliases::UnusedInParent => (parent_ptr, parent_ptr),
                    Aliases::UnusedInContext => (ctx_ptr, ctx_ptr),
                };
                let snapshot = (pool, ctx, parent, next, scratch);
                let (memory, mut env) = case(
                    ctx_ptr as u64,
                    parent_ptr as u64,
                    pool_ptr as u64,
                    state,
                    literal,
                );
                env.insert("abi_x2".into(), next_ptr as u64);
                env.insert("abi_x3".into(), scratch_ptr as u64);
                let returned = queries.return_obligation();
                for condition in &returned.preconditions {
                    assert!(instantiate(condition, &memory, &env).as_bool());
                }
                assert_eq!(
                    instantiate(&returned.trust_ir_expr, &memory, &env).as_u64(),
                    expected,
                    "original Core {state:#x}/{literal:#x}/{aliases:?}"
                );
                assert_eq!(
                    instantiate(&returned.aarch64_expr, &memory, &env).as_u64(),
                    expected,
                    "actual LIR {state:#x}/{literal:#x}/{aliases:?}"
                );
                for query in queries.load_obligations() {
                    assert_eq!(
                        instantiate(&query.trust_ir_expr, &memory, &env),
                        instantiate(&query.aarch64_expr, &memory, &env)
                    );
                }
                // SAFETY: ctx owns two aligned words; ctx+8 contains the
                // pointer to four live aligned pool words (read at pool+24).
                // parent owns at least one aligned word, including when it
                // aliases ctx. next/scratch point to live words; the original
                // body does not access them. All owners and the code buffer
                // stay alive until this synchronous call returns.
                let actual =
                    unsafe { function.as_ref()(ctx_ptr, parent_ptr, next_ptr, scratch_ptr) };
                assert_eq!(
                    actual, expected,
                    "UNCHECKED native {level:?}/{state:#x}/{literal:#x}/{aliases:?}"
                );
                assert_eq!((pool, ctx, parent, next, scratch), snapshot);
                calls += 1;
            }
        }
    }
    assert_eq!(compiled, 4);
    assert_eq!(calls, samples.len() * 4 * 4);
    println!(
        "TY_ORIGINAL_READ_ONLY_NATIVE compiled={compiled} calls={calls} original_linkage=Internal full_status=true parent_ctx_alias=true scratch_alias=true validation=Unchecked emit_proofs=false independent_replay=false machine_correspondence=false private_frame_proof=false"
    );
}

#[test]
fn scalar_edge_projection_unchecked_macos_original_branch_executes_o0_o2() {
    type Branch = unsafe extern "C" fn(*const u64, u64) -> u64;
    let host = CoreHostJitTarget::detect().expect("actual ARM64/macOS host");
    let mut module = super::liveness_tests::original_branch_module(true);
    module.target_info = Some(host.trust_ir_target_info().clone());
    let before = serde_json::to_value(&module).unwrap();
    let (lowering, _) = trust_cg_lower::translate_function_with_license(
        &module.functions[0],
        &module,
        &crate::license_test_support::permit_unlicensed(),
    )
    .unwrap();
    let projection =
        super::scalar_edge_projection::check_scalar_block_arguments(&module, 0, &lowering).unwrap();
    assert_eq!(projection.transports().len(), 2);
    let queries = bind_read_only_source(&module, 0, &lowering).unwrap();
    assert_eq!(queries.read_requirements().len(), 2);
    let mut calls = 0;
    for level in [OptLevel::O0, OptLevel::O2] {
        let compiler = Compiler::new_for_target_spec(
            CompilerConfig {
                opt_level: level,
                emit_proofs: false,
                ..CompilerConfig::for_host_jit_unchecked()
            },
            host.target_spec(),
        )
        .with_codegen_license(crate::license_test_support::permit_unlicensed());
        assert!(compiler.config().jit_validation_mode().is_unchecked());
        let result = compiler
            .compile_module_to_jit(&module, &HashMap::new())
            .unwrap();
        assert_eq!(result.metrics.function_count, 1);
        assert!(!result.buffer.code_slice().is_empty());
        // SAFETY: exact retained C signature is Ptr,U64 -> U64; each call's
        // pointer addresses a live initialized u64, held through this buffer.
        let function = unsafe {
            result
                .buffer
                .get_fn_bound::<Branch>(&module.functions[0].name)
                .unwrap()
        };
        for value in [0, 7, 23, u64::MAX] {
            for condition in [0, 1, u64::MAX] {
                let mut memory = [value];
                let snapshot = memory;
                assert_eq!(
                    unsafe { function.as_ref()(memory.as_mut_ptr().cast_const(), condition) },
                    if condition == 0 { value } else { 7 }
                );
                assert_eq!(memory, snapshot);
                calls += 1;
            }
        }
        assert_eq!(serde_json::to_value(&module).unwrap(), before);
    }
    assert_eq!(calls, 24);
    println!(
        "SCALAR_EDGE_ORIGINAL_NATIVE compiled=2 calls={calls} validation=Unchecked emit_proofs=false source_unchanged=true machine_correspondence=false body_proof=false native_credit=false"
    );
}
