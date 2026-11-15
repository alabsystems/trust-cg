// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Multi-result Fast calls followed by C calls must preserve unread ABI lanes.
//! This is an actual JIT diagnostic, not a caller-authored proof certificate.

#![cfg(all(
    target_arch = "aarch64",
    any(target_os = "macos", all(target_os = "linux", target_env = "gnu"))
))]

use std::collections::HashMap;
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::{Compiler, CompilerConfig, CoreHostJitTarget, Target};
use trust_ir::{BinOp, CallingConv, CastOp, Ty};
use trust_ir_build::ModuleBuilder;

#[repr(C)]
struct Pair {
    status: u64,
    value: u64,
}

extern "C" fn observe(status: u64, value: u64) -> Pair {
    Pair { status, value }
}

fn module(indirect: bool, pressure: usize) -> trust_ir::Module {
    let host = CoreHostJitTarget::detect().expect("supported native AArch64 test host");
    let mut m = ModuleBuilder::new_with_target_info(
        "aarch64_call_result_liveness",
        host.trust_ir_target_info().clone(),
    );
    let pair = m.add_struct(trust_ir::StructDef {
        origin: None,
        id: trust_ir::StructId::new(0),
        name: "Pair".into(),
        fields: ["status", "value"]
            .into_iter()
            .enumerate()
            .map(|(i, name)| trust_ir::FieldDef {
                name: name.into(),
                ty: Ty::U64,
                offset: Some(i as u64 * 8),
            })
            .collect(),
        size: Some(16),
        align: Some(8),
        repr: trust_ir::StructRepr::C,
    });
    let helper_ty = m.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::Struct(pair)]);
    let helper = m.declare_function("observe", helper_ty);
    let leaf_ty = m.add_func_type(vec![Ty::Ptr], vec![Ty::U64; 5]);
    let leaf = m.declare_function("five_lanes", leaf_ty);
    {
        let mut b = m.define_function(leaf).unwrap();
        b.set_calling_conv(CallingConv::Fast);
        let block = b.create_block();
        let input = b.add_block_param(block, Ty::Ptr);
        b.switch_to_block(block);
        let lanes = (0..5)
            .map(|i| {
                let p = b.gep_byte_offset(input, i * 8);
                b.load(Ty::U64, p)
            })
            .collect();
        b.ret(lanes);
        b.build();
    }
    let entry_ty = m.add_func_type(vec![Ty::Ptr, Ty::Ptr, Ty::Ptr], vec![Ty::U64]);
    {
        let mut b = m.function("entry", entry_ty);
        let block = b.create_block();
        let input = b.add_block_param(block, Ty::Ptr);
        let output = b.add_block_param(block, Ty::Ptr);
        let callback = b.add_block_param(block, Ty::Ptr);
        b.switch_to_block(block);
        let mut live = Vec::new();
        for i in 0..pressure {
            let p = b.gep_byte_offset(input, (i as u64 + 5) * 8);
            live.push(b.load(Ty::U64, p));
        }
        let lanes = if indirect {
            // The target is supplied by the caller, not a statically foldable
            // FnAddr, so this exercises the genuine indirect result path.
            let callback = b.cast(CastOp::PtrToPtr, Ty::Ptr, Ty::Func(leaf_ty), callback);
            b.call_indirect_results_cc::<5>(callback, leaf_ty, vec![input], CallingConv::Fast)
        } else {
            b.call_results::<5>(leaf, vec![input])
        };
        // The first returned lane is intentionally unused, as in the original
        // failing caller. Its emitted result copy may NOT overwrite lane 1.
        let observed = b.call(helper, vec![lanes[1], lanes[2]]);
        let observed_status = b.extract_field(Ty::U64, observed, 0);
        let observed_value = b.extract_field(Ty::U64, observed, 1);
        for (i, value) in [
            observed_status,
            observed_value,
            lanes[1],
            lanes[2],
            lanes[3],
            lanes[4],
        ]
        .into_iter()
        .enumerate()
        {
            let p = b.gep_byte_offset(output, i as u64 * 8);
            b.store(Ty::U64, p, value);
        }
        let mut sum = b.uconst(Ty::U64, 0);
        for value in live {
            sum = b.binop(BinOp::Add, Ty::U64, sum, value);
        }
        b.ret(vec![sum]);
        b.build();
    }
    m.build().expect("ModuleBuilder::build: test fixture")
}

fn run(indirect: bool) {
    let host = CoreHostJitTarget::detect().expect("supported native AArch64 test host");
    for opt in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
        for pressure in [0, 4, 16, 28] {
            let module = module(indirect, pressure);
            let errors = trust_ir_build::validate_module(&module);
            assert!(errors.is_empty(), "{errors:?}");
            let mut config = CompilerConfig::jit_fast(Target::Aarch64);
            config.opt_level = opt;
            let symbols = HashMap::from([("observe".to_string(), observe as *const u8)]);
            let compiled = Compiler::new_for_target_spec(config, host.target_spec())
                .with_codegen_license(permit_unlicensed())
                .compile_module_to_jit(&module, &symbols)
                .unwrap_or_else(|error| panic!("{indirect}/{opt:?}/{pressure}: {error}"));
            let entry = compiled.buffer.get_fn_ptr_bound("entry").unwrap();
            let callback = compiled.buffer.get_fn_ptr_bound("five_lanes").unwrap();
            // SAFETY: this diagnostic owns the exact native image and C entry
            // signature; Fast calls occur only inside generated code. Arrays
            // are live, correctly sized and disjoint for the entire call.
            let entry: unsafe extern "C" fn(*const u64, *mut u64, *const u8) -> u64 =
                unsafe { std::mem::transmute(entry.as_ptr()) };
            for status in [0, 71, 0x1234_5678_9abc_def0] {
                let mut input = [0u64; 33];
                for (i, value) in input.iter_mut().enumerate() {
                    *value = 0x1020_3040_5060_7080u64.wrapping_add(i as u64 * 17);
                }
                input[1] = status;
                let mut output = [u64::MAX; 6];
                let sum = unsafe { entry(input.as_ptr(), output.as_mut_ptr(), callback.as_ptr()) };
                assert_eq!(
                    output,
                    [input[1], input[2], input[1], input[2], input[3], input[4]],
                    "indirect={indirect} opt={opt:?} pressure={pressure}"
                );
                assert_eq!(
                    sum,
                    input[5..5 + pressure]
                        .iter()
                        .fold(0u64, |a, b| a.wrapping_add(*b))
                );
            }
        }
    }
}

#[test]
fn aarch64_direct_five_result_call_preserves_unread_lanes() {
    run(false);
}

#[test]
fn aarch64_indirect_five_result_call_preserves_unread_lanes() {
    run(true);
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
