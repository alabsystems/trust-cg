// trust-cg-codegen/tests/aarch64_compiler_jit_sealed_link.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The compiler's own AArch64 JIT (`Compiler::compile_module_to_jit`) links
//! its prepared functions SEALED: each carries the final-stream check its
//! preparation ran and passed, and the link does not run that identical check
//! a second time — the raw lane's `compile_raw_checked` contract
//! (`aarch64_checked_functions.rs`), now on the typed JIT every embedding
//! runtime reaches through `Compiler` (ay's JIT kernels among them).
//!
//! This binary holds ONE test because it counts the frame net's process-wide
//! coverage counter: with `TCG_NO_SEALED_JIT_LINK` the link runs the net once
//! more per function than the default, and the published image is the same.
//! AArch64 hosts only (the JIT runs natively).

#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::Target;
use trust_cg_verify::post_ra_spill_slots::frame_coverage;
use trust_ir::ty::FuncTy;
use trust_ir::value::{BlockId, FuncId, ValueId};
use trust_ir::{BinOp, Block, Constant, Function, Inst, InstrNode, Module, Ty};

const LANES: usize = 24;

/// `caller(p) = helper(v0) + sum(v_i)` with every `v_i = p[i] * k_i` live
/// across the call: a framed, spilling function, and its callee.
fn spilling_module() -> Module {
    let mut next = 0u32;
    let mut fresh = || {
        let value = ValueId(next);
        next += 1;
        value
    };
    let mut body = Vec::new();
    let input = fresh();
    let mut emit = |body: &mut Vec<InstrNode>, inst: Inst| {
        let result = fresh();
        body.push(InstrNode::new(inst).with_result(result));
        result
    };
    let mut live = Vec::with_capacity(LANES);
    for lane in 0..LANES {
        let index = emit(
            &mut body,
            Inst::Const {
                ty: Ty::I64,
                value: Constant::i64(lane as i64),
            },
        );
        let address = emit(
            &mut body,
            Inst::GEP {
                pointee_ty: Ty::I64,
                base: input,
                indices: vec![index],
                inbounds: false,
            },
        );
        let loaded = emit(
            &mut body,
            Inst::Load {
                ty: Ty::I64,
                ptr: address,
                volatile: false,
                align: None,
            },
        );
        let factor = emit(
            &mut body,
            Inst::Const {
                ty: Ty::I64,
                value: Constant::i64((lane as i64 % 7) + 2),
            },
        );
        live.push(emit(
            &mut body,
            Inst::BinOp {
                op: BinOp::Mul,
                ty: Ty::I64,
                lhs: loaded,
                rhs: factor,
            },
        ));
    }
    let mut acc = emit(
        &mut body,
        Inst::Call {
            callee: FuncId(1),
            args: vec![live[0]],
        },
    );
    for value in live {
        acc = emit(
            &mut body,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: acc,
                rhs: value,
            },
        );
    }
    body.push(InstrNode::new(Inst::Return { values: vec![acc] }));

    let mut module = Module::new("aarch64_compiler_jit_sealed_link");
    let caller_ty = module
        .add_func_type(FuncTy {
            params: vec![Ty::Ptr],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let helper_ty = module
        .add_func_type(FuncTy {
            params: vec![Ty::I64],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut caller = Function::new(FuncId(0), "checked_caller", caller_ty, BlockId(0));
    let mut block = Block::new(BlockId(0)).with_param(input, Ty::Ptr);
    block.body = body;
    caller.blocks = vec![block];
    module
        .try_add_function(caller)
        .expect("Module::try_add_function: test fixture");

    let param = ValueId(0);
    let helper_body = vec![
        InstrNode::new(Inst::Const {
            ty: Ty::I64,
            value: Constant::i64(1),
        })
        .with_result(ValueId(1)),
        InstrNode::new(Inst::BinOp {
            op: BinOp::Add,
            ty: Ty::I64,
            lhs: param,
            rhs: ValueId(1),
        })
        .with_result(ValueId(2)),
        InstrNode::new(Inst::Return {
            values: vec![ValueId(2)],
        }),
    ];
    let mut helper = Function::new(FuncId(1), "checked_helper", helper_ty, BlockId(0));
    let mut helper_block = Block::new(BlockId(0)).with_param(param, Ty::I64);
    helper_block.body = helper_body;
    helper.blocks = vec![helper_block];
    module
        .try_add_function(helper)
        .expect("Module::try_add_function: test fixture");
    module
}

fn analyzed() -> u64 {
    frame_coverage().analyzed + frame_coverage().declined
}

#[test]
fn compiler_jit_links_sealed_functions_to_the_same_image_and_checks_once() {
    let module = spilling_module();
    let externs: HashMap<String, *const u8> = HashMap::new();
    let functions = module.functions.len() as u64;
    let input: Vec<i64> = (0..LANES as i64).map(|lane| lane * 3 - 11).collect();
    let expected: i64 = {
        let live: Vec<i64> = input
            .iter()
            .enumerate()
            .map(|(lane, value)| value * ((lane as i64 % 7) + 2))
            .collect();
        (live[0] + 1) + live.iter().sum::<i64>()
    };
    for opt_level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
        let mut config = CompilerConfig::jit_fast(Target::Aarch64);
        config.opt_level = opt_level;
        let compiler = Compiler::new(config).with_codegen_license(permit_unlicensed());

        let before = analyzed();
        let sealed = compiler
            .compile_module_to_jit(&module, &externs)
            .expect("sealed JIT compile");
        let sealed_runs = analyzed() - before;

        let before = analyzed();
        let unsealed = trust_cg_codegen::env_lock::with_env_overrides(
            &[(trust_cg_codegen::compiler::SEALED_JIT_LINK_KILL_SWITCH, "1")],
            || {
                compiler
                    .compile_module_to_jit(&module, &externs)
                    .expect("unsealed JIT compile")
            },
        );
        let unsealed_runs = analyzed() - before;

        // The link skips exactly one frame-net run per function, and only
        // that: the preparation's own run is unchanged.
        assert_eq!(
            unsealed_runs,
            sealed_runs + functions,
            "{opt_level:?}: sealed {sealed_runs} vs unsealed {unsealed_runs} net runs"
        );
        assert_eq!(
            sealed.buffer.code_slice(),
            unsealed.buffer.code_slice(),
            "{opt_level:?}: the sealed link publishes the unsealed link's code"
        );
        assert_eq!(
            sealed.buffer.published_image_sha256(),
            unsealed.buffer.published_image_sha256(),
            "{opt_level:?}: the complete published image is the same"
        );

        for result in [&sealed, &unsealed] {
            let entry = unsafe {
                result
                    .buffer
                    .get_fn_bound::<extern "C" fn(*const i64) -> i64>("checked_caller")
                    .expect("checked_caller")
            };
            assert_eq!((*entry.as_ref())(input.as_ptr()), expected, "{opt_level:?}");
        }
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
