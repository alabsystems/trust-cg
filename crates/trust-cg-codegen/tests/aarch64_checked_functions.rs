// trust-cg-codegen/tests/aarch64_checked_functions.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Sealed prepared functions (`Pipeline::prepare_function_checked`,
//! `JitCompiler::compile_raw_checked*`).
//!
//! A sealed function is the prepared function plus the final-stream check its
//! preparation ran and passed; the raw JIT then skips re-running that
//! identical check at link. This binary holds ONE test because it counts the
//! frame net's process-wide coverage counter: preparation and link each run
//! the net once on the plain path, the sealed path runs it once, and a link
//! whose check differs from the sealed one (a diagnostic mode changed between
//! preparation and link) runs it again. Every lane must produce the same
//! function and the same relocatable image bytes.
//!
//! The raw JIT is AArch64-only, so the test runs on AArch64 hosts.

#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;

use trust_cg_codegen::CheckedAarch64Functions;
use trust_cg_codegen::jit::{JitCompiler, JitConfig};
use trust_cg_codegen::pipeline::{OptLevel, Pipeline, PipelineConfig};
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

    let mut module = Module::new("aarch64_checked_functions");
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
fn sealed_functions_link_to_the_same_bytes_and_skip_only_an_identical_check() {
    let module = spilling_module();
    let lir = trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        &module,
        trust_cg_lower::GuardCarrierArch::default(),
        trust_cg_lower::TlsDialect::default(),
        &permit_unlicensed(),
    )
    .expect("fixture lowers");
    let externs: HashMap<String, *const u8> = HashMap::new();
    for opt_level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
        let pipeline = Pipeline::new(PipelineConfig {
            opt_level,
            ..PipelineConfig::for_host_aarch64()
        });
        let jit = JitCompiler::new(JitConfig {
            opt_level,
            verify: false,
            ..JitConfig::default()
        });

        // Plain: preparation and link each run the frame net once per function.
        let before = analyzed();
        let plain: Vec<_> = lir
            .iter()
            .map(|(func, ctx)| {
                pipeline
                    .prepare_function_with_metrics(func, Some(ctx))
                    .expect("prepares")
                    .0
            })
            .collect();
        let (_buffer, plain_image) = jit
            .compile_raw_relocatable(&plain, &externs)
            .expect("plain link");
        let plain_image = plain_image.expect("relocatable");
        assert_eq!(
            analyzed() - before,
            2 * lir.len() as u64,
            "{opt_level:?} plain"
        );

        // Sealed: the link does not re-run the check preparation passed.
        let before = analyzed();
        let sealed: CheckedAarch64Functions = lir
            .iter()
            .map(|(func, ctx)| {
                pipeline
                    .prepare_function_checked(func, Some(ctx))
                    .expect("prepares")
                    .0
            })
            .collect();
        let (_buffer, sealed_image) = jit
            .compile_raw_checked_relocatable(&sealed, &externs)
            .expect("sealed link");
        let sealed_image = sealed_image.expect("relocatable");
        assert_eq!(
            analyzed() - before,
            lir.len() as u64,
            "{opt_level:?} sealed"
        );

        assert_eq!(
            format!("{:?}", sealed.functions()),
            format!("{plain:?}"),
            "{opt_level:?}: the sealed functions are the prepared functions"
        );
        assert_eq!(sealed_image.image_sha256(), plain_image.image_sha256());
        assert_eq!(sealed_image.to_bytes(), plain_image.to_bytes());

        // A link whose check differs (the frame net's diagnostic mode changed
        // since preparation) checks the stream again, and still emits the
        // same bytes.
        let before = analyzed();
        let rechecked_image = trust_cg_codegen::env_lock::with_env_overrides(
            &[("TCG_AARCH64_POST_RA_SPILL_SLOTS", "warn")],
            || {
                jit.compile_raw_checked_relocatable(&sealed, &externs)
                    .expect("re-checked link")
                    .1
            },
        );
        assert_eq!(
            analyzed() - before,
            lir.len() as u64,
            "{opt_level:?} mode change"
        );
        assert_eq!(
            rechecked_image.expect("relocatable").to_bytes(),
            plain_image.to_bytes()
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
