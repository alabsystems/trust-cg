// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
//! The installed-artifact replay of the verifying AArch64 JIT (ledger
//! `L11-P2`) through the public API, on this host's own MAP_JIT publication.
//!
//! * A verifying raw publication (`JitConfig::verify`) with an internal tail
//!   call and an external one through a veneer carries the replay record:
//!   every function's installed words compared with its certificate-bound
//!   words, both branch sites decoded and re-targeted at the mapped address,
//!   the veneer's two words and literal checked; the image the replay
//!   re-read is the one the seal hashed, and every function runs.
//! * A non-verifying publication carries none (the fast path is unchanged).
//! * The proof-required compiler route (`AlwaysVerify`, and a
//!   `CachedVerified` warm hit that does not re-run the verifier) publishes
//!   an exhaustively checked `zext i8 -> i32` only with a replay covering it.
//!
//! The tamper controls (a byte flipped, a branch re-encoded to a valid wrong
//! target, a veneer literal moved, each after the seal and the cache walk but
//! before hand-out) need the publisher's test-only hook and are unit tests of
//! the crate (`jit::jit_installed_replay_tests`). Execution here is testing,
//! not proof.
#![cfg(all(target_arch = "aarch64", feature = "verify"))]
// Test fixture: the big `Err` is the compiler's own public error type.
#![allow(clippy::result_large_err)]

use std::collections::HashMap;
use std::sync::Arc;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig, JitValidationMode};
use trust_cg_codegen::env_lock;
use trust_cg_codegen::jit::{ExecutableBuffer, JitCompiler, JitConfig};
use trust_cg_codegen::jit_cert::JitCertCache;
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::Target;
use trust_cg_ir::aarch64_regs::X0;
use trust_cg_ir::{AArch64Opcode, MachFunction, MachInst, MachOperand, Signature, Type};
use trust_ir::inst::CastOp;
use trust_ir::{Block, BlockId, FuncId, FuncTy, Function, Inst, InstrNode, Module, Ty, ValueId};

extern "C" fn installed_replay_floor_host(value: i64) -> i64 {
    value.wrapping_mul(3)
}

const HOST: &str = "installed_replay_floor_host";

/// `callee: ADD X0, X0, #1; RET`, `tail_internal: B callee`,
/// `tail_external: B <HOST>`.
fn raw_functions() -> Vec<MachFunction> {
    let signature = || Signature::new(vec![Type::I64], vec![Type::I64]);
    let mut callee = MachFunction::new("callee".to_owned(), signature());
    let entry = callee.entry;
    let add = callee.push_inst(MachInst::new(
        AArch64Opcode::AddRI,
        vec![
            MachOperand::PReg(X0),
            MachOperand::PReg(X0),
            MachOperand::Imm(1),
        ],
    ));
    callee.append_inst(entry, add);
    let ret = callee.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]).with_implicit_uses(&[X0]));
    callee.append_inst(entry, ret);
    let tail = |name: &str, target: &str| {
        let mut function = MachFunction::new(name.to_owned(), signature());
        let entry = function.entry;
        let branch = function.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Symbol(target.to_owned())],
        ));
        function.append_inst(entry, branch);
        function
    };
    vec![
        callee,
        tail("tail_internal", "callee"),
        tail("tail_external", HOST),
    ]
}

fn raw_publish(verify: bool) -> ExecutableBuffer {
    JitCompiler::new(JitConfig {
        verify,
        ..JitConfig::default()
    })
    .compile_raw(
        &raw_functions(),
        &HashMap::from([(HOST.to_owned(), installed_replay_floor_host as *const u8)]),
    )
    .expect("the raw fixture publishes")
}

fn call_i64(buffer: &ExecutableBuffer, name: &str, value: i64) -> i64 {
    // SAFETY: every raw fixture function has the `(i64) -> i64` C ABI and
    // the buffer is live for the call.
    unsafe {
        (buffer
            .get_fn_bound::<extern "C" fn(i64) -> i64>(name)
            .expect("published symbol")
            .as_ref())(value)
    }
}

#[test]
fn a_verifying_raw_publication_replays_words_branches_and_veneers() {
    let buffer = raw_publish(true);
    let record = buffer
        .installed_replay()
        .expect("a verifying AArch64 publication carries its installed-artifact replay");
    assert!(record.covers_exactly(["callee", "tail_internal", "tail_external"]));
    assert_eq!(record.functions().len(), 3);
    assert_eq!(
        (
            record.words_compared(),
            record.branch_sites(),
            record.veneers(),
            record.literals()
        ),
        (2, 2, 1, 0),
        "ADD and RET compared; two B sites re-targeted; one veneer checked"
    );
    assert_eq!(
        record.installed_image_sha256(),
        buffer.published_image_sha256()
    );
    assert_eq!(call_i64(&buffer, "callee", 41), 42);
    assert_eq!(call_i64(&buffer, "tail_internal", i64::MAX), i64::MIN);
    assert_eq!(call_i64(&buffer, "tail_external", 14), 42);
}

#[test]
fn a_non_verifying_publication_carries_no_replay() {
    let buffer = raw_publish(false);
    assert!(buffer.installed_replay().is_none());
    assert_eq!(call_i64(&buffer, "tail_external", -2), -6);
}

/// The policy and authority variables the outer certificate cache reads
/// (as `jit_cert_cache_identity_aarch64` removes them).
const CACHE_POLICY_ENV: &[&str] = &[
    "TCG_JIT_UNCHECKED",
    "TCG_PROVENANCE_XCHECK",
    "TCG_NO_VERDICT_DB",
    "TCG_NO_PROOF_CACHE",
    "TCG_NO_JIT_CERT_CACHE",
    "TCG_NO_SOLVER_SERVER",
    "AY_SOLVER_PATH",
    "TCG_EXTERNAL_CLEAN_CHECKER",
    "TCG_CLEAN_CHECKER",
    "TCG_PRECISE_CITATIONS",
    "TCG_BLOCKING_IDENTITY",
];

fn with_cache_authority<T>(run: impl FnOnce() -> T) -> T {
    env_lock::with_env_overrides_removed(CACHE_POLICY_ENV, || {
        env_lock::with_env_overrides(&[("TCG_BLOCKING_IDENTITY", "1")], || {
            assert!(
                trust_cg_verify::jit_verification_authority_id_if_ready().is_some(),
                "this control requires the discovered AY/Clean verification authority; an \
                 unavailable authority is a failure, not a pass"
            );
            run()
        })
    })
}

/// `zext i8 -> i32`, certified by exhaustive evidence.
fn zext_module(name: &str) -> Module {
    let mut module = Module::new("jit_installed_artifact_replay");
    let signature = module
        .add_func_type(FuncTy {
            params: vec![Ty::I8],
            returns: vec![Ty::I32],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = Function::new(FuncId::new(0), name, signature, BlockId::new(0));
    function.blocks.push(Block {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I8)],
        body: vec![
            InstrNode::new(Inst::Cast {
                op: CastOp::ZExt,
                src_ty: Ty::I8,
                dst_ty: Ty::I32,
                operand: ValueId::new(0),
            })
            .with_result(ValueId::new(1)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(1)],
            }),
        ],
    });
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
    module
}

fn proof_required(cache: &Arc<JitCertCache>, mode: JitValidationMode) -> Compiler {
    Compiler::new(CompilerConfig {
        opt_level: OptLevel::O1,
        parallel: false,
        jit_validation_mode_override: Some(mode),
        ..CompilerConfig::jit_fast(Target::Aarch64)
    })
    .with_jit_cert_cache(Arc::clone(cache))
    .with_codegen_license(permit_unlicensed())
}

fn zext_call(buffer: &ExecutableBuffer, name: &str, value: u8) -> u32 {
    // SAFETY: `(u8) -> u32` is the module's C ABI; the buffer is live.
    unsafe {
        (buffer
            .get_fn_bound::<extern "C" fn(u8) -> u32>(name)
            .expect("published symbol")
            .as_ref())(value)
    }
}

#[test]
fn proof_required_publications_replay_every_function_including_warm_hits() {
    with_cache_authority(|| {
        let cache = Arc::new(JitCertCache::new());
        for (mode, name) in [
            (JitValidationMode::AlwaysVerify, "replayed_zext_always"),
            (JitValidationMode::CachedVerified, "replayed_zext_cached"),
        ] {
            let compiler = proof_required(&cache, mode);
            let module = zext_module(name);
            let cold = compiler
                .compile_module_to_jit(&module, &HashMap::new())
                .unwrap_or_else(|error| panic!("{mode:?}: cold compile: {error}"));
            let warm = compiler
                .compile_module_to_jit(&module, &HashMap::new())
                .unwrap_or_else(|error| panic!("{mode:?}: warm compile: {error}"));
            for (label, result) in [("cold", &cold), ("warm", &warm)] {
                let record = result.buffer.installed_replay().unwrap_or_else(|| {
                    panic!("{mode:?} {label}: a proof-required publication without its replay")
                });
                assert!(record.covers_exactly([name]), "{mode:?} {label}");
                assert!(record.words_compared() > 0, "{mode:?} {label}");
                assert_eq!(
                    (record.branch_sites(), record.veneers(), record.literals()),
                    (0, 0, 0),
                    "{mode:?} {label}: a relocation-free leaf"
                );
                assert_eq!(
                    record.installed_image_sha256(),
                    result.buffer.published_image_sha256(),
                    "{mode:?} {label}"
                );
                for value in [0u8, 1, 0x7f, 0x80, 0xff] {
                    assert_eq!(zext_call(&result.buffer, name, value), u32::from(value));
                }
            }
            let (cold_record, warm_record) = (
                cold.buffer.installed_replay().unwrap(),
                warm.buffer.installed_replay().unwrap(),
            );
            assert_eq!(
                cold_record.words_compared(),
                warm_record.words_compared(),
                "{mode:?}: the warm publication is replayed in full, not trusted"
            );
            if mode == JitValidationMode::CachedVerified {
                assert!(
                    warm.buffer
                        .certificate(name)
                        .is_some_and(|certificate| certificate.served_from_cache()),
                    "the warm CachedVerified verdict came from the cache"
                );
            }
        }
    });
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes, and no refusal is the license's, by accident.
fn permit_unlicensed() -> trust_cg_codegen::CodegenLicensePolicy {
    trust_cg_codegen::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit)
}
