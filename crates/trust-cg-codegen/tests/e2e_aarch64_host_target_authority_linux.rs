// Copyright 2026 Andrew Yates | Apache-2.0
//! Linux AArch64 native controls for explicit target authority (X-DARWIN-P12).
//!
//! On a Linux host every host-derived selection must resolve to
//! `aarch64-unknown-linux-gnu` (AAPCS64, ELF) and say so, and the Pipeline must
//! refuse an empty triple instead of silently using DarwinPCS/Mach-O. The JIT
//! execution control passes narrow arguments on the stack, where DarwinPCS
//! packs them at natural size and AAPCS64 gives each an 8-byte slot; Rust's
//! own `extern "C"` caller uses the host (AAPCS64) placement, so a JIT that
//! selected DarwinPCS would read the wrong bytes.

#![cfg(all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"))]

use std::collections::HashMap;

use trust_cg_codegen::pipeline::{OptLevel, Pipeline, PipelineConfig, PipelineError};
use trust_cg_codegen::{
    Compiler, CompilerConfig, CompilerTargetSelection, JitCompiler, JitConfig, Target,
    TargetSelectionOrigin,
};
use trust_cg_lower::abi::AArch64AbiVariant;

const LINUX: &str = "aarch64-unknown-linux-gnu";

const NARROW_STACK_ARGS: &str = r#"
; trust_ir text format v1
module "linux_host_narrow_stack_args"
target "aarch64-unknown-linux-gnu" 8 little

functy.0 = (i64, i64, i64, i64, i64, i64, i64, i64, i8, i16, i32, i64) -> (i64)

fn @host_narrow_stack_args(functy.0) {
bb0(%0: i64, %1: i64, %2: i64, %3: i64, %4: i64, %5: i64, %6: i64, %7: i64, %8: i8, %9: i16, %10: i32, %11: i64):
    %12 = sext i8 %8 to i64
    %13 = sext i16 %9 to i64
    %14 = sext i32 %10 to i64
    %15 = const i64 1000
    %16 = mul i64 %12, %15
    %17 = const i64 1000000
    %18 = mul i64 %13, %17
    %19 = add i64 %16, %18
    %20 = add i64 %19, %14
    %21 = add i64 %20, %11
    %22 = add i64 %21, %0
    %23 = add i64 %22, %7
    ret %23
}
"#;

type NarrowStackArgs =
    extern "C" fn(i64, i64, i64, i64, i64, i64, i64, i64, i8, i16, i32, i64) -> i64;

#[test]
fn host_derived_compiler_records_linux_elf() {
    let compiler = Compiler::new(CompilerConfig {
        target: Target::Aarch64,
        ..CompilerConfig::default()
    })
    .with_codegen_license(permit_unlicensed());
    let expected = CompilerTargetSelection {
        triple: LINUX.to_owned(),
        origin: TargetSelectionOrigin::HostDerived { host_os: "linux" },
    };
    assert_eq!(compiler.target_selection(), expected);
    let module = trust_ir::parser::parse_module(NARROW_STACK_ARGS).expect("fixture parses");
    let result = compiler
        .compile(&module)
        .expect("host-derived AOT compiles");
    assert_eq!(result.target_selection, expected);
    assert_eq!(&result.object_code[..4], b"\x7fELF");
    assert_eq!(
        u16::from_le_bytes([result.object_code[18], result.object_code[19]]),
        183,
        "EM_AARCH64"
    );
}

#[test]
fn pipeline_host_target_is_aapcs64_and_empty_is_refused() {
    let host = PipelineConfig::for_host_aarch64();
    assert_eq!(host.target_triple, LINUX);
    assert_eq!(
        Pipeline::new(host).resolved_aarch64_abi().unwrap(),
        AArch64AbiVariant::Aapcs64
    );
    assert!(matches!(
        Pipeline::new(PipelineConfig::default()).resolved_aarch64_abi(),
        Err(PipelineError::TargetAbiUnresolved(_))
    ));
    assert_eq!(
        JitCompiler::new(JitConfig::default()).aarch64_target_triple(),
        LINUX,
        "the raw JIT must lower for the host ABI, not an empty default"
    );
}

#[test]
fn host_jit_places_narrow_stack_arguments_in_aapcs64_slots() {
    let module = trust_ir::parser::parse_module(NARROW_STACK_ARGS).expect("fixture parses");
    for opt_level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
        let mut config = CompilerConfig::jit_fast(Target::Aarch64);
        config.opt_level = opt_level;
        let compiler = Compiler::new(config).with_codegen_license(permit_unlicensed());
        assert_eq!(compiler.target_selection().triple, LINUX);
        let buffer = compiler
            .compile_module_to_jit(&module, &HashMap::new())
            .unwrap_or_else(|error| panic!("{opt_level:?}: {error}"))
            .buffer;
        let raw = buffer
            .get_fn_ptr_bound("host_narrow_stack_args")
            .expect("entry symbol")
            .as_ptr();
        let entry: NarrowStackArgs = unsafe { std::mem::transmute(raw) };
        let got = entry(3, 0, 0, 0, 0, 0, 0, 5, -7, 12, -40_000, 900_000_000_000);
        let want = -7_i64 * 1000 + 12 * 1_000_000 - 40_000 + 900_000_000_000 + 3 + 5;
        assert_eq!(got, want, "{opt_level:?}");
    }
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
