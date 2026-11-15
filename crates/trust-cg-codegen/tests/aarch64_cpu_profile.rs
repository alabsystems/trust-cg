// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
//! Actual Linux CPU capabilities, child execution and JIT feature admission.
//! An explicitly emulated process supplies emulated evidence, never native credit.
#![cfg(all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"))]

#[path = "common/fresh_dir.rs"]
mod fresh_dir;
#[path = "common/rosetta.rs"]
mod process;

use std::collections::HashMap;
use std::fs;
use std::os::unix::process::ExitStatusExt;
use std::process::Command;

use trust_cg_codegen::aarch64_dispatch::aarch64_host_features;
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::{AArch64IsaFeature, AArch64IsaProfile};
use trust_cg_codegen::{Compiler, CompilerConfig, Target};
use trust_ir::Ty;
use trust_ir_build::ModuleBuilder;

const FEATURES: [(AArch64IsaFeature, &str); 3] = [
    (AArch64IsaFeature::Lse, "lse"),
    (AArch64IsaFeature::Fp16, "fp16"),
    (AArch64IsaFeature::DotProd, "dotprod"),
];
const OPTS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];

fn command(program: &std::path::Path) -> Command {
    process::aarch64_emulation::configured_command(program)
        .expect("valid explicit execution configuration")
        .unwrap_or_else(|| Command::new(program))
}

#[test]
fn actual_cpu_and_child_executor_agree_on_optional_instruction_availability() {
    let dir = fresh_dir::create("trust-cg-cpu-profile-");
    let source = dir.join("cpu.c");
    let executable = dir.join("cpu");
    fs::write(&source, include_str!("support/aarch64_cpu_profile.c")).unwrap();
    let build = process::command_output_with_timeout(
        Command::new("cc")
            .args(["-std=c11", "-O2", "-march=armv8-a"])
            .arg(&source)
            .arg("-o")
            .arg(&executable),
        process::codegen_link_timeout(),
    )
    .unwrap();
    assert!(
        !build.timed_out && build.output.status.success(),
        "{}",
        String::from_utf8_lossy(&build.output.stderr)
    );
    let run = process::command_output_with_timeout(
        command(&executable).arg("features"),
        process::codegen_run_timeout(),
    )
    .unwrap();
    assert!(!run.timed_out && run.output.status.success());
    let text = String::from_utf8(run.output.stdout).unwrap();
    let flags: HashMap<_, _> = text
        .split_whitespace()
        .filter_map(|word| word.split_once('='))
        .collect();
    let host = aarch64_host_features();
    let profile = AArch64IsaProfile::for_host_jit();
    let mut checks = 0;
    for (mode, implemented) in [
        ("llsc", true),
        ("lse", host.implements(AArch64IsaFeature::Lse)),
        ("fp16_scalar", host.implements(AArch64IsaFeature::Fp16)),
        ("fp16_simd", host.implements(AArch64IsaFeature::Fp16)),
        ("dotprod", host.implements(AArch64IsaFeature::DotProd)),
    ] {
        if mode != "llsc" {
            assert_eq!(
                flags.get(mode).copied(),
                Some(if implemented { "1" } else { "0" }),
                "parent/child CPU mismatch: {text}"
            );
        }
        let ran = process::command_output_with_timeout(
            command(&executable).arg(mode),
            process::codegen_run_timeout(),
        )
        .unwrap();
        assert!(!ran.timed_out, "{mode}: execution timed out");
        if implemented {
            assert!(
                ran.output.status.success(),
                "{mode}: {:?} {}",
                ran.output.status,
                String::from_utf8_lossy(&ran.output.stderr)
            );
        } else {
            assert_eq!(
                ran.output.status.signal(),
                Some(4),
                "{mode}: expected actual SIGILL"
            );
        }
        checks += 1;
    }
    for (feature, _) in FEATURES {
        assert_eq!(profile.permits(feature), host.implements(feature));
    }
    assert_eq!(checks, 5);
    eprintln!(
        "AARCH64_CPU_PROFILE checks={checks} profile={profile} {}",
        text.trim()
    );
}

fn module(feature: Option<&str>) -> trust_ir::Module {
    let mut builder = ModuleBuilder::new("cpu_feature_admission");
    let signature = builder.add_func_type(vec![], vec![Ty::I32]);
    let mut function = builder.function("answer", signature);
    let entry = function.create_block();
    function.switch_to_block(entry);
    let value = function.iconst(Ty::I32, 17);
    function.ret(vec![value]);
    function.build();
    let mut module = builder.build().expect("valid feature fixture");
    if let Some(feature) = feature {
        module.functions[0].attrs.target_features = vec![feature.to_owned()];
    }
    module
}

#[test]
fn jit_feature_attributes_match_the_executing_cpu_at_every_optimization_level() {
    let mut matched = 0;
    let mut refused = 0;
    for opt_level in OPTS {
        for (feature, required) in std::iter::once((None, None)).chain(
            FEATURES
                .into_iter()
                .map(|(feature, name)| (Some(name), Some(feature))),
        ) {
            let mut config = CompilerConfig::jit_fast(Target::Aarch64);
            config.opt_level = opt_level;
            let result = Compiler::new(config)
                .with_codegen_license(
                    trust_cg_codegen::CodegenLicensePolicy::default()
                        .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit),
                )
                .compile_module_to_jit(&module(feature), &HashMap::new());
            if required.is_none_or(|feature| aarch64_host_features().implements(feature)) {
                let compiled =
                    result.unwrap_or_else(|error| panic!("{opt_level:?} {feature:?}: {error}"));
                type Answer = extern "C" fn() -> i32;
                // SAFETY: exact signature; every declared feature is implemented by this CPU.
                let function = unsafe { compiled.buffer.get_fn_bound::<Answer>("answer") }.unwrap();
                assert_eq!(function.as_ref()(), 17);
                matched += 1;
            } else {
                let Err(error) = result else {
                    panic!("unavailable feature must refuse before publication");
                };
                let error = error.to_string();
                assert!(
                    error.contains("[TCG-TARGET-FEATURE]") && error.contains(feature.unwrap()),
                    "{error}"
                );
                refused += 1;
            }
        }
    }
    assert_eq!(matched + refused, 16);
    assert!(matched >= 4, "every baseline function must execute");
    eprintln!("AARCH64_JIT_CPU_PROFILE cells=16 matched={matched} refused={refused}");
}

#[test]
fn emulation_configuration_rejects_incomplete_and_untrusted_inputs() {
    use process::aarch64_emulation::Emulation;
    assert!(Emulation::from_values(None, None).unwrap().is_none());
    assert!(Emulation::from_values(Some("/usr/bin/false".into()), None).is_err());
    assert!(Emulation::from_values(None, Some("cortex-a53".into())).is_err());
    assert!(Emulation::new(std::path::Path::new("relative"), "cortex-a53").is_err());
    assert!(Emulation::new(std::path::Path::new("/usr/bin/false"), "cortex-a53,+lse").is_err());
    let dir = fresh_dir::create("trust-cg-emulation-contract-");
    let script = dir.join("script");
    fs::write(&script, b"#!/bin/sh\nexit 0\n").unwrap();
    let emulator = Emulation::new(std::path::Path::new("/usr/bin/false"), "cortex-a53").unwrap();
    assert!(
        emulator.command(&script).is_err(),
        "configured execution cannot fall back for a script"
    );
    assert!(
        emulator
            .command(std::path::Path::new("./relative"))
            .is_err()
    );
    let executable = std::env::current_exe().unwrap();
    let selected = emulator.command(&executable).unwrap();
    assert_eq!(selected.get_program(), "/usr/bin/false");
    assert_eq!(selected.get_args().next().unwrap(), "-cpu");
    eprintln!("AARCH64_EMULATION_CONTRACT controls=8");
}
