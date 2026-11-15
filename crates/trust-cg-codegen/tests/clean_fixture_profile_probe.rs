// trust-cg-codegen/tests/clean_fixture_profile_probe.rs - a release-mode
// time-attribution probe for ONE Clean-kernel fixture.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// WHY. `clean_fixture_host_lowering` reports whether a fixture lowers inside
// `FIXTURE_DEADLINE`; it cannot say WHERE the time goes. This target compiles
// one named fixture with `trace_level: Full` and prints the phase rows, so the
// ~380s four and the ~25s three can be compared phase by phase. It measures;
// it asserts nothing about time, and it changes nothing the sweep measures.
//
// INERT BY DEFAULT: without `CLEAN_PROFILE_FIXTURE` it compiles nothing and
// passes, so it costs a normal `cargo test` run only its own link.
//
// USE:
//   CLEAN_PROFILE_FIXTURE=clean_lazy_delta.gate.trust.tir \
//   TCG_TIME_X86PM=1 \
//   scripts/trust_cargo.sh test --release -p trust-cg-codegen \
//     --test clean_fixture_profile_probe -- --nocapture
//
// `CLEAN_PROFILE_OPT=O0|O1` picks the opt level (default O1).

#![cfg(target_arch = "x86_64")]

#[path = "common/kernel_fixture.rs"]
mod kernel_fixture;

use std::time::Instant;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig, CompilerTraceLevel};
use trust_cg_codegen::pipeline::OptLevel;

#[test]
fn profile_one_clean_fixture() {
    let Ok(name) = std::env::var("CLEAN_PROFILE_FIXTURE") else {
        eprintln!("CLEAN_PROFILE_FIXTURE unset: nothing measured");
        return;
    };
    let opt_level = match std::env::var("CLEAN_PROFILE_OPT").as_deref() {
        Ok("O0") => OptLevel::O0,
        _ => OptLevel::O1,
    };
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join(&name);
    let text = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("cannot read {}: {e}", path.display()));

    let parse_start = Instant::now();
    let module = kernel_fixture::parse_host_module(&text)
        .unwrap_or_else(|e| panic!("{name}: parse for host failed: {e:?}"));
    let parse = parse_start.elapsed();

    let compile_start = Instant::now();
    let result = Compiler::new(CompilerConfig {
        opt_level,
        target: kernel_fixture::host_jit_target(),
        trace_level: CompilerTraceLevel::Full,
        ..CompilerConfig::default()
    })
    .with_codegen_license(permit_unlicensed())
    .compile(&module)
    .unwrap_or_else(|e| panic!("{name} at {opt_level:?}: {e:?}"));
    let compile = compile_start.elapsed();

    println!("CLEAN_PROFILE fixture={name} opt={opt_level:?}");
    println!("CLEAN_PROFILE parse={:.3}s", parse.as_secs_f64());
    println!("CLEAN_PROFILE compile={:.3}s", compile.as_secs_f64());
    println!(
        "CLEAN_PROFILE functions={} object_bytes={} code_size={} insts={}",
        result.metrics.function_count,
        result.object_code.len(),
        result.metrics.code_size_bytes,
        result.metrics.instruction_count
    );
    if let Some(trace) = &result.trace {
        println!(
            "CLEAN_PROFILE trace_total={:.3}s",
            trace.total_duration.as_secs_f64()
        );
        for entry in &trace.entries {
            println!(
                "CLEAN_PROFILE phase {:<28} {:>10.3}s  {}",
                entry.phase,
                entry.duration.as_secs_f64(),
                entry.detail.as_deref().unwrap_or("")
            );
        }
    }
}

/// The Clean fixtures carry no codegen license (`body_gate: None`), which
/// trust-cg REFUSES by default (roadmap WS7.5, decision gate DG-73). The
/// probe states `Permit` explicitly, exactly as `clean_fixture_host_lowering`
/// does, so the phases it measures are the lowering's, never the license's.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
