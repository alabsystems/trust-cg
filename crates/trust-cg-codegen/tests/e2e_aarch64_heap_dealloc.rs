// Copyright 2026 Andrew Yates | Apache-2.0
//! AArch64 Mach-O native control for TrustIR `Inst::HeapAlloc` released by a
//! CALL to the owning runtime's deallocation entry point: the corpus in
//! `common/heap_dealloc_corpus.rs` is compiled at O0-O3, linked against a C
//! driver that interposes `__rust_alloc`, `__rust_dealloc`, `malloc` and
//! `free`, and executed. The driver checks each release's allocator and exact
//! layout, that every call leaves nothing live, and that its leak and
//! double-free negative controls are observed. `Inst::Dealloc` itself is
//! refused for codegen in every body (G18-1), which the backend-refusal row
//! pins without a host. Execution evidence on aarch64-apple-darwin only;
//! `e2e_aarch64_heap_dealloc_linux.rs` is the ELF and Linux-native twin.
//! Neither is a proof of the external allocator.

#[path = "common/heap_dealloc_corpus.rs"]
mod corpus;
#[path = "common/rosetta.rs"]
mod process;

#[path = "common/fresh_dir.rs"]
mod fresh_dir;

use std::fs;
use std::process::Command;

use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::TargetSpec;
use trust_cg_codegen::{Compiler, CompilerConfig};

const TRIPLE: &str = "aarch64-apple-darwin";

fn compile(module: &trust_ir::Module, opt_level: OptLevel) -> Result<Vec<u8>, String> {
    Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level,
            ..CompilerConfig::default()
        },
        TargetSpec::parse(TRIPLE).unwrap(),
    )
    .with_codegen_license(permit_unlicensed())
    .compile(module)
    .map(|output| output.object_code)
    .map_err(|error| format!("{error:?}"))
}

#[test]
fn backend_refuses_every_dealloc_whatever_its_provenance() {
    for opt_level in [OptLevel::O0, OptLevel::O2] {
        for (shape, module) in corpus::dealloc_modules(TRIPLE) {
            let refusal = compile(&module, opt_level)
                .expect_err("every Inst::Dealloc must be refused (G18-1)");
            assert!(
                refusal.contains("[TCG-DEALLOC]") && refusal.contains("UnlowerableForCodegen"),
                "{shape} at {opt_level:?}: {refusal}"
            );
        }
    }
}

#[test]
fn native_heap_dealloc_balances_rust_and_libc_allocators_o0_through_o3() {
    if !cfg!(all(target_os = "macos", target_arch = "aarch64")) {
        eprintln!("SKIP: needs aarch64-apple-darwin");
        return;
    }
    let module = corpus::corpus(TRIPLE);
    for opt_level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
        let object = compile(&module, opt_level).unwrap();
        assert_eq!(
            &object[..4],
            &[0xcf, 0xfa, 0xed, 0xfe],
            "Mach-O 64 object expected"
        );
        let dir = fresh_dir::create("trust-cg-heap-dealloc-");
        fs::write(dir.join("module.o"), &object).unwrap();
        fs::write(dir.join("driver.c"), corpus::DRIVER).unwrap();
        let binary = dir.join("driver");
        let link = process::command_output_with_timeout(
            Command::new("cc")
                .arg("-O2")
                .arg("-fno-builtin")
                .arg(dir.join("driver.c"))
                .arg(dir.join("module.o"))
                .arg("-o")
                .arg(&binary),
            process::codegen_link_timeout(),
        )
        .unwrap();
        assert!(
            !link.timed_out && link.output.status.success(),
            "{opt_level:?} files={dir:?}: {}",
            String::from_utf8_lossy(&link.output.stderr)
        );
        let run =
            process::run_executable_with_timeout(&binary, process::codegen_run_timeout()).unwrap();
        let stdout = String::from_utf8_lossy(&run.output.stdout);
        assert!(
            !run.timed_out && run.output.status.success(),
            "{opt_level:?} files={dir:?}: {stdout} {}",
            String::from_utf8_lossy(&run.output.stderr)
        );
        assert_eq!(
            stdout.trim(),
            corpus::EXPECTED_PASS,
            "{opt_level:?} files={dir:?}: incomplete native execution"
        );
        eprintln!("{opt_level:?}: {}", stdout.trim());
        fs::remove_dir_all(&dir).unwrap();
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
