// Copyright 2026 Andrew Yates | Apache-2.0
//! AArch64 Mach-O native control for trust-ir niche-encoded enums: the corpus
//! in `common/niche_enum_corpus.rs` (`Option<&u64>`, `Option<NonZeroU32>`,
//! `Option<bool>`, `Option<char>`, the three-variant `Tri` and the wrapping
//! `Wrapped`) is compiled at O0-O3, linked against a C driver whose oracle is
//! the C spelling of each niche layout, and executed. The corpus reads the
//! discriminant (`ExtractField` element 0) and switches on it, constructs
//! every variant from constants and runtime payload inserts, and selects a
//! complete fieldless variant at runtime. Canonical retagging is refused.
//! Execution evidence on aarch64-apple-darwin only; `e2e_aarch64_niche_enum_linux.rs` is the ELF
//! and Linux-native twin. Not a proof of the niche codec.

#[path = "common/niche_enum_corpus.rs"]
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
fn backend_refuses_canonical_enum_retagging_at_every_optimization() {
    let module = corpus::discriminant_write_module(TRIPLE);
    let errors = trust_ir_build::validate_module(&module);
    assert!(errors.iter().any(|error| matches!(
        error,
        trust_ir_build::ValidationError::FieldAccessInvalid { op, reason, .. }
            if op.as_str() == "insert_field" && reason.contains("cannot rewrite an enum discriminant")
    )), "{errors:?}");
    for level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
        // Since WS7.3 ingestion admission refuses it first, by trust-ir's
        // own finding (the adapter's `EnumTagWriteUnsupported` stays behind
        // it on the raw adapter entries).
        let error = compile(&module, level).expect_err("retagging must not reach emission");
        assert!(
            error.starts_with("InvalidTrustIr(") && error.contains("FieldAccessInvalid"),
            "{level:?}: {error}"
        );
    }
}

/// A reserved value that overlaps a valid payload must be refused.
#[test]
fn backend_refuses_a_niche_whose_reserved_value_is_a_valid_payload() {
    let mut module = corpus::corpus(TRIPLE);
    let bool_enum = module
        .enums
        .iter_mut()
        .find(|e| e.name == "OptionBool")
        .expect("the corpus has Option<bool>");
    if let Some(layout) = bool_enum.layout.as_mut()
        && let trust_ir::ty::EnumTagEncoding::Niche { niche_start, .. } = &mut layout.encoding
    {
        // 1 is `true`: `Some(true)` would decode as `None`.
        *niche_start = 1;
    }
    for opt_level in [OptLevel::O0, OptLevel::O3] {
        let error = compile(&module, opt_level).expect_err("an overlapping niche must be refused");
        assert!(
            error.contains("[TCG-NICHE-ENUM]") && error.contains("overlap"),
            "{opt_level:?}: {error}"
        );
    }
}

#[test]
fn native_niche_enums_agree_with_the_c_oracle_o0_through_o3() {
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
        let dir = fresh_dir::create("trust-cg-niche-enum-");
        fs::write(dir.join("module.o"), &object).unwrap();
        fs::write(dir.join("driver.c"), corpus::DRIVER).unwrap();
        let binary = dir.join("driver");
        let link = process::command_output_with_timeout(
            Command::new("cc")
                .arg("-O2")
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
