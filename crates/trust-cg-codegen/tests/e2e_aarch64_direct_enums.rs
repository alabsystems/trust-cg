// Copyright 2026 Andrew Yates | Apache-2.0
//! AArch64 Mach-O native control for DIRECT-TAG trust-ir enums beyond the
//! canonical index/unsigned/canonical-layout shape (ledger L05-P5): the
//! corpus in `common/direct_enums_corpus.rs` (`Ordering`, `Mixed`, `ReprC`,
//! `Small`, `Slot`, `Bytes3` and the record `Rec`, each at the producer
//! layout rustc gives it, plus enum-, record- and relocation-bearing
//! globals) is compiled at O0-O3, linked against a C driver whose oracle is
//! the C spelling of each layout, and executed; every zero-argument function
//! is ALSO run by the trust-ir reference interpreter, and the native value
//! printed by the driver must equal the interpreter's. The carrier and
//! refusal rows run on any host.
//!
//! Execution evidence on aarch64-apple-darwin only (Mach-O objects linked by
//! the host `cc`); `e2e_aarch64_direct_enums_linux.rs` is the ELF and
//! Linux-native twin. Not a proof of enum semantics.

#[path = "common/direct_enums_corpus.rs"]
mod corpus;

#[path = "common/admission_expect.rs"]
mod admission_expect;
#[path = "common/rosetta.rs"]
mod process;

#[path = "common/fresh_dir.rs"]
mod fresh_dir;

use std::collections::BTreeMap;
use std::fs;
use std::process::Command;

use corpus::{
    BYTES3, EXPECTED_CHECKS, LEVELS, MIXED, ORACLE, ORDERING, REPRC, SLOT, SMALL, enum_ty,
};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::TargetSpec;
use trust_cg_codegen::{Compiler, CompilerConfig};
use trust_cg_lower::types::Type;
use trust_ir::{EnumId, Module};
use trust_ir_build::validate_module;

const TRIPLE: &str = "aarch64-apple-darwin";

fn compile(module: &Module, opt_level: OptLevel) -> Result<Vec<u8>, String> {
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

/// The interpreter itself is pinned to the closed forms, so it cannot agree
/// with a wrong native value by being wrong the same way.
#[test]
fn interpreter_oracle_matches_the_closed_forms() {
    let module = corpus::corpus(TRIPLE);
    assert_eq!(
        validate_module(&module),
        [],
        "the corpus must be valid trust-ir"
    );
    for (name, want) in ORACLE {
        assert_eq!(corpus::interpret(&module, name), *want, "{name}");
    }
}

/// The carriers the type translation picks: the canonical `Type::Enum` where
/// it reproduces the producer's bytes, the byte-image carrier where it does
/// not — never a canonical recomputation of a different layout.
#[test]
fn producer_layouts_lower_to_their_declared_carriers() {
    use trust_cg_lower::adapter::translate_type_in_module;
    let module = corpus::corpus(TRIPLE);
    let carrier = |id: u32| translate_type_in_module(&module, &enum_ty(id)).expect("lowers");
    assert_eq!(
        carrier(MIXED),
        Type::Struct(vec![Type::Array(Box::new(Type::I64), 2)])
    );
    assert_eq!(
        carrier(SMALL),
        Type::Struct(vec![Type::Array(Box::new(Type::I16), 2)])
    );
    assert!(
        matches!(carrier(ORDERING), Type::Enum { .. }),
        "a one-byte tag with no payload is the canonical shape"
    );
    assert!(
        matches!(
            carrier(REPRC),
            Type::Enum {
                tag_width: trust_cg_ir::function::EnumTagWidth::U32,
                ..
            }
        ),
        "a declared four-byte tag lane the canonical shape reproduces"
    );
    assert!(matches!(carrier(SLOT), Type::Enum { .. }));
    assert!(matches!(carrier(BYTES3), Type::Enum { .. }));
    for id in [ORDERING, MIXED, REPRC, SMALL, SLOT, BYTES3] {
        let lowered = carrier(id);
        let shape = module
            .enum_layout_shape(EnumId::new(id))
            .expect("trust-ir computes the layout");
        assert_eq!(
            (
                u64::from(lowered.bytes()) * 8,
                u64::from(lowered.align()) * 8
            ),
            (shape.size_bits, shape.align_bits),
            "enum {id}: the carrier has trust-ir's size and alignment"
        );
    }
}

/// What stays refused is refused by name, at O0 and O3: a re-tag through
/// `InsertField`, duplicate discriminants, a 128-bit tag lane, a descriptor
/// whose field overlaps its tag word, a niche-enum-typed global, and a global
/// initializer whose discriminant names no variant.
#[test]
fn what_stays_refused_is_refused_by_name() {
    for (fixture, needle, module) in corpus::refusal_fixtures(TRIPLE) {
        for opt_level in [OptLevel::O0, OptLevel::O3] {
            let error = compile(&module, opt_level).expect_err(needle);
            assert!(
                admission_expect::names_first_finding(&module, &error, &permit_unlicensed())
                    .unwrap_or_else(|| error.contains(needle)),
                "{fixture} {opt_level:?}: neither trust-ir's admission finding nor `{needle}` \
                 in {error}"
            );
        }
    }
}

#[test]
fn native_direct_enums_agree_with_the_c_oracle_and_the_interpreter_o0_through_o3() {
    if !cfg!(all(target_os = "macos", target_arch = "aarch64")) {
        eprintln!("SKIP: needs aarch64-apple-darwin");
        return;
    }
    let module = corpus::corpus(TRIPLE);
    assert_eq!(
        validate_module(&module),
        [],
        "the corpus must be valid trust-ir"
    );
    let expected: BTreeMap<&str, u64> = ORACLE
        .iter()
        .map(|(name, _)| (*name, corpus::interpret(&module, name)))
        .collect();
    for opt_level in LEVELS {
        let object = compile(&module, opt_level).unwrap();
        assert_eq!(
            &object[..4],
            &[0xcf, 0xfa, 0xed, 0xfe],
            "Mach-O 64 object expected"
        );
        let dir = fresh_dir::create("trust-cg-direct-enums-");
        fs::write(dir.join("module.o"), &object).unwrap();
        fs::write(dir.join("driver.c"), corpus::driver()).unwrap();
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
        let mut native: BTreeMap<&str, u64> = BTreeMap::new();
        let mut verdict = None;
        for line in stdout.lines() {
            if let Some((name, value)) = line.split_once('=') {
                native.insert(name, value.trim().parse().expect("driver prints u64"));
            } else {
                verdict = Some(line.trim().to_string());
            }
        }
        assert_eq!(
            verdict.as_deref(),
            Some(format!("PASS {EXPECTED_CHECKS} direct-enum checks").as_str()),
            "{opt_level:?} files={dir:?}: incomplete native execution: {stdout}"
        );
        for (name, want) in &expected {
            assert_eq!(
                native.get(name),
                Some(want),
                "{opt_level:?}: native `{name}` disagrees with the interpreter"
            );
        }
        eprintln!(
            "{opt_level:?}: {} and {} oracle values agree with the interpreter",
            verdict.unwrap_or_default(),
            expected.len()
        );
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
