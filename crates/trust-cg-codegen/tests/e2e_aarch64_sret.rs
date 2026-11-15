// trust-cg-codegen/tests/e2e_aarch64_sret.rs
//
// Apple arm64 hidden-result (`sret`) results through X8, both directions,
// against a clang oracle (ledger L01-P5).
//
// A C function returning a 40-byte non-homogeneous struct receives the
// result address in X8 (AAPCS64 §6.9 indirect result location register),
// outside the X0-X7 argument bank, so its ordinary arguments are numbered as
// if the hidden pointer did not exist. TrustIR states that convention in two
// shapes and both must produce byte-identical machine conventions:
//
// * structural: `returns: [Struct(Big)]`, which the target ABI classifies
//   indirect. The FUNCTION TYPE itself carries the identity, so a pointer that
//   flows dynamically (a C function pointer passed as a parameter) can be
//   called through it;
// * pre-lowered: `params: [Ptr sret, ...], returns: []`, the frontend-lowered
//   form carried by `ParamAttrs::sret` on the DECLARATION. The pinned trust-ir
//   has no attribute slot on a `FuncTy` and none on a `CallIndirect`, so the
//   adapter establishes an indirect call's identity only through trust-ir's
//   own typed provenance (`Const FnDef` reached through `Copy` /
//   `ReifyFnPointer`) to such a declaration, and refuses an edge that
//   disagrees with it.
//
// Every callee takes nine integer, nine floating-point and two narrow
// arguments, so one integer, one double and both narrow arguments are passed
// on the stack (the narrow ones packed at 4-byte offsets, DarwinPCS), and the
// CG callee calls a C helper while every argument is still live, so the
// hidden pointer and the arguments must survive X8 and the caller-saved bank
// being clobbered. Directions and shapes, each at O0-O3:
//
// * C caller (through a `volatile` function pointer) -> CG callee, both
//   shapes;
// * CG caller -> C callee: through a static-provenance pointer (pre-lowered
//   shape, `BLR` with X8), through a pointer received from C (structural
//   shape), and through a variadic callee `struct Big f(int n, ...)` in both
//   shapes, with the anonymous arguments on the Apple stack.
//
// Refusals that stay: a hidden parameter anywhere but index 0, a hidden
// parameter with a non-empty return list, an indirect edge whose signature
// disagrees with the resolved `sret` declaration, an indirect call over a
// variadic signature, and a variadic DEFINITION (no `va_start` lowering).
//
// The TrustIR corpus and the C driver live in `common/sret_corpus.rs`, shared
// with the ELF and Linux-native twin `e2e_aarch64_sret_linux.rs`; this file
// keeps the Darwin (Mach-O, `otool`, clang) evidence.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

#![cfg(all(target_os = "macos", target_arch = "aarch64"))]

#[path = "common/sret_corpus.rs"]
mod corpus;

#[path = "common/admission_expect.rs"]
mod admission_expect;

#[path = "common/fresh_dir.rs"]
mod fresh_dir;

use std::fs;
use std::process::Command;

use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::TargetSpec;
use trust_cg_codegen::{Compiler, CompilerConfig};
use trust_ir::{Module, Ty};

use corpus::{CALLEE_DRIVER, CALLER_DRIVER, ORACLE_PRELUDE};

const TRIPLE: &str = "aarch64-apple-darwin";

fn compile_at(module: &Module, opt_level: OptLevel) -> Vec<u8> {
    let object = Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level,
            ..CompilerConfig::default()
        },
        TargetSpec::parse(TRIPLE).expect("Darwin triple parses"),
    )
    .with_codegen_license(permit_unlicensed())
    .compile(module)
    .unwrap_or_else(|error| panic!("sret module must compile at {opt_level:?}: {error:?}"))
    .object_code;
    assert_eq!(
        &object[..4],
        &[0xcf, 0xfa, 0xed, 0xfe],
        "the Darwin target must emit a Mach-O object"
    );
    object
}

fn compile_error(module: &Module, opt_level: OptLevel) -> String {
    let error = Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level,
            ..CompilerConfig::default()
        },
        TargetSpec::parse(TRIPLE).expect("Darwin triple parses"),
    )
    .with_codegen_license(permit_unlicensed())
    .compile(module)
    .map(|_| ())
    .expect_err("the module must be refused");
    format!("{error} ({error:?})")
}

/// `module` is refused at `opt_level`: by trust-ir's own first admission
/// finding when trust-ir refuses it (WS7.3: ingestion admission runs before
/// any backend arm), else by the backend's message naming every `needle`.
fn assert_refused(module: &Module, opt_level: OptLevel, needles: &[&str]) {
    let message = compile_error(module, opt_level);
    match admission_expect::names_first_finding(module, &message, &permit_unlicensed()) {
        Some(named) => assert!(
            named,
            "{opt_level:?}: trust-ir's finding {:?} is not named in {message}",
            admission_expect::first_finding(module, &permit_unlicensed())
        ),
        None => assert!(
            needles.iter().all(|needle| message.contains(needle)),
            "{opt_level:?}: {message}"
        ),
    }
}

fn scratch_dir(tag: &str) -> fresh_dir::ScratchDir {
    fresh_dir::create(&format!("trust-cg-darwin-sret-{tag}-"))
}

fn link_and_run(tag: &str, object: &[u8], driver: &str) -> (i32, String) {
    let dir = scratch_dir(tag);
    let object_path = dir.join("module.o");
    let driver_path = dir.join("driver.c");
    let binary_path = dir.join("driver");
    fs::write(&object_path, object).expect("write object");
    fs::write(&driver_path, format!("{ORACLE_PRELUDE}\n{driver}")).expect("write driver");
    // An optimized oracle: an O0 C side could spill and re-read in ways that
    // mask a placement defect on the CG side.
    let link = Command::new("cc")
        .arg("-O2")
        .arg(&driver_path)
        .arg(&object_path)
        .arg("-o")
        .arg(&binary_path)
        .output()
        .expect("cc is required on the macOS aarch64 host");
    assert!(
        link.status.success(),
        "{tag}: link failed; files={dir:?}\n{}",
        String::from_utf8_lossy(&link.stderr)
    );
    let run = Command::new(&binary_path)
        .output()
        .expect("run the linked driver");
    let stdout = String::from_utf8_lossy(&run.stdout).into_owned();
    let code = run.status.code().unwrap_or(-1);
    if code == 0 {
        let _ = fs::remove_dir_all(&dir);
    }
    (code, stdout)
}

/// True when a disassembly line names the register `x8` as a whole operand
/// token (not `#0x8`, `#0x80` or an address containing the digits).
fn names_register_x8(line: &str) -> bool {
    line.split(|c: char| !c.is_ascii_alphanumeric())
        .any(|token| token == "x8")
}

/// The `otool -tv` disassembly of one function in `object`.
fn disassemble(tag: &str, object: &[u8], symbol: &str) -> String {
    let dir = scratch_dir(tag);
    let object_path = dir.join("module.o");
    fs::write(&object_path, object).expect("write object");
    let out = Command::new("otool")
        .arg("-tv")
        .arg(&object_path)
        .output()
        .expect("otool is required on the macOS aarch64 host");
    assert!(
        out.status.success(),
        "otool failed: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    let text = String::from_utf8_lossy(&out.stdout).into_owned();
    let _ = fs::remove_dir_all(&dir);
    let start = text
        .find(&format!("{symbol}:"))
        .unwrap_or_else(|| panic!("{symbol} is not in the disassembly:\n{text}"));
    let rest = &text[start + symbol.len() + 1..];
    let end = rest.find("\n_").unwrap_or(rest.len());
    rest[..end].to_string()
}

#[test]
fn c_caller_reaches_cg_sret_callees_through_pointers_o0_to_o3() {
    let module = corpus::build_callee_module(TRIPLE);
    for opt_level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
        let object = compile_at(&module, opt_level);
        let (code, stdout) = link_and_run(&format!("callee-{opt_level:?}"), &object, CALLEE_DRIVER);
        assert_eq!(
            code, 0,
            "CG sret callee diverged from clang at {opt_level:?}: {stdout}"
        );
    }
}

#[test]
fn cg_caller_reaches_c_sret_callees_through_pointers_and_variadics_o0_to_o3() {
    let module = corpus::build_caller_module(TRIPLE);
    for opt_level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
        let object = compile_at(&module, opt_level);
        // The static-provenance edge stays an indirect call: a `blr`, never a
        // `bl` to the resolved symbol (an external declaration is not an
        // exact-module target), with the buffer address staged into x8.
        let text = disassemble(
            &format!("caller-{opt_level:?}"),
            &object,
            "_cg_call_attr_fp",
        );
        assert!(text.contains("blr"), "{opt_level:?}: no blr in\n{text}");
        assert!(
            !text.contains("bl\t_c_big_attr") && !text.contains("bl\t0x"),
            "{opt_level:?}: the static-provenance sret edge was devirtualized:\n{text}"
        );
        assert!(
            text.lines().any(names_register_x8),
            "{opt_level:?}: x8 is never written before the blr:\n{text}"
        );
        let (code, stdout) = link_and_run(&format!("caller-{opt_level:?}"), &object, CALLER_DRIVER);
        assert_eq!(
            code, 0,
            "CG caller of C sret callees diverged from clang at {opt_level:?}: {stdout}"
        );
    }
}

#[test]
fn indirect_edge_disagreeing_with_a_resolved_sret_declaration_is_refused() {
    // The declaration passes a hidden buffer and returns nothing; the edge
    // claims the same parameters but an I64 result.
    let module = corpus::indirect_edge_module(
        TRIPLE,
        (vec![Ty::Ptr, Ty::I64], vec![], false),
        |attrs| attrs[0].sret = true,
        (vec![Ty::Ptr, Ty::I64], vec![Ty::I64], false),
        1,
    );
    for opt_level in [OptLevel::O0, OptLevel::O2] {
        assert_refused(
            &module,
            opt_level,
            &["[TCG-SRET-ABI]", "indirect call resolves to `callee`"],
        );
    }
}

#[test]
fn indirect_edge_agreeing_with_a_resolved_sret_declaration_compiles() {
    let module = corpus::indirect_edge_module(
        TRIPLE,
        (vec![Ty::Ptr, Ty::I64], vec![], false),
        |attrs| attrs[0].sret = true,
        (vec![Ty::Ptr, Ty::I64], vec![], false),
        0,
    );
    for opt_level in [OptLevel::O0, OptLevel::O2] {
        let object = compile_at(&module, opt_level);
        let text = disassemble(&format!("edge-{opt_level:?}"), &object, "_caller");
        assert!(text.contains("blr"), "{opt_level:?}: no blr in\n{text}");
        assert!(
            text.lines().any(names_register_x8),
            "{opt_level:?}:\n{text}"
        );
    }
}

#[test]
fn indirect_call_over_a_variadic_sret_signature_stays_refused() {
    let module = corpus::indirect_edge_module(
        TRIPLE,
        (vec![Ty::Ptr, Ty::I32], vec![], true),
        |attrs| attrs[0].sret = true,
        (vec![Ty::Ptr, Ty::I32], vec![], true),
        0,
    );
    assert_refused(
        &module,
        OptLevel::O0,
        &["CallIndirect over variadic FuncTyId"],
    );
}

#[test]
fn hidden_parameter_declarations_the_selector_cannot_place_are_refused() {
    // sret at index 1: no register is named for a non-leading hidden pointer.
    assert_refused(
        &corpus::sret_at_index_1_module(TRIPLE),
        OptLevel::O0,
        &[
            "[TCG-SRET-ABI]",
            "only a leading hidden return-buffer parameter is supported",
        ],
    );

    // sret alongside a return value: two competing return conventions.
    assert_refused(
        &corpus::sret_with_return_module(TRIPLE),
        OptLevel::O0,
        &["[TCG-SRET-ABI]", "requires an empty return list"],
    );

    // A variadic DEFINITION with a hidden buffer: no va_start lowering exists,
    // so the definition (not the convention) is what is refused.
    assert_refused(
        &corpus::sret_variadic_definition_module(TRIPLE),
        OptLevel::O0,
        &["[TCG-VARIADIC-DEFINITION]"],
    );
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
