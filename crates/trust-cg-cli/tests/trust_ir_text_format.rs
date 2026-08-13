// trust-cg-cli/tests/trust_ir_text_format.rs - Integration tests for .trust_ir text I/O (#413)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Per `designs/2026-04-16-trust_ir-transport-architecture.md` Layer 3 and
// issue #413, Trust Codegen now:
//   - accepts the human-readable `.trust_ir` text format as a debug input
//     (enabled via `--format=text` or the `.trust_ir` extension under
//     `--format=auto`).
//   - can emit `.trust_ir` text via `--emit-trust_ir <PATH>` for round-tripping.
//
// Upstream trust_ir now emits and parses the `func_types` table, so parsed
// `.trust_ir` modules can be handed directly to Trust Codegen's lowering pass.
//
// These tests exercise the CLI binary end-to-end, concentrating on
// the output-side path that is working today:
//
//   1. `--emit-trust_ir <PATH>` writes parseable `.trust_ir` text from any input.
//   2. `--emit-trust_ir` rejects multi-input invocations.
//   3. Golden check: the printer output starts with the canonical
//      `; trust_ir text format v1` header (catches unintentional format drift).
//   4. `--format=text` accepts a `.trust_ir` input through the loader
//      (parse succeeds). Full compilation is disabled until the
//      upstream func_types round-trip lands.
//   5. `--format=auto` detects `.trust_ir` by extension.

use std::path::PathBuf;
use std::process::Command;

use trust_cg_codegen::pipeline::{encode_tmbc, encode_trust_ir_text, parse_trust_ir_text};
use trust_ir::{Module as TrustIrModule, Ty};
use trust_ir_build::ModuleBuilder;

/// Build a minimal `fn return_42() -> i64 { 42 }` trust_ir module.
fn make_test_module() -> TrustIrModule {
    let mut mb = ModuleBuilder::new("cli_trust_ir_text_test");
    let ty = mb.add_func_type(vec![], vec![Ty::I64]);
    let mut fb = mb.function("_return_42", ty);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let r = fb.iconst(Ty::I64, 42);
    fb.ret(vec![r]);
    fb.build();
    mb.build()
}

/// Create a fresh, empty scratch directory under the OS temp dir.
fn scratch_dir(test_name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!(
        "trust_cg_cli_trust_ir_{}_{}",
        test_name,
        std::process::id()
    ));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create scratch dir");
    dir
}

fn trust_cg_bin() -> PathBuf {
    PathBuf::from(env!("CARGO_BIN_EXE_trust-cg"))
}

// ---------------------------------------------------------------------------
// Case 1: `.trust_ir` input under `--format=text` is loaded and compiled.
// ---------------------------------------------------------------------------

#[test]
fn cli_format_text_reaches_lowering_pass() {
    let dir = scratch_dir("format_text");
    let trust_ir_path = dir.join("module.trust_ir");
    let out_path = dir.join("module.o");

    let module = make_test_module();
    let text = encode_trust_ir_text(&module);
    std::fs::write(&trust_ir_path, &text).expect("write .trust_ir");

    let output = Command::new(trust_cg_bin())
        .arg("--format=text")
        .arg("-c")
        .arg("-o")
        .arg(&out_path)
        .arg(&trust_ir_path)
        .output()
        .expect("run trust-cg");

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "--format=text should compile parsed .trust_ir input. stderr:\n{}",
        stderr
    );
    assert!(
        out_path.exists(),
        "--format=text should write {}",
        out_path.display()
    );

    let _ = std::fs::remove_dir_all(&dir);
}

// ---------------------------------------------------------------------------
// Case 2: `--format=auto` picks up `.trust_ir` by extension.
// ---------------------------------------------------------------------------

#[test]
fn cli_format_auto_picks_up_trust_ir_extension() {
    let dir = scratch_dir("auto_trust_ir");
    let trust_ir_path = dir.join("module.trust_ir");
    let out_path = dir.join("module.o");

    let module = make_test_module();
    let text = encode_trust_ir_text(&module);
    std::fs::write(&trust_ir_path, &text).expect("write .trust_ir");

    let output = Command::new(trust_cg_bin())
        .arg("--format=auto")
        .arg("-c")
        .arg("-o")
        .arg(&out_path)
        .arg(&trust_ir_path)
        .output()
        .expect("run trust-cg");

    let stderr = String::from_utf8_lossy(&output.stderr);
    // The loader must NOT mis-detect `.trust_ir` as JSON (which would
    // produce a JSON parse error). It must be recognised as text
    // and successfully parsed.
    assert!(
        !stderr.contains("JSON error"),
        "--format=auto should recognise .trust_ir extension as text, not JSON. stderr:\n{}",
        stderr
    );
    assert!(
        !stderr.contains("failed to read trust_ir module"),
        "--format=auto must NOT fail at the parser for .trust_ir input. stderr:\n{}",
        stderr
    );
    assert!(
        output.status.success(),
        "--format=auto should compile .trust_ir input. stderr:\n{}",
        stderr
    );
    assert!(
        out_path.exists(),
        "--format=auto should write {}",
        out_path.display()
    );

    let _ = std::fs::remove_dir_all(&dir);
}

// ---------------------------------------------------------------------------
// Case 3: `--emit-trust_ir` dumps a parseable .trust_ir text module.
// ---------------------------------------------------------------------------

#[test]
fn cli_emit_trust_ir_round_trips_through_parser() {
    let dir = scratch_dir("emit_trust_ir");
    let tmbc_path = dir.join("module.tmbc");
    let emitted_trust_ir = dir.join("dumped.trust_ir");

    let module = make_test_module();
    let tmbc = encode_tmbc(&module).expect("encode tMBC");
    std::fs::write(&tmbc_path, &tmbc).expect("write tmbc");

    // Call trust-cg with --emit-trust_ir; don't need a compile to succeed,
    // but request -c so we don't try to link. The .trust_ir file should
    // be written before compilation, which is what we're checking.
    let output = Command::new(trust_cg_bin())
        .arg("--emit-trust_ir")
        .arg(&emitted_trust_ir)
        .arg("-c")
        .arg("-o")
        .arg(dir.join("module.o"))
        .arg(&tmbc_path)
        .output()
        .expect("run trust-cg");

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "--emit-trust_ir should succeed. stderr: {}",
        stderr
    );
    assert!(
        emitted_trust_ir.exists(),
        "--emit-trust_ir should write {}",
        emitted_trust_ir.display()
    );

    // Round-trip: parse the emitted text back to a module.
    let text = std::fs::read_to_string(&emitted_trust_ir).expect("read emitted .trust_ir");
    let reparsed = parse_trust_ir_text(&text).expect("parse emitted .trust_ir");
    assert_eq!(reparsed.name, module.name, "module name round-trips");
    assert_eq!(
        reparsed.functions.len(),
        module.functions.len(),
        "function count round-trips"
    );

    let _ = std::fs::remove_dir_all(&dir);
}

// ---------------------------------------------------------------------------
// Case 4 (golden): the printer output starts with the canonical header.
// ---------------------------------------------------------------------------

#[test]
fn trust_ir_display_golden_header_is_stable() {
    let module = make_test_module();
    let text = encode_trust_ir_text(&module);
    // If this line changes, it is a breaking change to the text format
    // and should be propagated to downstream debuggers intentionally.
    assert!(
        text.starts_with("; TrustIr text format v1\n"),
        "expected canonical '; TrustIr text format v1' header; got:\n{}",
        text.lines().take(3).collect::<Vec<_>>().join("\n")
    );
    // Sanity: module name appears in the dump.
    assert!(
        text.contains("\"cli_trust_ir_text_test\""),
        "expected module name in text dump. got:\n{}",
        text
    );
}

// ---------------------------------------------------------------------------
// Case 5: `--emit-trust_ir` rejects multi-input invocations.
// ---------------------------------------------------------------------------

#[test]
fn cli_emit_trust_ir_rejects_multiple_inputs() {
    let dir = scratch_dir("emit_trust_ir_multi");
    let a = dir.join("a.tmbc");
    let b = dir.join("b.tmbc");
    let out = dir.join("dumped.trust_ir");

    let module = make_test_module();
    let tmbc = encode_tmbc(&module).expect("encode tMBC");
    std::fs::write(&a, &tmbc).expect("write a");
    std::fs::write(&b, &tmbc).expect("write b");

    let output = Command::new(trust_cg_bin())
        .arg("--emit-trust_ir")
        .arg(&out)
        .arg("-c")
        .arg(&a)
        .arg(&b)
        .output()
        .expect("run trust-cg");

    assert!(
        !output.status.success(),
        "--emit-trust_ir with >1 input must fail"
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("--emit-trust_ir") && stderr.contains("one input"),
        "error should mention --emit-trust_ir and one input. stderr: {}",
        stderr
    );

    let _ = std::fs::remove_dir_all(&dir);
}
