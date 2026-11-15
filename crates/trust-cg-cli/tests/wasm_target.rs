// trust-cg-cli/tests/wasm_target.rs - CLI wasm32 lane end-to-end tests
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// `--target wasm32-unknown-unknown` (alias `wasm32`) routes the CLI through
// the wasm backend (`trust_cg_codegen::wasm::compile_module`): one trust_ir
// module in, the raw `.wasm` module bytes written to `-o`, and the
// machine-readable compile-evidence summary (verification route: not_run)
// printed to stderr. These tests exercise the route end-to-end through the
// compiled binary:
//
//   1. a text-format (`.trust_ir`) module compiles to a well-formed `.wasm`;
//   2. a control-flow-bearing binary (`.tmbc`) module compiles, and the
//      default output path is the input with a `.wasm` extension;
//   3. a target-free module is REFUSED with a diagnostic naming the fix;
//   4. object-file/linker flags are REFUSED by name before input loading;
//   5. non-closed-module wasm triples (WASI, emscripten) are rejected at
//      `--target` parsing;
//   6. dropped requests (an explicit `--fsym-solver` with the preflight off)
//      are refused by name, and every `-O` level is read: -O0 emits the
//      lowering's own bodies byte for byte, -O1 to -O3 the validated local
//      emission pass, on both the closed-module and the object route;
//   7. PUBLICATION ORDER: a failed compile publishes NOTHING, and a
//      successful one publishes every requested artifact;
//   8. aliased output paths (an artifact over its own input, two artifacts
//      over one file) are refused by name;
//   9. `-c` writes a relocatable wasm object (`<input>.o`) for `wasm-ld`;
//  10. several inputs are compiled to objects and linked by `wasm-ld` into
//      one module whose cross-object call runs (skipped without `wasm-ld`;
//      the execution leg is skipped without `node`);
//  12. the codegen-license flags (`--recognize-authority`,
//      `--refuse-unlicensed`) reach both wasm32 lanes, and trust-ir's codegen
//      admission refuses an evidence-bound license with no certificate there
//      whatever the flags say.
//
// "Well-formed wasm" is not asserted by eyeballing the magic header: every
// emitted module is run through `wasmparser::Validator`, the Bytecode Alliance
// reference validator (the same gate `trust-cg-codegen`'s
// `tests/wasm_module_validation.rs` applies to the backend). Evidence is not
// asserted by substring either: the `trust-cg: wasm-evidence:` line is parsed
// as JSON and its fields — including the size and SHA-256 of the module — are
// checked against the artifact actually written.

use std::path::{Path, PathBuf};
use std::process::Command;

use trust_cg_codegen::jit_diagnostics::sha256_hex;
use trust_cg_codegen::pipeline::{OptLevel, encode_tmbc, encode_trust_ir_text};
use trust_cg_codegen::wasm;
use trust_ir::{ICmpOp, Module as TrustIrModule, Ty};
use trust_ir_build::ModuleBuilder;

const WASM_MAGIC: &[u8] = &[0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00];

/// The evidence line prefix the CLI prints for every wasm compile.
const EVIDENCE_PREFIX: &str = "trust-cg: wasm-evidence: ";

fn trust_cg_bin() -> PathBuf {
    PathBuf::from(env!("CARGO_BIN_EXE_trust-cg"))
}

/// A new scratch directory, removed when the returned guard is dropped.
fn scratch_dir(test_name: &str) -> scratch::ScratchDir {
    scratch::create(&format!("trust_cg_cli_wasm_{test_name}_"))
}

/// `fn seven() -> i32 { 7 }`, pinned to the wasm32 lane.
fn make_const_module() -> TrustIrModule {
    let mut mb = ModuleBuilder::new("cli_wasm_const");
    let ty = mb.add_func_type(vec![], vec![Ty::I32]);
    let mut fb = mb.function("seven", ty);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let c = fb.iconst(Ty::I32, 7);
    fb.ret(vec![c]);
    fb.build();
    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
    module.target_info = Some(wasm::wasm32_target_info());
    module
}

/// gcd(a, b) by modulo — a reducible loop through the relooper (the difftest
/// corpus's `gcd_mod_loop` shape), pinned to the wasm32 lane.
fn make_gcd_module() -> TrustIrModule {
    let mut mb = ModuleBuilder::new("cli_wasm_gcd");
    let ft = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);
    let mut fb = mb.function("gcd", ft);
    let entry = fb.create_block();
    let ghead = fb.create_block();
    let gstep = fb.create_block();
    let exit = fb.create_block();
    let a0 = fb.add_block_param(entry, Ty::I32);
    let b0 = fb.add_block_param(entry, Ty::I32);
    let gx = fb.add_block_param(ghead, Ty::I32);
    let gy = fb.add_block_param(ghead, Ty::I32);
    let sx = fb.add_block_param(gstep, Ty::I32);
    let sy = fb.add_block_param(gstep, Ty::I32);
    let g = fb.add_block_param(exit, Ty::I32);
    fb.switch_to_block(entry);
    fb.br(ghead, vec![a0, b0]);
    fb.switch_to_block(ghead);
    let z = fb.iconst(Ty::I32, 0);
    let ne = fb.icmp(ICmpOp::Ne, Ty::I32, gy, z);
    fb.condbr(ne, gstep, vec![gx, gy], exit, vec![gx]);
    fb.switch_to_block(gstep);
    let rem = fb.binop(trust_ir::BinOp::URem, Ty::I32, sx, sy);
    fb.br(ghead, vec![sy, rem]);
    fb.switch_to_block(exit);
    fb.ret(vec![g]);
    fb.build();
    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
    module.target_info = Some(wasm::wasm32_target_info());
    module
}

/// Read the emitted module and assert it is a REAL wasm module: the magic
/// header, a body beyond it, and acceptance by the Bytecode Alliance reference
/// validator (an independent implementation of the spec — not our encoder's
/// own invariants). Returns the bytes so the caller can bind evidence to them.
fn read_validated_wasm(path: &Path) -> Vec<u8> {
    let bytes = std::fs::read(path)
        .unwrap_or_else(|e| panic!("read emitted wasm at {}: {e}", path.display()));
    assert!(
        bytes.len() > WASM_MAGIC.len() && &bytes[..WASM_MAGIC.len()] == WASM_MAGIC,
        "{} is not a wasm module ({} bytes)",
        path.display(),
        bytes.len(),
    );
    wasmparser::Validator::new()
        .validate_all(&bytes)
        .unwrap_or_else(|e| {
            panic!(
                "emitted wasm at {} REJECTED by the reference validator ({} bytes): {e}",
                path.display(),
                bytes.len(),
            )
        });
    bytes
}

/// Parse the single `trust-cg: wasm-evidence:` line out of stderr as JSON.
fn parse_evidence(stderr: &str) -> serde_json::Value {
    let line = stderr
        .lines()
        .find(|line| line.starts_with(EVIDENCE_PREFIX))
        .unwrap_or_else(|| panic!("no `{EVIDENCE_PREFIX}` line on stderr:\n{stderr}"));
    serde_json::from_str(&line[EVIDENCE_PREFIX.len()..])
        .unwrap_or_else(|e| panic!("evidence line is not JSON ({e}):\n{line}"))
}

/// Assert the parsed evidence tells the truth about the artifact that was
/// actually written: the honest not_run verification route, the function
/// count, and a size and digest that match the bytes on disk.
fn assert_evidence_describes(evidence: &serde_json::Value, bytes: &[u8], function_count: u64) {
    assert_eq!(
        evidence["schema"], "trust-cg.wasm_compile_evidence.v1",
        "unexpected evidence schema: {evidence}"
    );
    assert_eq!(evidence["target"], "wasm32-unknown-unknown", "{evidence}");
    assert_eq!(
        evidence["verification_route"], "not_run",
        "the wasm lane runs no verifier and must say so: {evidence}"
    );
    assert_eq!(evidence["verdict"], "missing_evidence", "{evidence}");
    assert_eq!(
        evidence["function_count"],
        serde_json::json!(function_count),
        "{evidence}"
    );
    assert_eq!(
        evidence["module_size_bytes"],
        serde_json::json!(bytes.len()),
        "evidence size must match the {} bytes written: {evidence}",
        bytes.len(),
    );
    assert_eq!(
        evidence["module_sha256"],
        serde_json::json!(sha256_hex(bytes)),
        "evidence digest must match the bytes written: {evidence}"
    );
}

// ---------------------------------------------------------------------------
// 1. End-to-end: text-format module -> .wasm bytes at -o.
// ---------------------------------------------------------------------------

#[test]
fn cli_wasm32_compiles_text_format_module_end_to_end() {
    let dir = scratch_dir("text_end_to_end");
    let trust_ir_path = dir.join("module.trust_ir");
    let out_path = dir.join("module.wasm");

    // The `.trust_ir` text round-trips the wasm32 target pin
    // (`target "wasm32-unknown-unknown" 4 little ...`).
    let text = encode_trust_ir_text(&make_const_module());
    assert!(
        text.contains("wasm32-unknown-unknown"),
        "text form must carry the target pin:\n{text}"
    );
    std::fs::write(&trust_ir_path, &text).expect("write .trust_ir");

    let output = Command::new(trust_cg_bin())
        .arg("--permit-unlicensed")
        .arg("--format=text")
        .arg("--target")
        .arg("wasm32-unknown-unknown")
        .arg("-o")
        .arg(&out_path)
        .arg(&trust_ir_path)
        .output()
        .expect("run trust-cg");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "wasm32 text compile should succeed. stderr:\n{stderr}"
    );
    let bytes = read_validated_wasm(&out_path);

    // The honest evidence summary is on stderr: this route ran no verifier,
    // and every field it states matches the artifact on disk.
    assert_evidence_describes(&parse_evidence(&stderr), &bytes, 1);
    assert!(
        stderr.contains("compiled 1 function(s)"),
        "missing summary line. stderr:\n{stderr}"
    );
}

// ---------------------------------------------------------------------------
// 2. End-to-end: control-flow-bearing .tmbc module, default output path.
// ---------------------------------------------------------------------------

#[test]
fn cli_wasm32_compiles_tmbc_loop_module_with_default_output_path() {
    let dir = scratch_dir("tmbc_default_out");
    let tmbc_path = dir.join("gcd.tmbc");
    let bytes = encode_tmbc(&make_gcd_module()).expect("encode tMBC");
    std::fs::write(&tmbc_path, &bytes).expect("write .tmbc");

    // The bare `wasm32` alias, no -o: output derives as `<input>.wasm`.
    let output = Command::new(trust_cg_bin())
        .arg("--permit-unlicensed")
        .arg("--target")
        .arg("wasm32")
        .arg(&tmbc_path)
        .output()
        .expect("run trust-cg");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "wasm32 tmbc compile should succeed. stderr:\n{stderr}"
    );
    let wasm_bytes = read_validated_wasm(&dir.join("gcd.wasm"));
    assert_evidence_describes(&parse_evidence(&stderr), &wasm_bytes, 1);
    assert!(
        stderr.contains("(wasm32-unknown-unknown)"),
        "summary should name the wasm target. stderr:\n{stderr}"
    );
}

// ---------------------------------------------------------------------------
// 3. A target-free module is refused, naming the fix.
// ---------------------------------------------------------------------------

#[test]
fn cli_wasm32_refuses_target_free_module() {
    let dir = scratch_dir("target_free");
    let tmbc_path = dir.join("free.tmbc");
    let mut module = make_const_module();
    module.target_info = None; // deliberately target-free
    let bytes = encode_tmbc(&module).expect("encode tMBC");
    std::fs::write(&tmbc_path, &bytes).expect("write .tmbc");

    let output = Command::new(trust_cg_bin())
        .arg("--permit-unlicensed")
        .arg("--target")
        .arg("wasm32-unknown-unknown")
        .arg(&tmbc_path)
        .output()
        .expect("run trust-cg");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !output.status.success(),
        "a target-free module must be refused. stderr:\n{stderr}"
    );
    assert!(
        stderr.contains("target_info") && stderr.contains("wasm32_target_info"),
        "the refusal must name the missing pin and the fix. stderr:\n{stderr}"
    );
    assert!(
        !dir.join("free.wasm").exists(),
        "a refused compile must publish no module"
    );
}

// ---------------------------------------------------------------------------
// 4. Object-file/linker options are refused by name, before input loading.
// ---------------------------------------------------------------------------

#[test]
fn cli_wasm32_refuses_linker_and_object_flags_by_name() {
    let output = Command::new(trust_cg_bin())
        .arg("--permit-unlicensed")
        .arg("--target")
        .arg("wasm32")
        .arg("-g")
        .arg("-L")
        .arg("/nonexistent-libdir")
        .arg("-l")
        .arg("m")
        .arg("--emit-proofs")
        .arg("/nonexistent-proofs")
        .arg("does-not-exist.tmbc")
        .output()
        .expect("run trust-cg");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !output.status.success(),
        "inapplicable flags must be refused. stderr:\n{stderr}"
    );
    for flag in ["-g:", "-L:", "-l:", "--emit-proofs:"] {
        assert!(
            stderr.contains(flag),
            "expected a named refusal for {flag}. stderr:\n{stderr}"
        );
    }
    assert!(
        !stderr.contains("failed to read trust_ir module"),
        "flag refusal must fire before input loading. stderr:\n{stderr}"
    );
}

// ---------------------------------------------------------------------------
// 5. Non-closed-module wasm triples are rejected at --target parsing.
// ---------------------------------------------------------------------------

#[test]
fn cli_rejects_wasi_and_emscripten_wasm_triples_at_target_parsing() {
    for target in ["wasm32-wasip1", "wasm32-wasi", "wasm32-unknown-emscripten"] {
        let output = Command::new(trust_cg_bin())
            .arg("--permit-unlicensed")
            .arg("--target")
            .arg(target)
            .arg("unused.tmbc")
            .output()
            .unwrap_or_else(|e| panic!("run trust-cg for {target}: {e}"));
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            !output.status.success(),
            "{target} must be rejected at --target parsing"
        );
        assert!(
            stderr.contains("closed-module") && stderr.contains("wasm32-unknown-unknown"),
            "{target} rejection must point at the closed-module lane. stderr:\n{stderr}"
        );
        assert!(
            !stderr.contains("failed to read trust_ir module"),
            "{target} must fail while parsing --target. stderr:\n{stderr}"
        );
    }
}

// ---------------------------------------------------------------------------
// 6. Dropped requests are refused by name; every -O level is read.
// ---------------------------------------------------------------------------

/// Compile `input` through the CLI's wasm lane with `flags`, writing `out`;
/// returns the validated bytes and the parsed evidence line.
fn compile_wasm_with(input: &Path, out: &Path, flags: &[&str]) -> (Vec<u8>, serde_json::Value) {
    let run = Command::new(trust_cg_bin())
        .arg("--permit-unlicensed")
        .args(["--format=text", "--target", "wasm32-unknown-unknown"])
        .args(flags)
        .arg(input)
        .arg("-o")
        .arg(out)
        .output()
        .expect("run trust-cg");
    let stderr = String::from_utf8_lossy(&run.stderr);
    assert!(
        run.status.success(),
        "{flags:?} must compile. stderr:\n{stderr}"
    );
    assert!(
        !stderr.contains("-O/--opt-level"),
        "no -O level is refused, got: {stderr}"
    );
    (read_validated_wasm(out), parse_evidence(&stderr))
}

/// Every `-O` level is a request the closed-module route reads. -O0 emits
/// each function's baseline body: the bytes the codegen library emits at O0,
/// with the local emission pass reported as not enabled. -O1, -O2 and -O3
/// run the pass; the default level is -O2. The loop module has copies the
/// pass removes, so O0 and O2 differ.
#[test]
fn every_opt_level_reaches_the_closed_module_route() {
    let dir = scratch_dir("opt_levels_closed");
    let module = make_gcd_module();
    let input = dir.join("gcd.trust_ir");
    std::fs::write(&input, encode_trust_ir_text(&module)).expect("write input");
    let mut by_level = Vec::new();
    for (flag, level) in [
        ("-O0", OptLevel::O0),
        ("-O1", OptLevel::O1),
        ("-O2", OptLevel::O2),
        ("-O3", OptLevel::O3),
    ] {
        let out = dir.join(format!("gcd{flag}.wasm"));
        let (bytes, evidence) = compile_wasm_with(&input, &out, &[flag]);
        assert_evidence_describes(&evidence, &bytes, 1);
        let (library, _) = wasm::compile_sized_closed_module_with_evidence_license_optimized(
            &module,
            &permit_unlicensed(),
            level,
        )
        .expect("library compile");
        assert_eq!(
            bytes, library,
            "{flag} must emit the codegen library's bytes at {level:?}"
        );
        assert_eq!(
            evidence["local_emission"]["enabled"],
            serde_json::json!(level != OptLevel::O0),
            "{flag}: {evidence}"
        );
        by_level.push(bytes);
    }
    let (default, _) = compile_wasm_with(&input, &dir.join("gcd-default.wasm"), &[]);
    assert_eq!(default, by_level[2], "the default level is -O2");
    assert_ne!(
        by_level[0], by_level[2],
        "-O0 must keep the lowering's body, which the pass rewrites at -O2"
    );
}

/// The object route (`-c`) reads `-O` too: -O0 is the library's O0 object
/// (the lowering's bodies) and -O2 its O2 object, and they differ.
#[test]
fn every_opt_level_reaches_the_object_route() {
    let dir = scratch_dir("opt_levels_object");
    let module = make_gcd_module();
    let input = dir.join("gcd.trust_ir");
    std::fs::write(&input, encode_trust_ir_text(&module)).expect("write input");
    let mut by_level = Vec::new();
    for (flag, level) in [
        ("-O0", OptLevel::O0),
        ("-O1", OptLevel::O1),
        ("-O2", OptLevel::O2),
        ("-O3", OptLevel::O3),
    ] {
        let out = dir.join(format!("gcd{flag}.o"));
        let (bytes, evidence) = compile_wasm_with(&input, &out, &["-c", flag]);
        let (library, _) = wasm::compile_object_with_evidence_license_optimized(
            &module,
            &permit_unlicensed(),
            level,
        )
        .expect("library compile");
        assert_eq!(
            bytes, library,
            "-c {flag} must emit the codegen library's object at {level:?}"
        );
        assert_eq!(
            evidence["local_emission"]["enabled"],
            serde_json::json!(level != OptLevel::O0),
            "-c {flag}: {evidence}"
        );
        by_level.push(bytes);
    }
    assert_ne!(
        by_level[0], by_level[2],
        "-c -O0 must keep the lowering's body"
    );
}

/// An invalid level is still refused at argument parsing.
#[test]
fn an_unknown_opt_level_is_refused() {
    let dir = scratch_dir("opt_level_unknown");
    let input = dir.join("m.trust_ir");
    std::fs::write(&input, encode_trust_ir_text(&make_const_module())).expect("write input");
    let out = Command::new(trust_cg_bin())
        .arg("--permit-unlicensed")
        .args(["--format=text", "--target", "wasm32-unknown-unknown", "-Os"])
        .arg(&input)
        .output()
        .expect("run trust-cg");
    assert!(!out.status.success(), "-Os is not a level this CLI has");
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        stderr.contains("invalid optimization level"),
        "got: {stderr}"
    );
    assert!(!input.with_extension("wasm").exists(), "nothing is written");
}

/// The DEFAULT opt level: no refusal is emitted, the run SUCCEEDS, and the module it publishes is a real, validated wasm module
/// whose evidence matches the bytes on disk. (Asserting only the absence of
/// the refusal string would pass on a compile that failed outright.)
#[test]
fn default_opt_level_is_not_refused() {
    let dir = scratch_dir("default_opt_level");
    let input = dir.join("m.trust_ir");
    std::fs::write(&input, encode_trust_ir_text(&make_const_module())).expect("write input");
    let out = dir.join("m.wasm");

    let run = Command::new(trust_cg_bin())
        .arg("--permit-unlicensed")
        .args(["--format=text", "--target", "wasm32-unknown-unknown", "-c"])
        .arg(&input)
        .arg("-o")
        .arg(&out)
        .output()
        .expect("run trust-cg");

    let stderr = String::from_utf8_lossy(&run.stderr);
    assert!(
        !stderr.contains("-O/--opt-level"),
        "the default opt level must not be refused, got: {stderr}"
    );
    assert!(
        run.status.success(),
        "the default opt level must compile. stderr:\n{stderr}"
    );
    let bytes = read_validated_wasm(&out);
    assert_evidence_describes(&parse_evidence(&stderr), &bytes, 1);
}

/// `--fsym-solver` is only read while the preflight runs, so passing it under
/// the default `--fsym=off` is a dropped request and is refused by name. (The rule is CLI-wide; it is
/// exercised here on the wasm lane, where the sibling dropped-request refusals
/// live.)
#[test]
fn explicit_fsym_solver_without_the_preflight_is_refused() {
    let dir = scratch_dir("fsym_solver_dropped");
    let input = dir.join("m.trust_ir");
    std::fs::write(&input, encode_trust_ir_text(&make_const_module())).expect("write input");
    let out = dir.join("m.wasm");

    let refused = Command::new(trust_cg_bin())
        .arg("--permit-unlicensed")
        .args([
            "--format=text",
            "--target",
            "wasm32-unknown-unknown",
            "--fsym-solver=local",
        ])
        .arg("-o")
        .arg(&out)
        .arg(&input)
        .output()
        .expect("run trust-cg");
    let stderr = String::from_utf8_lossy(&refused.stderr);
    assert!(
        !refused.status.success(),
        "an explicit --fsym-solver with the preflight off must be refused. stderr:\n{stderr}"
    );
    assert!(
        stderr.contains("--fsym-solver requires --fsym=warn or --fsym=error"),
        "the refusal must name the flag and the fix. stderr:\n{stderr}"
    );
    assert!(
        !out.exists(),
        "a refused invocation must write no artifacts"
    );

    // With the preflight actually on, the same solver request is honoured and
    // the compile publishes its module.
    let accepted = Command::new(trust_cg_bin())
        .arg("--permit-unlicensed")
        .args([
            "--format=text",
            "--target",
            "wasm32-unknown-unknown",
            "--fsym=warn",
            "--fsym-solver=local",
        ])
        .arg("-o")
        .arg(&out)
        .arg(&input)
        .output()
        .expect("run trust-cg");
    let stderr = String::from_utf8_lossy(&accepted.stderr);
    assert!(
        accepted.status.success(),
        "--fsym-solver under --fsym=warn must be accepted. stderr:\n{stderr}"
    );
    let bytes = read_validated_wasm(&out);
    assert_evidence_describes(&parse_evidence(&stderr), &bytes, 1);
}

// ---------------------------------------------------------------------------
// 7. Publication order: nothing is published until the compile succeeds.
// ---------------------------------------------------------------------------

/// A module the BACKEND refuses (target-free) must leave no artifact behind,
/// including the `--emit-json` / `--emit-trust_ir` round-trip files, which are
/// requested before the compile but published only after it.
#[test]
fn wasm32_publishes_nothing_when_the_backend_refuses_the_module() {
    let dir = scratch_dir("publication_order_refused");
    let tmbc_path = dir.join("free.tmbc");
    let mut module = make_const_module();
    module.target_info = None; // refused by the backend's target-info guard
    std::fs::write(&tmbc_path, encode_tmbc(&module).expect("encode tMBC")).expect("write .tmbc");

    let json = dir.join("round-trip.json");
    let text = dir.join("round-trip.trust_ir");
    let out = dir.join("out.wasm");

    let run = Command::new(trust_cg_bin())
        .arg("--permit-unlicensed")
        .args(["--target", "wasm32-unknown-unknown", "--emit-json"])
        .arg(&json)
        .arg("--emit-trust_ir")
        .arg(&text)
        .arg("-o")
        .arg(&out)
        .arg(&tmbc_path)
        .output()
        .expect("run trust-cg");
    let stderr = String::from_utf8_lossy(&run.stderr);

    assert!(
        !run.status.success(),
        "a target-free module must be refused. stderr:\n{stderr}"
    );
    assert!(
        stderr.contains("target_info"),
        "the refusal must name the missing pin. stderr:\n{stderr}"
    );
    for artifact in [&json, &text, &out] {
        assert!(
            !artifact.exists(),
            "{} was published by a FAILED compile. stderr:\n{stderr}",
            artifact.display(),
        );
    }
}

/// The mirror image: a compile that succeeds publishes every requested
/// artifact, and each one is real — the JSON round-trips back into a module,
/// the `.trust_ir` text carries the target pin, and the `.wasm` validates.
#[test]
fn wasm32_publishes_every_requested_artifact_after_a_successful_compile() {
    let dir = scratch_dir("publication_order_ok");
    let tmbc_path = dir.join("const.tmbc");
    let module = make_const_module();
    std::fs::write(&tmbc_path, encode_tmbc(&module).expect("encode tMBC")).expect("write .tmbc");

    let json = dir.join("round-trip.json");
    let text = dir.join("round-trip.trust_ir");
    let out = dir.join("out.wasm");

    let run = Command::new(trust_cg_bin())
        .arg("--permit-unlicensed")
        .args(["--target", "wasm32-unknown-unknown", "--emit-json"])
        .arg(&json)
        .arg("--emit-trust_ir")
        .arg(&text)
        .arg("-o")
        .arg(&out)
        .arg(&tmbc_path)
        .output()
        .expect("run trust-cg");
    let stderr = String::from_utf8_lossy(&run.stderr);
    assert!(
        run.status.success(),
        "the compile should succeed. stderr:\n{stderr}"
    );

    let round_tripped: TrustIrModule =
        serde_json::from_str(&std::fs::read_to_string(&json).expect("read emitted JSON"))
            .expect("emitted JSON must round-trip into a trust_ir module");
    assert_eq!(round_tripped.name, module.name);
    assert_eq!(round_tripped.functions.len(), module.functions.len());

    let emitted_text = std::fs::read_to_string(&text).expect("read emitted .trust_ir text");
    assert!(
        emitted_text.contains("wasm32-unknown-unknown") && emitted_text.contains("seven"),
        "the .trust_ir text must carry the pin and the function:\n{emitted_text}"
    );

    let bytes = read_validated_wasm(&out);
    assert_evidence_describes(&parse_evidence(&stderr), &bytes, 1);
}

// ---------------------------------------------------------------------------
// 8. Aliased output paths are refused by name.
// ---------------------------------------------------------------------------

/// `--format=text --emit-json <input> <input>` would overwrite the input with
/// JSON before it is read as text. The alias is refused by name, and the input
/// is left exactly as it was.
#[test]
fn wasm32_refuses_an_output_path_that_aliases_the_input() {
    let dir = scratch_dir("alias_over_input");
    let input = dir.join("m.trust_ir");
    let source = encode_trust_ir_text(&make_const_module());
    std::fs::write(&input, &source).expect("write input");

    let run = Command::new(trust_cg_bin())
        .arg("--permit-unlicensed")
        .args(["--format=text", "--target", "wasm32-unknown-unknown"])
        .arg("--emit-json")
        .arg(&input)
        .arg(&input)
        .output()
        .expect("run trust-cg");
    let stderr = String::from_utf8_lossy(&run.stderr);

    assert!(
        !run.status.success(),
        "an emit path that names the input must be refused. stderr:\n{stderr}"
    );
    assert!(
        stderr.contains("--emit-json:") && stderr.contains("input module"),
        "the refusal must name the flag and the collision. stderr:\n{stderr}"
    );
    assert_eq!(
        std::fs::read_to_string(&input).expect("read input back"),
        source,
        "the input module must be untouched by a refused run"
    );
}

/// Two requested outputs that resolve to one file mean one of them is silently
/// lost — a dropped request. `./out.json` and `out.json` are recognised as the
/// same file even though neither exists yet.
#[test]
fn wasm32_refuses_two_outputs_that_name_one_file() {
    let dir = scratch_dir("alias_output_collision");
    let input = dir.join("m.tmbc");
    std::fs::write(
        &input,
        encode_tmbc(&make_const_module()).expect("encode tMBC"),
    )
    .expect("write input");

    let json = dir.join("out.json");
    let aliased = dir.join(".").join("out.json");

    let run = Command::new(trust_cg_bin())
        .arg("--permit-unlicensed")
        .args(["--target", "wasm32-unknown-unknown", "--emit-json"])
        .arg(&json)
        .arg("-o")
        .arg(&aliased)
        .arg(&input)
        .output()
        .expect("run trust-cg");
    let stderr = String::from_utf8_lossy(&run.stderr);

    assert!(
        !run.status.success(),
        "two outputs naming one file must be refused. stderr:\n{stderr}"
    );
    assert!(
        stderr.contains("--emit-json:") && stderr.contains("-o/--output"),
        "the refusal must name BOTH requests. stderr:\n{stderr}"
    );
    assert!(
        !json.exists(),
        "a refused invocation must write no artifacts"
    );
}

// ---------------------------------------------------------------------------
// 9./10. Relocatable objects and wasm-ld linking.
// ---------------------------------------------------------------------------

const GCD_TEXT: &str = "module \"gcd_unit\"\ntarget \"wasm32-unknown-unknown\" 4 little\n\n\
    functy.0 = (i32, i32) -> (i32)\n\n\
    fn @gcd(functy.0) {\n\
    bb0(%1: i32, %2: i32):\n\
    \x20   br bb1(%1, %2)\n\
    bb1(%3: i32, %4: i32):\n\
    \x20   %5 = const i32 0\n\
    \x20   %6 = icmp ne i32 %4, %5\n\
    \x20   condbr %6, bb2, bb3\n\
    bb2:\n\
    \x20   %7 = urem i32 %3, %4\n\
    \x20   br bb1(%4, %7)\n\
    bb3:\n\
    \x20   ret %3\n\
    }\n";

/// `lcm(a, b) = a / gcd(a, b) * b`, calling the `gcd` another object defines.
const LCM_TEXT: &str = "module \"lcm_unit\"\ntarget \"wasm32-unknown-unknown\" 4 little\n\n\
    functy.0 = (i32, i32) -> (i32)\n\n\
    fn @gcd(functy.0) {\n}\n\n\
    fn @lcm(functy.0) {\n\
    bb0(%1: i32, %2: i32):\n\
    \x20   %3 = call @func.0(%1, %2)\n\
    \x20   %4 = udiv i32 %1, %3\n\
    \x20   %5 = mul i32 %4, %2\n\
    \x20   ret %5\n\
    }\n";

fn wasm_ld() -> Option<PathBuf> {
    if let Some(path) = std::env::var_os("WASM_LD") {
        return Some(PathBuf::from(path));
    }
    std::env::split_paths(&std::env::var_os("PATH")?)
        .map(|dir| dir.join("wasm-ld"))
        .find(|candidate| candidate.is_file())
}

#[test]
fn wasm32_compile_only_writes_a_relocatable_object() {
    let dir = scratch_dir("compile_only_object");
    let input = dir.join("gcd.trust_ir");
    std::fs::write(&input, GCD_TEXT).expect("write input");
    let output = Command::new(trust_cg_bin())
        .arg("--permit-unlicensed")
        .args(["--format=text", "--target", "wasm32", "-c"])
        .arg(&input)
        .output()
        .expect("run trust-cg");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "-c should succeed. stderr:\n{stderr}"
    );
    let object = dir.join("gcd.o");
    assert!(
        stderr.contains("relocatable object"),
        "missing object summary line. stderr:\n{stderr}"
    );
    let bytes = read_validated_wasm(&object);
    // A relocatable object carries the tool-conventions `linking` section
    // wasm-ld reads (with its symbol table), and no memory of its own.
    let mut linking = false;
    let mut defines_memory = false;
    for payload in wasmparser::Parser::new(0).parse_all(&bytes) {
        match payload.expect("parse object") {
            wasmparser::Payload::CustomSection(c) if c.name() == "linking" => linking = true,
            wasmparser::Payload::MemorySection(_) => defines_memory = true,
            _ => {}
        }
    }
    assert!(linking, "the object has no `linking` section");
    assert!(
        !defines_memory,
        "a relocatable object must not define its own memory"
    );
    assert!(!dir.join("gcd.wasm").exists(), "-c must not write a module");
}

#[test]
fn wasm32_links_several_inputs_with_wasm_ld() {
    let Some(linker) = wasm_ld() else {
        eprintln!(
            "wasm32_links_several_inputs_with_wasm_ld: SKIPPED — no wasm-ld (WASM_LD / PATH)"
        );
        return;
    };
    let dir = scratch_dir("link_two_inputs");
    let (gcd, lcm, out) = (
        dir.join("gcd.trust_ir"),
        dir.join("lcm.trust_ir"),
        dir.join("app.wasm"),
    );
    std::fs::write(&gcd, GCD_TEXT).expect("write gcd");
    std::fs::write(&lcm, LCM_TEXT).expect("write lcm");
    let output = Command::new(trust_cg_bin())
        .arg("--permit-unlicensed")
        .args(["--format=text", "--target", "wasm32", "--wasm-ld"])
        .arg(&linker)
        .arg("-o")
        .arg(&out)
        .arg(&lcm)
        .arg(&gcd)
        .output()
        .expect("run trust-cg");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "linking should succeed. stderr:\n{stderr}"
    );
    let bytes = read_validated_wasm(&out);
    let mut exports = Vec::new();
    for payload in wasmparser::Parser::new(0).parse_all(&bytes) {
        if let wasmparser::Payload::ExportSection(r) = payload.expect("parse module") {
            exports.extend(r.into_iter().map(|e| e.expect("export").name.to_owned()));
        }
    }
    for name in ["gcd", "lcm"] {
        assert!(
            exports.iter().any(|e| e == name),
            "`{name}` not exported: {exports:?}"
        );
    }
    let Some(node) = std::env::split_paths(&std::env::var_os("PATH").unwrap_or_default())
        .map(|d| d.join("node"))
        .find(|c| c.is_file())
    else {
        eprintln!("wasm32_links_several_inputs_with_wasm_ld: execution leg SKIPPED — no node");
        return;
    };
    let run = Command::new(node)
        .arg("-e")
        .arg(
            "const E = new WebAssembly.Instance(new WebAssembly.Module(\
             require('fs').readFileSync(process.argv[1])), {}).exports; \
             console.log(E.lcm(4, 6), E.lcm(21, 6), E.gcd(48, 18));",
        )
        .arg(&out)
        .output()
        .expect("run node");
    assert_eq!(
        String::from_utf8_lossy(&run.stdout).trim(),
        "12 42 6",
        "stderr: {}",
        String::from_utf8_lossy(&run.stderr)
    );
}

/// `counter` is a data global; `bump` increments it through its address.
const COUNTER_TEXT: &str = "module \"counter_unit\"\ntarget \"wasm32-unknown-unknown\" 4 little\n\n\
    functy.0 = () -> (i32)\n\n\
    global mut @counter i32 = 41\n\n\
    fn @bump(functy.0) {\n\
    bb0:\n\
    \x20   %1 = global_addr @global.0\n\
    \x20   %2 = load i32, ptr %1\n\
    \x20   %3 = const i32 1\n\
    \x20   %4 = add i32 %2, %3\n\
    \x20   store i32 %4, ptr %1\n\
    \x20   ret %4\n\
    }\n";

/// A linker named like the generic lld driver (`rust-lld`, as rustup ships
/// it) is run with `-flavor wasm` when given by `--wasm-ld`, exactly as when
/// it is found on PATH; and the link lays the 1 MiB shadow stack out BELOW
/// static data (`--stack-first`, as rustc links wasm32), so static data
/// starts above the stack.
#[cfg(unix)]
#[test]
fn wasm32_links_through_a_generic_rust_lld_driver_with_the_stack_first() {
    let Some(linker) = wasm_ld() else {
        eprintln!(
            "wasm32_links_through_a_generic_rust_lld_driver_with_the_stack_first: SKIPPED — no \
             wasm-ld (WASM_LD / PATH)"
        );
        return;
    };
    let dir = scratch_dir("rust_lld_flavor");
    // lld selects its driver from argv[0]: a `rust-lld` name selects none.
    let rust_lld = dir.join("rust-lld");
    std::os::unix::fs::symlink(&linker, &rust_lld).expect("symlink rust-lld");
    let (counter, gcd, out) = (
        dir.join("counter.trust_ir"),
        dir.join("gcd.trust_ir"),
        dir.join("app.wasm"),
    );
    std::fs::write(&counter, COUNTER_TEXT).expect("write counter");
    std::fs::write(&gcd, GCD_TEXT).expect("write gcd");
    let output = Command::new(trust_cg_bin())
        .arg("--permit-unlicensed")
        .args(["--format=text", "--target", "wasm32", "--wasm-ld"])
        .arg(&rust_lld)
        .arg("-o")
        .arg(&out)
        .arg(&counter)
        .arg(&gcd)
        .output()
        .expect("run trust-cg");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "linking through rust-lld should succeed. stderr:\n{stderr}"
    );
    let bytes = read_validated_wasm(&out);
    // Every active data segment sits at or above the 1 MiB stack.
    let mut offsets = Vec::new();
    for payload in wasmparser::Parser::new(0).parse_all(&bytes) {
        if let wasmparser::Payload::DataSection(r) = payload.expect("parse module") {
            for data in r {
                if let wasmparser::DataKind::Active { offset_expr, .. } =
                    data.expect("data segment").kind
                {
                    let mut ops = offset_expr.get_operators_reader();
                    if let wasmparser::Operator::I32Const { value } = ops.read().expect("op") {
                        offsets.push(value);
                    }
                }
            }
        }
    }
    assert!(!offsets.is_empty(), "the counter's data segment is missing");
    assert!(
        offsets.iter().all(|&o| o >= 1 << 20),
        "static data must sit above the 1 MiB stack: {offsets:?}"
    );
    let Some(node) = std::env::split_paths(&std::env::var_os("PATH").unwrap_or_default())
        .map(|d| d.join("node"))
        .find(|c| c.is_file())
    else {
        eprintln!("rust-lld link: execution leg SKIPPED — no node");
        return;
    };
    let run = Command::new(node)
        .arg("-e")
        .arg(
            "const E = new WebAssembly.Instance(new WebAssembly.Module(\
             require('fs').readFileSync(process.argv[1])), {}).exports; \
             console.log(E.bump(), E.bump(), E.gcd(48, 18));",
        )
        .arg(&out)
        .output()
        .expect("run node");
    assert_eq!(
        String::from_utf8_lossy(&run.stdout).trim(),
        "42 43 6",
        "stderr: {}",
        String::from_utf8_lossy(&run.stderr)
    );
}

// ---------------------------------------------------------------------------
// 11. The closed module sizes its memory to its static data; builds are
//     reproducible; the link refuses an export named like the memory.
// ---------------------------------------------------------------------------

/// A 72,000-byte immutable table read by index: past the one page the
/// default closed module owns.
fn big_table_text() -> String {
    let values: Vec<String> = (0..18_000u32)
        .map(|i| ((i * 7919) % 100_003).to_string())
        .collect();
    format!(
        "module \"big\"\ntarget \"wasm32-unknown-unknown\" 4 little\n\ntype ty.0 = i32\n\n\
         functy.0 = (i32) -> (i32)\n\nglobal @big [ty.0 x 18000] = array[ {} ]\n\n\
         fn @at(functy.0) {{\nbb0(%1: i32):\n    %2 = global_addr @global.0\n\
             %3 = gep i32, ptr %2, %1\n    %4 = load i32, ptr %3\n    ret %4\n}}\n",
        values.join(", ")
    )
}

#[test]
fn wasm32_closed_module_holds_static_data_past_one_page() {
    let dir = scratch_dir("big_static_data");
    let input = dir.join("big.trust_ir");
    let out = dir.join("big.wasm");
    std::fs::write(&input, big_table_text()).expect("write input");
    let output = Command::new(trust_cg_bin())
        .arg("--permit-unlicensed")
        .args(["--format=text", "--target", "wasm32", "-o"])
        .arg(&out)
        .arg(&input)
        .output()
        .expect("run trust-cg");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(output.status.success(), "stderr:\n{stderr}");
    let bytes = read_validated_wasm(&out);
    let Some(node) = std::env::split_paths(&std::env::var_os("PATH").unwrap_or_default())
        .map(|d| d.join("node"))
        .find(|c| c.is_file())
    else {
        return;
    };
    let run = Command::new(node)
        .arg("-e")
        .arg(
            "const E = new WebAssembly.Instance(new WebAssembly.Module(\
             require('fs').readFileSync(process.argv[1])), {}).exports; \
             console.log(E.at(0), E.at(1), E.at(17999));",
        )
        .arg(&out)
        .output()
        .expect("run node");
    let want = |i: u32| (i * 7919) % 100_003;
    assert_eq!(
        String::from_utf8_lossy(&run.stdout).trim(),
        format!("{} {} {}", want(0), want(1), want(17_999)),
        "{} bytes; stderr: {}",
        bytes.len(),
        String::from_utf8_lossy(&run.stderr)
    );
}

/// Homes that never conflict share one frame offset; their order must not
/// follow a hash map's. Two separate processes (fresh hash seeds) emit the
/// same bytes and the same evidence digest, closed and as an object.
#[test]
fn wasm32_output_is_reproducible_across_processes() {
    let dir = scratch_dir("reproducible");
    let input = dir.join("tie.trust_ir");
    let mut text = String::from(
        "module \"tie\"\ntarget \"wasm32-unknown-unknown\" 4 little\n\n\
         struct @P { : i32 @0, : i32 @4 } size=8 align=4 id=0\n\n\
         functy.0 = (i32, i32) -> (i32)\n\nfn @f(functy.0) {\nbb0(%0: i32, %1: i32):\n",
    );
    let mut last = 0;
    let mut next = 2;
    for _ in 0..16 {
        text.push_str(&format!(
            "    %{} = make_aggregate struct.0 (%{last}, %1)\n    %{} = extractfield i32 %{}, 0\n",
            next,
            next + 1,
            next
        ));
        last = next + 1;
        next += 2;
    }
    text.push_str(&format!("    ret %{last}\n}}\n"));
    std::fs::write(&input, text).expect("write input");
    let run = |args: &[&str], out: &Path| {
        let output = Command::new(trust_cg_bin())
            .arg("--permit-unlicensed")
            .args(["--format=text", "--target", "wasm32"])
            .args(args)
            .arg("-o")
            .arg(out)
            .arg(&input)
            .output()
            .expect("run trust-cg");
        let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
        assert!(output.status.success(), "stderr:\n{stderr}");
        (std::fs::read(out).expect("read output"), stderr)
    };
    for args in [&[][..], &["-c"][..]] {
        let (a, sa) = run(args, &dir.join("a.out"));
        let (b, sb) = run(args, &dir.join("b.out"));
        assert_eq!(a, b, "{args:?}: two runs emitted different bytes");
        assert_eq!(
            parse_evidence(&sa)["module_sha256"],
            parse_evidence(&sb)["module_sha256"]
        );
    }
}

/// `wasm-ld` exports the linked memory as `memory` and, under
/// `--export-dynamic`, every default-visibility definition by name, without
/// checking the two apart: an exported `memory` function would give the
/// module two exports of one name. The link refuses it by name.
#[test]
fn wasm32_link_refuses_a_definition_exported_as_memory() {
    let Some(linker) = wasm_ld() else {
        eprintln!("wasm32_link_refuses_a_definition_exported_as_memory: SKIPPED — no wasm-ld");
        return;
    };
    let dir = scratch_dir("memory_export");
    let (mem, gcd, out) = (
        dir.join("mem.trust_ir"),
        dir.join("gcd.trust_ir"),
        dir.join("app.wasm"),
    );
    std::fs::write(
        &mem,
        "module \"mem\"\ntarget \"wasm32-unknown-unknown\" 4 little\n\n\
         functy.0 = (i32) -> (i32)\n\nfn @memory(functy.0) {\nbb0(%1: i32):\n    ret %1\n}\n",
    )
    .expect("write mem");
    std::fs::write(&gcd, GCD_TEXT).expect("write gcd");
    let link = |extra: &[&str]| {
        let _ = std::fs::remove_file(&out);
        let output = Command::new(trust_cg_bin())
            .arg("--permit-unlicensed")
            .args(["--format=text", "--target", "wasm32", "--wasm-ld"])
            .arg(&linker)
            .args(extra)
            .arg("-o")
            .arg(&out)
            .arg(&mem)
            .arg(&gcd)
            .output()
            .expect("run trust-cg");
        (
            output.status.success(),
            String::from_utf8_lossy(&output.stderr).into_owned(),
        )
    };
    // Options that only size or share the memory keep its `memory` export
    // (`--initial-memory=` used to switch the check off).
    for extra in [
        &[][..],
        &["-Wl,--initial-memory=1310720"],
        &["-Wl,--max-memory=1310720"],
    ] {
        let (ok, stderr) = link(extra);
        assert!(!ok, "{extra:?}: the link must be refused");
        assert!(
            stderr.contains("exported function `memory`"),
            "{extra:?} stderr:\n{stderr}"
        );
        assert!(!out.exists(), "{extra:?}: nothing is published");
    }
    // A renamed memory export frees the name.
    let (ok, stderr) = link(&["-Wl,--export-memory=mem"]);
    assert!(ok, "a renamed memory export links: {stderr}");
    wasmparser::Validator::new()
        .validate_all(&std::fs::read(&out).expect("linked module"))
        .expect("the linked module validates");
    // Any other export collision the link produces is caught in the linked
    // module itself, which is removed.
    let (ok, stderr) = link(&["-Wl,--export=__heap_base,--export-memory=__heap_base"]);
    assert!(!ok, "a duplicate export must be refused");
    assert!(
        stderr.contains("exports `__heap_base` twice"),
        "stderr:\n{stderr}"
    );
    assert!(!out.exists(), "the invalid module is removed");
}

// 12. The codegen-license flags reach both wasm32 lanes.

/// `make_const_module` with exactly one licensing state.
fn write_gated_module(dir: &Path, name: &str, gate: Option<trust_ir::BodyGate>) -> PathBuf {
    let mut module = make_const_module();
    for function in &mut module.functions {
        function.body_gate = gate.clone();
    }
    let path = dir.join(format!("{name}.tmbc"));
    std::fs::write(&path, encode_tmbc(&module).expect("encode tMBC")).expect("write tMBC");
    path
}

/// `trust-cg --target wasm32 [-c] -o <out> [flags] <input>` on the closed
/// module (`compile_only == false`) or the object lane; returns (success,
/// stderr) after checking that an output exists exactly when it succeeded.
fn run_wasm_lane(dir: &Path, input: &Path, compile_only: bool, flags: &[&str]) -> (bool, String) {
    let out = dir.join(format!(
        "{}.{}",
        input.file_stem().unwrap().to_string_lossy(),
        if compile_only { "o" } else { "wasm" }
    ));
    let _ = std::fs::remove_file(&out);
    let mut command = Command::new(trust_cg_bin());
    command.args(["--target", "wasm32"]);
    if compile_only {
        command.arg("-c");
    }
    let output = command
        .arg("-o")
        .arg(&out)
        .args(flags)
        .arg(input)
        .output()
        .expect("run trust-cg");
    let ok = output.status.success();
    assert_eq!(
        out.exists(),
        ok,
        "an output exists exactly when the compile succeeds"
    );
    (ok, String::from_utf8_lossy(&output.stderr).to_string())
}

#[test]
fn codegen_license_flags_reach_both_wasm32_lanes() {
    let dir = scratch_dir("license_flags");
    let gated = |authority: &str| Some(trust_ir::BodyGate::gated(authority.to_string()));
    let vendor = write_gated_module(dir.path(), "vendor", gated("vendor-gate"));
    let unlicensed = write_gated_module(dir.path(), "unlicensed", None);
    let ungated = write_gated_module(dir.path(), "ungated", Some(trust_ir::BodyGate::Ungated));
    let clean = write_gated_module(dir.path(), "clean", gated("clean-kernel-tv"));
    for compile_only in [false, true] {
        let lane = if compile_only { "object" } else { "module" };
        // `--recognize-authority` widens the recognized set on this lane too.
        let (ok, stderr) = run_wasm_lane(dir.path(), &vendor, compile_only, &[]);
        assert!(!ok, "{lane}: an unrecognized authority must fail");
        assert!(
            stderr.contains("does not recognize") && stderr.contains("vendor-gate"),
            "{lane}: stderr:\n{stderr}"
        );
        let (ok, stderr) = run_wasm_lane(
            dir.path(),
            &vendor,
            compile_only,
            &["--recognize-authority", "vendor-gate"],
        );
        assert!(
            ok,
            "{lane}: a recognized authority compiles. stderr:\n{stderr}"
        );
        // A claim-less body is refused by default and by the explicit
        // `--refuse-unlicensed` (roadmap WS7.5, DG-73), and compiles only
        // under the disclosed `--permit-unlicensed`.
        for flags in [&[][..], &["--refuse-unlicensed"][..]] {
            let (ok, stderr) = run_wasm_lane(dir.path(), &unlicensed, compile_only, flags);
            assert!(!ok, "{lane} {flags:?}: a claim-less body must fail");
            assert!(
                stderr.contains("no codegen license"),
                "{lane} {flags:?}: {stderr}"
            );
            assert!(
                !stderr.contains("--permit-unlicensed: '"),
                "{lane} {flags:?}: nothing disclosed: {stderr}"
            );
        }
        let (ok, stderr) = run_wasm_lane(
            dir.path(),
            &unlicensed,
            compile_only,
            &["--permit-unlicensed"],
        );
        assert!(
            ok,
            "{lane}: --permit-unlicensed compiles a claim-less body: {stderr}"
        );
        assert!(
            stderr.contains("--permit-unlicensed: '") && stderr.contains("NO codegen license"),
            "{lane}: the permitted body is disclosed: {stderr}"
        );
        let (ok, stderr) = run_wasm_lane(
            dir.path(),
            &vendor,
            compile_only,
            &[
                "--refuse-unlicensed",
                "--recognize-authority",
                "vendor-gate",
            ],
        );
        assert!(ok, "{lane}: a licensed body compiles: {stderr}");
        // No flag admits an `ungated` body, or an evidence-bound license
        // worn without its certificate (trust-ir's codegen admission).
        for flags in [&[][..], &["--recognize-authority", "ungated"][..]] {
            let (ok, stderr) = run_wasm_lane(dir.path(), &ungated, compile_only, flags);
            assert!(!ok, "{lane} {flags:?}: an ungated body must fail");
            assert!(stderr.contains("affirmatively ungated"), "{lane}: {stderr}");
        }
        for flags in [&[][..], &["--recognize-authority", "clean-kernel-tv"][..]] {
            let (ok, stderr) = run_wasm_lane(dir.path(), &clean, compile_only, flags);
            assert!(
                !ok,
                "{lane} {flags:?}: an evidence-bound license without its evidence must fail"
            );
            assert!(
                stderr.contains("without the evidence it names")
                    && stderr.contains("clean-kernel-tv"),
                "{lane} {flags:?}: stderr:\n{stderr}"
            );
        }
    }
}

#[path = "common/scratch.rs"]
mod scratch;

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes (or is refused) because the license silently refused it.
fn permit_unlicensed() -> trust_cg_codegen::CodegenLicensePolicy {
    trust_cg_codegen::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit)
}
