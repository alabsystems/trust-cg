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
//   6. dropped requests (an explicit `-O`, an explicit `--fsym-solver` with
//      the preflight off) are refused by name;
//   7. PUBLICATION ORDER: a failed compile publishes NOTHING, and a
//      successful one publishes every requested artifact;
//   8. aliased output paths (an artifact over its own input, two artifacts
//      over one file) are refused by name.
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
use trust_cg_codegen::pipeline::{encode_tmbc, encode_trust_ir_text};
use trust_cg_codegen::wasm;
use trust_ir::{ICmpOp, Module as TrustIrModule, Ty};
use trust_ir_build::ModuleBuilder;

const WASM_MAGIC: &[u8] = &[0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00];

/// The evidence line prefix the CLI prints for every wasm compile.
const EVIDENCE_PREFIX: &str = "trust-cg: wasm-evidence: ";

fn trust_cg_bin() -> PathBuf {
    PathBuf::from(env!("CARGO_BIN_EXE_trust-cg"))
}

/// Create a fresh, empty scratch directory under the OS temp dir.
fn scratch_dir(test_name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!(
        "trust_cg_cli_wasm_{}_{}",
        test_name,
        std::process::id()
    ));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create scratch dir");
    dir
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
    let mut module = mb.build();
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
    let mut module = mb.build();
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
// 6. Dropped requests are refused by name.
// ---------------------------------------------------------------------------

/// An EXPLICIT `-O` on the wasm lane is a dropped request (the route never
/// reads opt_level), so it is refused by name — and the refusal fires before
/// any input is read or artifact written, even with `--emit-json` present.
#[test]
fn explicit_opt_level_is_refused_and_emits_nothing() {
    let dir = scratch_dir("explicit_opt_level");
    let input = dir.join("m.trust_ir");
    std::fs::write(
        &input,
        "module \"probe\"\ntarget \"wasm32-unknown-unknown\" 4 little\n",
    )
    .expect("write input");
    let json = dir.join("side-effect.json");

    let out = Command::new(trust_cg_bin())
        .args([
            "--format=text",
            "--target",
            "wasm32-unknown-unknown",
            "-O3",
            "--emit-json",
        ])
        .arg(&json)
        .arg(&input)
        .output()
        .expect("run trust-cg");

    assert!(!out.status.success(), "explicit -O must be refused");
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        stderr.contains("-O/--opt-level"),
        "refusal must name the flag, got: {stderr}"
    );
    assert!(
        !json.exists(),
        "a refused invocation must write no artifacts"
    );
}

/// The DEFAULT opt level is not a dropped request: no refusal is emitted, the
/// run SUCCEEDS, and the module it publishes is a real, validated wasm module
/// whose evidence matches the bytes on disk. (Asserting only the absence of
/// the refusal string would pass on a compile that failed outright.)
#[test]
fn default_opt_level_is_not_refused() {
    let dir = scratch_dir("default_opt_level");
    let input = dir.join("m.trust_ir");
    std::fs::write(&input, encode_trust_ir_text(&make_const_module())).expect("write input");
    let out = dir.join("m.wasm");

    let run = Command::new(trust_cg_bin())
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
/// the default `--fsym=off` is a dropped request — the same class as the
/// explicit `-O` above — and is refused by name. (The rule is CLI-wide; it is
/// exercised here on the wasm lane, where the sibling dropped-request refusals
/// live.)
#[test]
fn explicit_fsym_solver_without_the_preflight_is_refused() {
    let dir = scratch_dir("fsym_solver_dropped");
    let input = dir.join("m.trust_ir");
    std::fs::write(&input, encode_trust_ir_text(&make_const_module())).expect("write input");
    let out = dir.join("m.wasm");

    let refused = Command::new(trust_cg_bin())
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
