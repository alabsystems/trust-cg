// trust-cg-cli/tests/emit_proofs_adapter_disclosure.rs — WS7.2 disclosure
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! WS7.2 (F-111): `--emit-proofs` names the adapter blind spot.
//!
//! The proof program's c13 gate module `shared_nomul.trust_ir`
//! (`two_inserts_sub(a, b) = p.x - q.x`, two insert chains off one base) went
//! through the full `--emit-proofs` gate while the adapter aliased an
//! `InsertField` result with its base: the object computed
//! `two_inserts_sub(9, 2) = 0` (want 7), and the CLI printed three
//! `[VERIFIED]` rules and wrote certified sidecars for it. The rules were
//! honest about LIR -> machine; the trust-ir -> LIR adapter was simply
//! outside them, and nothing said so.
//!
//! Every certificate and sidecar now carries `"covered_span":
//! "lir->machine"`, and the listing opens each function with `trust-ir->lir:
//! NOT COVERED (adapter outside the proven boundary)`. No line is a
//! function-level `VERIFIED`. No grade changes; only the labels are accurate.
//! The real binary's listing is read back from a compile that promotes (a
//! structural leaf). `shared_nomul.trust_ir` itself no longer promotes: with
//! the value-semantic adapter its correct object carries sampled evidence and
//! is refused by name, which this file pins as a ratchet. The in-process
//! re-measurement that the MISCOMPILED object still earns verified LIR ->
//! machine certificates lives with the differential that does check the
//! adapter step (`trust-cg-codegen/tests/trust_ir_interp_differential.rs`,
//! `--features mutation-knobs`).
//!
//! The release CLI carries no mutation knob: no manifest in its build graph
//! enables `trust-cg-lower/mutation-knobs` by default, and the binary reports
//! the knobs it was built with (`--metrics`), which must match the library
//! build it links.

use std::path::{Path, PathBuf};
use std::process::Command;

#[path = "common/scratch.rs"]
mod scratch;

const DISCLOSURE: &str = "trust-ir->lir: NOT COVERED (adapter outside the proven boundary)";

fn trust_cg_bin() -> PathBuf {
    PathBuf::from(env!("CARGO_BIN_EXE_trust-cg"))
}

/// The c13 gate module, vendored with the WS7.2 differential corpus.
fn shared_nomul() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../trust-cg-codegen/tests/fixtures/trust_ir_exec/c13_shared_nomul.trust_ir")
}

/// `shared_nomul` as a binary tMBC module in `dir`. WS7.3 refuses `.trust_ir`
/// text under `--emit-proofs` (TEXT_INPUT_NOT_TOTAL), so the proof-required
/// compile reads the binary module the text states.
fn shared_nomul_tmbc(dir: &Path) -> PathBuf {
    let path = shared_nomul();
    let text = std::fs::read_to_string(&path).expect("read c13_shared_nomul.trust_ir");
    let module = trust_cg_codegen::pipeline::parse_trust_ir_text(&text)
        .unwrap_or_else(|e| panic!("parse {}: {e:?}", path.display()));
    let tmbc = dir.join("shared_nomul.tmbc");
    std::fs::write(
        &tmbc,
        trust_cg_codegen::pipeline::encode_tmbc(&module).expect("encode tMBC"),
    )
    .expect("write tMBC");
    tmbc
}

fn files_with_suffix(root: &Path, suffix: &str) -> Vec<PathBuf> {
    let mut out = Vec::new();
    let mut stack = vec![root.to_path_buf()];
    while let Some(dir) = stack.pop() {
        let Ok(entries) = std::fs::read_dir(&dir) else {
            continue;
        };
        for entry in entries {
            let path = entry.expect("dir entry").path();
            if path.is_dir() {
                stack.push(path);
            } else if path.to_string_lossy().ends_with(suffix) {
                out.push(path);
            }
        }
    }
    out.sort();
    out
}

fn json(path: &Path) -> serde_json::Value {
    serde_json::from_slice(&std::fs::read(path).expect("read sidecar")).expect("sidecar JSON")
}

/// Assert the WS7.2 disclosure on a successful `--emit-proofs` run: the
/// listing opens `function`'s group with the NOT COVERED line, every
/// `VERIFIED` is a LIR -> machine rule row, no line naming the function says
/// `VERIFIED`, and every written certificate and sidecar says its span.
fn assert_disclosed(output: &std::process::Output, proofs_dir: &Path, function: &str) {
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "the --emit-proofs compile must promote: {stderr}"
    );
    let listing: Vec<&str> = stderr
        .lines()
        .skip_while(|line| *line != "--- proof certificates ---")
        .take_while(|line| *line != "--- end proofs ---")
        .collect();
    assert!(
        !listing.is_empty(),
        "--emit-proofs printed no certificate listing: {stderr}"
    );
    assert!(
        listing.contains(&format!("  [{function}] {DISCLOSURE}").as_str()),
        "the listing must name the adapter blind spot for {function}: {stderr}"
    );
    let mut rules = 0;
    for line in stderr.lines() {
        if line.contains("VERIFIED") {
            assert!(
                line.starts_with("    ") && line.ends_with("(lir->machine)"),
                "a VERIFIED that is not a LIR -> machine rule row: {line:?}\n{stderr}"
            );
            rules += 1;
        }
        if line.contains(function) {
            assert!(
                !line.contains("VERIFIED"),
                "a function-level VERIFIED: {line:?}\n{stderr}"
            );
        }
    }
    assert!(rules > 0, "no rule rows were listed: {stderr}");

    let certs = files_with_suffix(proofs_dir, ".cert");
    assert!(!certs.is_empty(), "no .cert was written: {stderr}");
    for path in certs {
        assert_eq!(
            json(&path)["covered_span"],
            "lir->machine",
            "{}",
            path.display()
        );
    }
    for suffix in [".lowering.json", ".trust-proof-cert.json"] {
        for path in files_with_suffix(proofs_dir, suffix) {
            assert_eq!(
                json(&path)["covered_span"],
                "lir->machine",
                "{}",
                path.display()
            );
        }
    }
}

/// A leaf that only returns: its proof-required Mach-O compile promotes on
/// every host (the same structural fixture `emit_proofs_flag.rs` uses), so
/// the real binary's listing and audit certificates can be read back.
fn structural_module() -> trust_ir::Module {
    let mut mb = trust_ir_build::ModuleBuilder::new("ws7_2_disclosure");
    let ty = mb.add_func_type(vec![], vec![]);
    let mut fb = mb.function("_structural", ty);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.ret(vec![]);
    fb.build();
    mb.build().expect("the structural fixture builds")
}

/// POSITIVE: a promoted `--emit-proofs` compile lists `trust-ir->lir: NOT
/// COVERED` for its function, prints no function-level `VERIFIED`, and every
/// `.cert` it writes says `"covered_span": "lir->machine"`.
#[test]
fn emit_proofs_prints_not_covered_and_no_function_level_verified() {
    let dir = scratch::create("trust_cg_cli_ws7_2_disclosure_");
    let tmbc = dir.join("structural.tmbc");
    std::fs::write(
        &tmbc,
        trust_cg_codegen::pipeline::encode_tmbc(&structural_module()).expect("encode tMBC"),
    )
    .expect("write tMBC");
    let proofs_dir = dir.join("proofs");
    // The structural leaf carries no body gate; WS7.5 refuses unlicensed
    // bodies by default, so this names the legacy-corpus exception exactly as
    // `emit_proofs_flag.rs` does for the same fixture.
    let output = Command::new(trust_cg_bin())
        .args([
            "--permit-unlicensed",
            "-c",
            "--target=aarch64-apple-darwin",
            "-o",
        ])
        .arg(dir.join("structural.o"))
        .arg(format!("--emit-proofs={}", proofs_dir.display()))
        .arg(&tmbc)
        .output()
        .expect("run trust-cg");
    assert_disclosed(&output, &proofs_dir, "_structural");
}

/// The c13 gate module `shared_nomul.trust_ir` itself. With the
/// value-semantic adapter its CORRECT object needs `AddRI` / `SubRI` /
/// `SubRR`, whose evidence is sampled, so the proof-required compile is
/// refused by name and publishes nothing: the `[VERIFIED]` listing c13
/// measured for the miscompiled object (`mov x0, #0`) is gone. Ratchet: this
/// asserts the current exact refusal; when those opcodes earn complete
/// evidence the module promotes and this test must move to
/// [`assert_disclosed`] (`two_inserts_sub`).
#[test]
fn emit_proofs_on_shared_nomul_is_refused_by_name_and_lists_nothing_verified() {
    let dir = scratch::create("trust_cg_cli_ws7_2_shared_nomul_");
    let out_path = dir.join("shared_nomul.o");
    let proofs_dir = dir.join("proofs");
    let tmbc = shared_nomul_tmbc(&dir);
    let output = Command::new(trust_cg_bin())
        .args([
            "--permit-unlicensed",
            "-c",
            "--target=aarch64-apple-darwin",
            "-o",
        ])
        .arg(&out_path)
        .arg(format!("--emit-proofs={}", proofs_dir.display()))
        .arg(&tmbc)
        .output()
        .expect("run trust-cg");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(!output.status.success(), "{stderr}");
    assert!(
        stderr.contains("proof promotion rejected for target Aarch64")
            && stderr.contains("in two_inserts_sub")
            && stderr.contains("statistical sampling is not proof credit"),
        "the refusal must name the uncredited evidence of two_inserts_sub: {stderr}"
    );
    assert!(
        !stderr.contains("VERIFIED"),
        "a refused compile lists nothing as VERIFIED: {stderr}"
    );
    assert!(!out_path.exists(), "a refused compile publishes no object");
    assert!(
        !proofs_dir.exists(),
        "a refused compile publishes no proofs"
    );
}

/// The shipped binary reports exactly the knobs its library build carries,
/// and in this target's default build that is none.
#[test]
fn release_cli_reports_the_mutation_knobs_it_carries() {
    let dir = scratch::create("trust_cg_cli_ws7_2_knobs_");
    let out_path = dir.join("shared_nomul.o");
    let output = Command::new(trust_cg_bin())
        .args([
            "--format=text",
            "--permit-unlicensed",
            "-c",
            "--target=aarch64-apple-darwin",
            "--metrics",
            "-o",
        ])
        .arg(&out_path)
        .arg(shared_nomul())
        .output()
        .expect("run trust-cg");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(output.status.success(), "{stderr}");
    let reported = format!("\"mutation_knobs\": {}", trust_cg_codegen::MUTATION_KNOBS);
    assert!(
        stderr.contains(&reported),
        "--metrics must report {reported}: {stderr}"
    );
}

/// Knob absence, statically, over EVERY manifest of the workspace (any
/// crate in the CLI's graph could otherwise forward the feature): only
/// `trust-cg-codegen` and `trust-cg-lower` may name the test-only
/// `mutation-knobs` feature, each only as its own non-default feature
/// (`trust-cg-codegen` FORWARDING it to `trust-cg-lower`), and no default
/// feature set enables it. The runtime twin above only proves the binary
/// matches its library build; this is the absence assertion.
#[test]
fn no_shipped_manifest_enables_the_mutation_knobs() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let mut manifests = files_with_suffix(&root.join("crates"), "/Cargo.toml");
    manifests.push(root.join("Cargo.toml"));
    assert!(
        manifests.len() > 4,
        "the manifest scan found the workspace: {manifests:?}"
    );
    let mut owners = Vec::new();
    for manifest in &manifests {
        let text = std::fs::read_to_string(manifest)
            .unwrap_or_else(|e| panic!("{}: {e}", manifest.display()));
        let package = manifest
            .parent()
            .and_then(Path::file_name)
            .map(|n| n.to_string_lossy().into_owned())
            .unwrap_or_default();
        let allowed: &[&str] = match package.as_str() {
            "trust-cg-codegen" => &["mutation-knobs = [\"trust-cg-lower/mutation-knobs\"]"],
            "trust-cg-lower" => &["mutation-knobs = []"],
            _ => &[],
        };
        for line in text.lines().map(str::trim) {
            if line.starts_with('#') || !line.contains("mutation-knobs") {
                continue;
            }
            assert!(
                allowed.contains(&line),
                "{}: unexpected mention of the mutation knobs: {line:?}",
                manifest.display()
            );
            owners.push(package.clone());
        }
        let default = text
            .lines()
            .find(|line| line.trim_start().starts_with("default ="))
            .unwrap_or("");
        assert!(
            !default.contains("mutation-knobs"),
            "{}: the default features enable the mutation knobs: {default}",
            manifest.display()
        );
    }
    owners.sort();
    assert_eq!(
        owners,
        ["trust-cg-codegen", "trust-cg-lower"],
        "the knob feature is declared exactly where the scan expects it"
    );
}
