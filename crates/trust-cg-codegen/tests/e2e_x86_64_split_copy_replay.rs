// trust-cg-codegen/tests/e2e_x86_64_split_copy_replay.rs - x86-64 regalloc
// replay of split copies, end to end
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// The fixtures are two unedited rustc-bridge trust-ir dumps of
// `fixtures/x86_split_copy_replay/split_copy_kernels.rs`, compiled for
// x86_64-apple-darwin at -Copt-level=3, with the bridge's sidecar records.
// `README.md` beside them records the command and its provenance;
// `fixtures_match_their_recorded_provenance` binds the README's sha256 rows to
// the bytes this file includes, and the sidecars to the compile configuration
// used here.
//
// At O3 this backend's x86 frame-slot forwarding turns each kernel's array
// reads into register copies, and greedy splitting then gives some split
// child no reader except an original ISel copy. Every such split copy must
// reach the emitted stream: the rule is stated on
// `replay_x86_regalloc_stream_mutations` in `src/x86_64/pipeline.rs`.
//
// Legs:
// * compile (always runs): both modules compile at O3 for x86-64 in the host's
//   object format.
// * run (gated by `x86_64_link_run_or_skip`: native x86-64, opted-in Rosetta 2
//   via TRUST_CG_RUN_ROSETTA_LINKRUN=1, or a cross driver plus binfmt): each
//   object is linked with a C driver and run, and its output must equal the
//   same kernel written in Rust below and compiled by the host compiler.

use std::fs;
use std::path::{Path, PathBuf};

use sha2::{Digest, Sha256};
use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::Target;

#[path = "common/rosetta.rs"]
mod rosetta;
use rosetta::{
    codegen_link_timeout, codegen_run_timeout, command_output_with_timeout,
    run_executable_with_timeout, x86_64_cc, x86_64_link_run_or_skip,
};

const FIXTURE_DIR: &str = "tests/fixtures/x86_split_copy_replay";
const README: &str = include_str!("fixtures/x86_split_copy_replay/README.md");
const SOURCE: &[u8] = include_bytes!("fixtures/x86_split_copy_replay/split_copy_kernels.rs");

struct Kernel {
    /// The `#[no_mangle]` symbol the C driver calls.
    symbol: &'static str,
    /// The unedited bridge dump's file name under `FIXTURE_DIR`.
    file: &'static str,
    bytes: &'static [u8],
    /// The bridge's sidecar record of the dump: its file name and text.
    sidecar_file: &'static str,
    sidecar: &'static str,
    /// The host compiler's oracle: the same kernel in Rust.
    oracle: fn(&[u64; 8]) -> u64,
    /// The oracle's value on `driver_input()`, as recorded in the README.
    expected: u64,
}

const KERNELS: [Kernel; 2] = [
    Kernel {
        symbol: "trustcg_split_copy_k_xsh_8",
        file: "k.trustcg_split_copy_k_xsh_8.rcgu.trust_irbin",
        bytes: include_bytes!(
            "fixtures/x86_split_copy_replay/k.trustcg_split_copy_k_xsh_8.rcgu.trust_irbin"
        ),
        sidecar_file: "k.trustcg_split_copy_k_xsh_8.rcgu.json",
        sidecar: include_str!(
            "fixtures/x86_split_copy_replay/k.trustcg_split_copy_k_xsh_8.rcgu.json"
        ),
        oracle: k_xsh_8,
        expected: 8_275_365_051_531_202_673,
    },
    Kernel {
        symbol: "trustcg_split_copy_k_mul_8",
        file: "k.trustcg_split_copy_k_mul_8.rcgu.trust_irbin",
        bytes: include_bytes!(
            "fixtures/x86_split_copy_replay/k.trustcg_split_copy_k_mul_8.rcgu.trust_irbin"
        ),
        sidecar_file: "k.trustcg_split_copy_k_mul_8.rcgu.json",
        sidecar: include_str!(
            "fixtures/x86_split_copy_replay/k.trustcg_split_copy_k_mul_8.rcgu.json"
        ),
        oracle: k_mul_8,
        expected: 8_577_365_346_607_315_621,
    },
];

/// `trustcg_split_copy_k_xsh_8` of `split_copy_kernels.rs`, without the
/// optimization barriers.
fn k_xsh_8(src: &[u64; 8]) -> u64 {
    let mut acc: u64 = 0;
    let mut t: u64 = 0;
    for (i, &x) in src.iter().enumerate() {
        acc = acc.wrapping_add(x ^ (x >> 29) ^ (x << 7));
        t = t.wrapping_add(i as u64 * 3 + 1);
    }
    acc ^ t.wrapping_mul(5)
}

/// `trustcg_split_copy_k_mul_8` of `split_copy_kernels.rs`, without the
/// optimization barriers.
fn k_mul_8(src: &[u64; 8]) -> u64 {
    let mut acc: u64 = 0;
    let mut t: u64 = 0;
    for (i, &x) in src.iter().enumerate() {
        acc = acc.wrapping_add((x ^ (x >> 29)).wrapping_mul(0x2545_F491_4F6C_DD1D));
        t = t.wrapping_add(i as u64 * 3 + 1);
    }
    acc ^ t.wrapping_mul(5)
}

/// The C driver's input: `s[i] = i * 0x9E3779B97F4A7C15` (wrapping).
fn driver_input() -> [u64; 8] {
    std::array::from_fn(|i| (i as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15))
}

/// The configuration the bridge compiled each dump with, as its sidecar
/// records (`fixtures_match_their_recorded_provenance` checks the sidecars).
fn bridge_config() -> CompilerConfig {
    CompilerConfig {
        target: Target::X86_64,
        opt_level: OptLevel::O3,
        emit_proofs: false,
        panic_unwind: false,
        parallel: false,
        ..CompilerConfig::default()
    }
}

/// The kernel's x86-64 O3 object, or the compiler's refusal.
fn try_compile_o3(kernel: &Kernel) -> Result<Vec<u8>, String> {
    // The bridge hands its module over in process, with no wire provenance, so
    // the fixture is decoded the same way.
    let module = trust_ir::binary::deserialize_module(kernel.bytes)
        .unwrap_or_else(|err| panic!("{}: the fixture must decode: {err:?}", kernel.file));
    let compiled = Compiler::new(bridge_config())
        .with_codegen_license(permit_unlicensed())
        .compile(&module)
        .map_err(|err| err.to_string())?;
    assert!(
        !compiled.object_code.is_empty(),
        "{}: empty object",
        kernel.symbol
    );
    Ok(compiled.object_code)
}

fn scratch_dir(test: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!(
        "trust_cg_e2e_x86_64_split_copy_replay_{test}_{}",
        std::process::id()
    ));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).expect("create the scratch directory");
    dir
}

fn link_and_run(dir: &Path, kernel: &Kernel, object: &[u8]) -> String {
    let object_path = dir.join(format!("{}.o", kernel.symbol));
    fs::write(&object_path, object).expect("write the object");
    let driver_path = dir.join(format!("{}_driver.c", kernel.symbol));
    fs::write(
        &driver_path,
        format!(
            "#include <stdint.h>\n\
             #include <stdio.h>\n\
             extern uint64_t {symbol}(const uint64_t *src);\n\
             int main(void) {{\n\
             \x20   uint64_t s[8];\n\
             \x20   for (uint64_t i = 0; i < 8; i++) s[i] = i * 0x9E3779B97F4A7C15ull;\n\
             \x20   printf(\"%llu\\n\", (unsigned long long){symbol}(s));\n\
             \x20   return 0;\n\
             }}\n",
            symbol = kernel.symbol
        ),
    )
    .expect("write the C driver");
    let binary = dir.join(kernel.symbol);
    let mut link = x86_64_cc();
    link.arg("-o")
        .arg(&binary)
        .arg(&driver_path)
        .arg(&object_path);
    let linked = command_output_with_timeout(&mut link, codegen_link_timeout())
        .expect("run the x86-64 C driver");
    assert!(
        !linked.timed_out && linked.output.status.success(),
        "{}: link failed (timed out: {}):\n{}",
        kernel.symbol,
        linked.timed_out,
        String::from_utf8_lossy(&linked.output.stderr)
    );
    let ran = run_executable_with_timeout(&binary, rosetta::exec_timeout(codegen_run_timeout()))
        .expect("run the linked x86-64 binary");
    assert!(
        !ran.timed_out && ran.output.status.success(),
        "{}: run failed (timed out: {}, status {:?}):\n{}",
        kernel.symbol,
        ran.timed_out,
        ran.output.status,
        String::from_utf8_lossy(&ran.output.stderr)
    );
    String::from_utf8_lossy(&ran.output.stdout)
        .trim()
        .to_string()
}

fn sha256_hex(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

#[test]
fn fixtures_match_their_recorded_provenance() {
    let mut files: Vec<(&str, &[u8])> = vec![("split_copy_kernels.rs", SOURCE)];
    for kernel in &KERNELS {
        files.push((kernel.file, kernel.bytes));
        files.push((kernel.sidecar_file, kernel.sidecar.as_bytes()));
    }
    for (file, bytes) in files {
        let row = format!("| `{file}` | `{}` |", sha256_hex(bytes));
        assert!(
            README.lines().any(|line| line.trim() == row),
            "{FIXTURE_DIR}/README.md must record `{row}`: the bytes changed or the README is stale"
        );
    }
    let config = bridge_config();
    for kernel in &KERNELS {
        let sidecar: serde_json::Value = serde_json::from_str(kernel.sidecar)
            .unwrap_or_else(|err| panic!("{}: sidecar must be JSON: {err}", kernel.sidecar_file));
        let recorded = |key: &str| sidecar[key].clone();
        assert_eq!(recorded("cgu"), serde_json::json!(kernel.symbol));
        assert_eq!(recorded("target"), serde_json::json!("X86_64"));
        assert_eq!(recorded("opt_level"), serde_json::json!("O3"));
        assert!(config.target == Target::X86_64 && config.opt_level == OptLevel::O3);
        for (key, used) in [
            ("emit_proofs", config.emit_proofs),
            ("panic_unwind", config.panic_unwind),
            ("parallel", config.parallel),
        ] {
            assert_eq!(
                recorded(key),
                serde_json::json!(used),
                "{}: the bridge compiled with `{key}` = {}, this test with {used}",
                kernel.sidecar_file,
                recorded(key)
            );
        }
        let module = trust_ir::binary::deserialize_module(kernel.bytes)
            .unwrap_or_else(|err| panic!("{}: the fixture must decode: {err:?}", kernel.file));
        let errors = trust_ir_build::validate_module(&module);
        assert!(
            errors.is_empty(),
            "{}: the bridge dump must be a well-formed module: {errors:?}",
            kernel.file
        );
        assert_eq!(
            (kernel.oracle)(&driver_input()),
            kernel.expected,
            "{}: the host oracle disagrees with the value the README records",
            kernel.symbol
        );
    }
}

#[test]
fn split_copy_kernels_compile_at_o3() {
    let refused: Vec<String> = KERNELS
        .iter()
        .filter_map(|kernel| {
            try_compile_o3(kernel)
                .err()
                .map(|err| format!("{}: {err}", kernel.symbol))
        })
        .collect();
    assert!(
        refused.is_empty(),
        "every kernel must compile at x86-64 O3: {refused:#?}"
    );
}

#[test]
fn split_copy_kernels_link_run_and_match_the_host_oracle_at_o3() {
    // Without an executor this leg skips by name; `split_copy_kernels_compile_at_o3`
    // still holds every compilation.
    if !x86_64_link_run_or_skip(
        "split_copy_kernels_link_run_and_match_the_host_oracle_at_o3",
        "x86-64 link/run",
    ) {
        return;
    }
    let dir = scratch_dir("link_run");
    // Every kernel is judged, so one refusal does not hide another's value.
    let mut failures = Vec::new();
    for kernel in &KERNELS {
        let expected = (kernel.oracle)(&driver_input()).to_string();
        match try_compile_o3(kernel) {
            Err(err) => failures.push(format!("{}: refused: {err}", kernel.symbol)),
            Ok(object) => {
                let printed = link_and_run(&dir, kernel, &object);
                if printed != expected {
                    failures.push(format!(
                        "{}: the x86-64 O3 object printed {printed}, the host oracle {expected}",
                        kernel.symbol
                    ));
                }
            }
        }
    }
    let _ = fs::remove_dir_all(&dir);
    assert!(failures.is_empty(), "{failures:#?}");
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes, and no refusal is the license's, by accident.
fn permit_unlicensed() -> trust_cg_codegen::CodegenLicensePolicy {
    trust_cg_codegen::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit)
}
