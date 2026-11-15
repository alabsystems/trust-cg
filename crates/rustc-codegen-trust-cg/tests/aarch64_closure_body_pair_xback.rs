// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// An admitted closure Pair must execute, including at register exhaustion,
// across all four LLVM/TrustCG rlib x bin combinations. Same-backend agreement
// alone cannot detect a mutually incorrect calling convention. Certificates
// remain off: this is native ABI execution evidence, not proof credit.
#![cfg(all(target_os = "macos", target_arch = "aarch64"))]

#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/positive_evidence.rs"]
mod positive_evidence;
#[path = "support/darwin_native_prerequisites.rs"]
mod prerequisites;
#[path = "support/toolchain.rs"]
mod toolchain_support;

#[path = "support/aarch64_closure_body_pair_xback.rs"]
mod aarch64_closure_body_pair_xback_support;
use aarch64_closure_body_pair_xback_support::{CALLEE, CALLER, EXPECTED};

use std::path::{Path, PathBuf};
use std::process::Command;

#[derive(Clone, Copy)]
enum Backend {
    Llvm,
    TrustCg,
}

impl Backend {
    fn tag(self) -> &'static str {
        match self {
            Self::Llvm => "llvm",
            Self::TrustCg => "tcg",
        }
    }
}

fn compile(
    dir: &Path,
    backend: Backend,
    opt: &str,
    library: Option<&Path>,
    dylib: &Path,
) -> PathBuf {
    let name = match library {
        None => "pair_lib",
        Some(_) => "pair_bin",
    };
    let cell = dir.join(format!(
        "{name}-{}-O{opt}-{}",
        backend.tag(),
        library
            .and_then(|p| p.parent())
            .and_then(|p| p.file_name())
            .and_then(|p| p.to_str())
            .unwrap_or("root")
    ));
    std::fs::create_dir_all(&cell).expect("create exact ABI cell");
    let source = cell.join("main.rs");
    std::fs::write(&source, if library.is_some() { CALLER } else { CALLEE }).unwrap();
    let output = cell.join(if library.is_some() {
        "prog"
    } else {
        "libpair_lib.rlib"
    });
    let mut command = toolchain_support::rustc_command_with_edition("2021");
    command
        .arg(&source)
        .arg("--crate-name")
        .arg(name)
        .args([
            "--target",
            "aarch64-apple-darwin",
            "-Cpanic=abort",
            "-Ccodegen-units=1",
        ])
        .arg(format!("-Copt-level={opt}"))
        .arg("-o")
        .arg(&output);
    if let Some(library) = library {
        command
            .arg("--extern")
            .arg(format!("pair_lib={}", library.display()));
    } else {
        command.args(["--crate-type", "rlib"]);
    }
    if matches!(backend, Backend::TrustCg) {
        let mut flag = std::ffi::OsString::from("-Zcodegen-backend=");
        flag.push(dylib);
        command
            .arg(flag)
            .arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]));
    }
    let built = command.output().expect("actual Trust compiler ABI cell");
    std::fs::write(cell.join("compile.stdout"), &built.stdout).unwrap();
    std::fs::write(cell.join("compile.stderr"), &built.stderr).unwrap();
    assert!(
        built.status.success(),
        "mandatory closure Pair {:?} O{opt} failed; artifacts={}\n{}",
        backend.tag(),
        cell.display(),
        String::from_utf8_lossy(&built.stderr)
    );
    assert!(output.is_file(), "actual output was not produced");
    output
}

fn execute(program: &Path) -> Vec<u64> {
    let output = Command::new(program)
        .output()
        .expect("actual mixed-backend execution");
    assert!(
        output.status.success(),
        "program={}\n{}",
        program.display(),
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(
        output.stdout.len(),
        64,
        "all eight scalar observations must be written"
    );
    output
        .stdout
        .chunks_exact(8)
        .map(|bytes| u64::from_le_bytes(bytes.try_into().unwrap()))
        .collect()
}

#[test]
fn closure_body_pairs_match_llvm_across_native_backend_boundaries() {
    prerequisites::require("aarch64_closure_body_pair_xback", &[]);
    let dylib = backend_artifact_support::current_test_backend();
    let dir = std::env::temp_dir().join(format!(
        "tcg_closure_body_pair_xback_{}_{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ));
    std::fs::create_dir(&dir).expect("fresh ABI artifact owner");
    let mut cells = 0;
    for opt in ["0", "1", "2", "3"] {
        let llvm = compile(&dir, Backend::Llvm, opt, None, &dylib);
        let tcg = compile(&dir, Backend::TrustCg, opt, None, &dylib);
        let oracle = execute(&compile(&dir, Backend::Llvm, opt, Some(&llvm), &dylib));
        assert_eq!(oracle, EXPECTED, "independent source arithmetic at O{opt}");
        for (caller, library) in [
            (Backend::TrustCg, &llvm),
            (Backend::Llvm, &tcg),
            (Backend::TrustCg, &tcg),
        ] {
            let observed = execute(&compile(&dir, caller, opt, Some(library), &dylib));
            assert_eq!(
                observed,
                oracle,
                "O{opt} caller={} library={} artifacts={}",
                caller.tag(),
                library.display(),
                dir.display()
            );
            cells += 1;
        }
    }
    assert_eq!(cells, 12);
    eprintln!(
        "CLOSURE_BODY_PAIR_XBACK rows=7 cells=16 opts=0,1,2,3 certs=off artifacts={}",
        dir.display()
    );
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}
