//! Read-dependent control flow preserves scalar values at every loop back-edge.
//! Diagnostic codegen only; proof-required admission remains a separate gate.
use super::{Artifacts, TARGET, backend, checked, run_bounded, rustc_command, sha256};
use std::path::{Path, PathBuf};
use std::process::Command;

fn artifacts() -> Artifacts {
    let temp = Command::new("mktemp")
        .args(["-d", "-t", "trust-cg-maximal-suffix.XXXXXX"])
        .output()
        .expect("mktemp maximal_suffix artifacts");
    assert!(temp.status.success());
    Artifacts(PathBuf::from(
        String::from_utf8(temp.stdout).unwrap().trim(),
    ))
}

/// The SSA-071 route traces (`refine-trace`) a case requires of its CG O0
/// compile, per function. A function the case does not list with the cell
/// retry may not reach it.
const VC_PROVEN: &str = "back-edge threading PROVEN";
const CELL_RETRY: &str = "SSA-071 cell retry admitted";

fn native_case(
    root: &Path,
    backend: &Path,
    digest: &str,
    rust: &str,
    driver: &str,
    expected: &str,
    routes: &[(&str, &str)],
) {
    std::fs::create_dir(root).unwrap();
    std::fs::write(root.join("corpus.rs"), rust).unwrap();
    std::fs::write(root.join("driver.rs"), driver).unwrap();
    for opt in 0..=3 {
        for lane in ["llvm", "cg"] {
            let stem = format!("{lane}-O{opt}");
            let dir = root.join(&stem);
            std::fs::create_dir(&dir).unwrap();
            let mut command = rustc_command();
            command.args([
                "--crate-type=lib",
                "--emit=obj",
                "-Cpanic=abort",
                "-Ccodegen-units=1",
                "--target",
                TARGET,
            ]);
            command.arg(format!("-Copt-level={opt}"));
            if lane == "cg" {
                command
                    .arg(format!("-Zcodegen-backend={}", backend.display()))
                    .arg("-Ztrust-ir-cg-args=diag-json no-proof-certs refine-trace");
            }
            command
                .arg(root.join("corpus.rs"))
                .arg("--out-dir")
                .arg(&dir);
            let compile = checked(&mut command, 180, &dir.join("compile.log"));
            if lane == "cg" && opt == 0 {
                let log = String::from_utf8_lossy(&compile.stderr);
                for (function, route) in routes {
                    assert!(
                        log.lines().any(|line| line
                            .starts_with(&format!("TCG_REFINE_TRACE {function}: "))
                            && line.contains(route)),
                        "missing {route:?} for {function}: {log}"
                    );
                }
                // A loop the VC stops proving must fail here, not move to the
                // storage fallback unnoticed.
                for line in log.lines().filter(|line| line.contains(CELL_RETRY)) {
                    assert!(
                        routes.iter().any(|(function, listed)| *listed == CELL_RETRY
                            && line.starts_with(&format!("TCG_REFINE_TRACE {function}: "))),
                        "unlisted SSA-071 cell retry {line:?}: {log}"
                    );
                }
            }
            let mut objects: Vec<_> = std::fs::read_dir(&dir)
                .unwrap()
                .map(|entry| entry.unwrap().path())
                .filter(|path| path.extension().is_some_and(|ext| ext == "o"))
                .collect();
            objects.sort();
            assert!(!objects.is_empty(), "no objects from {stem}");
            checked(
                Command::new("ar")
                    .arg("crs")
                    .arg(dir.join("libmaximal_suffix.a"))
                    .args(&objects),
                60,
                &dir.join("archive.log"),
            );
            let executable = dir.join("native.elf");
            checked(
                rustc_command()
                    .args(["--target", TARGET, "-Cpanic=abort"])
                    .arg(root.join("driver.rs"))
                    .arg("-L")
                    .arg(&dir)
                    .arg("-lstatic=maximal_suffix")
                    .arg("-o")
                    .arg(&executable),
                180,
                &dir.join("link.log"),
            );
            let output = checked(&mut Command::new(&executable), 20, &dir.join("native.log"));
            assert_eq!(output.stdout, expected.as_bytes());
            assert!(output.stderr.is_empty());
            assert_eq!(sha256(&backend), digest, "backend changed during {stem}");
        }
    }
}

#[test]
fn no_proof_maximal_suffix_matches_llvm() {
    let artifacts = artifacts();
    let (backend, digest) = backend(&artifacts.0);
    native_case(
        &artifacts.0.join("native"),
        &backend,
        &digest,
        include_str!("maximal_suffix/corpus.rs"),
        include_str!("maximal_suffix/driver.rs"),
        "PASS maximal_suffix checks=29930\n",
        &[("maximal_suffix", VC_PROVEN)],
    );
    println!("TCG_MAXIMAL_SUFFIX_DIAGNOSTIC executions=8 checks=239440 backend_sha256={digest}");
}

/// The default route for the two loops whose back-edge the VC cannot decide
/// (see the boundary test): the SSA-071 cell retry (35c463d81, merged by
/// 817cd8753) re-lowers their misthreaded loop-carried locals in memory cells
/// and re-runs every gate. Each driver checks an independent oracle; the
/// shadow `wrapping_add` is the crate's own `a ^ b`, never core's addition.
#[test]
fn no_proof_maximal_suffix_cell_retry_controls_match_llvm() {
    let artifacts = artifacts();
    let (backend, digest) = backend(&artifacts.0);
    native_case(
        &artifacts.0.join("dependent"),
        &backend,
        &digest,
        include_str!("maximal_suffix/dependent.rs"),
        include_str!("maximal_suffix/dependent_driver.rs"),
        "PASS read_dependent checks=256\n",
        &[("read_dependent", CELL_RETRY)],
    );
    native_case(
        &artifacts.0.join("shadow_wrapping"),
        &backend,
        &digest,
        include_str!("maximal_suffix/shadow_wrapping.rs"),
        include_str!("maximal_suffix/shadow_wrapping_driver.rs"),
        "PASS shadow_wrapping checks=2240\n",
        &[("shadow_wrapping", CELL_RETRY)],
    );
    println!("TCG_MAXIMAL_SUFFIX_CELL_RETRY executions=16 checks=19968 backend_sha256={digest}");
}

#[test]
fn maximal_suffix_retains_model_boundaries() {
    let artifacts = artifacts();
    let (backend, digest) = backend(&artifacts.0);
    // These controls observe the semantic VC's own verdict. `no-vc-diamond`
    // also turns the SSA-071 cell retry off; the other two turn it off
    // explicitly, because the retry admits those loops by storage in memory
    // cells (`no_proof_maximal_suffix_cell_retry_controls_match_llvm`), not by
    // a threading proof. Since 80e82b961 (merged by 817cd8753) the VC models
    // core's pure `<[T]>::get`, so the source walk now reaches the in-loop
    // diamond (disabled) and the read-dependent latch value (dependent) before
    // it fails, instead of stopping at the `get` call.
    for (name, source, extra, reason) in [
        (
            "disabled",
            include_str!("maximal_suffix/corpus.rs"),
            " no-vc-diamond",
            "-Ztrust-ir-cg-args=no-vc-diamond disables modeling it",
        ),
        (
            "dependent",
            include_str!("maximal_suffix/dependent.rs"),
            " no-ssa071-cell-retry",
            "derives from an unmodeled trust-ir value",
        ),
        (
            "shadow_wrapping",
            include_str!("maximal_suffix/shadow_wrapping.rs"),
            " no-ssa071-cell-retry",
            "unmodeled call `wrapping_add`",
        ),
    ] {
        let source_path = artifacts.0.join(format!("{name}.rs"));
        std::fs::write(&source_path, source).unwrap();
        for lane in ["llvm", "cg"] {
            let dir = artifacts.0.join(format!("{name}-{lane}"));
            std::fs::create_dir(&dir).unwrap();
            let mut command = rustc_command();
            command.args([
                "--crate-type=lib",
                "--emit=obj",
                "-Cpanic=abort",
                "-Ccodegen-units=1",
                "-Copt-level=0",
                "--target",
                TARGET,
            ]);
            if lane == "cg" {
                command
                    .arg(format!("-Zcodegen-backend={}", backend.display()))
                    .arg(format!(
                        "-Ztrust-ir-cg-args=diag-json no-proof-certs{extra}"
                    ));
            }
            command.arg(&source_path).arg("--out-dir").arg(&dir);
            let (output, transcript) = run_bounded(&mut command, 180, &dir.join("compile.log"));
            if lane == "llvm" {
                assert!(output.status.success(), "{transcript}");
            } else {
                assert_eq!(output.status.code(), Some(1), "{transcript}");
                assert!(
                    transcript.contains("TCG-SSA-071") && transcript.contains(reason),
                    "{transcript}"
                );
            }
            assert_eq!(sha256(&backend), digest);
        }
    }
    println!("TCG_MAXIMAL_SUFFIX_REFUSAL llvm_accepted=3 cg_refused=3 backend_sha256={digest}");
}
