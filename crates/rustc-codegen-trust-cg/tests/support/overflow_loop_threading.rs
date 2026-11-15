//! Overflowing loop updates and conditional exits retain their back-edge values.
//! Diagnostic codegen only; proof-required admission remains a separate gate.
use super::{Artifacts, TARGET, backend, checked, run_bounded, rustc_command, sha256};
use std::path::{Path, PathBuf};
use std::process::Command;

fn artifacts() -> Artifacts {
    let temp = Command::new("mktemp")
        .args(["-d", "-t", "trust-cg-overflow-loop-threading.XXXXXX"])
        .output()
        .expect("mktemp overflow_loop_threading artifacts");
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
    panic: &str,
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
                "-Ccodegen-units=1",
                "--target",
                TARGET,
            ]);
            command
                .arg(format!("-Copt-level={opt}"))
                .arg(format!("-Cpanic={panic}"));
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
                    .arg(dir.join("liboverflow_loop_threading.a"))
                    .args(&objects),
                60,
                &dir.join("archive.log"),
            );
            let executable = dir.join("native.elf");
            checked(
                rustc_command()
                    .args(["--target", TARGET])
                    .arg(format!("-Cpanic={panic}"))
                    .arg(root.join("driver.rs"))
                    .arg("-L")
                    .arg(&dir)
                    .arg("-lstatic=overflow_loop_threading")
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
fn no_proof_overflow_loop_threading_matches_llvm() {
    let artifacts = artifacts();
    let (backend, digest) = backend(&artifacts.0);
    // Since the wasm32 bridge port merged with main (991b0f996), the four pow_*
    // loops no longer leave a structurally misthreaded back-edge at O0, so no
    // VC proof is due for them; the driver's independent oracle still checks
    // every result. overflow_rotate and triangle_loop still need the VC.
    for panic in ["abort", "unwind"] {
        native_case(
            &artifacts.0.join(format!("native-{panic}")),
            &backend,
            &digest,
            include_str!("overflow_loop_threading/corpus.rs"),
            include_str!("overflow_loop_threading/driver.rs"),
            "PASS overflow_loop_threading checks=24576\n",
            panic,
            &[("overflow_rotate", VC_PROVEN), ("triangle_loop", VC_PROVEN)],
        );
    }
    println!(
        "TCG_OVERFLOW_LOOP_THREADING_DIAGNOSTIC executions=16 checks=393216 backend_sha256={digest}"
    );
}

/// The default route for the shadowed `overflowing_add`: the VC declines the
/// unmodeled call (see the boundary test), and the SSA-071 cell retry
/// (35c463d81, merged by 817cd8753) re-lowers the misthreaded loop-carried
/// locals in memory cells and re-runs every gate. The driver's oracle uses the
/// crate's own `(a ^ b, true)` method, so a backend that gave the shadow core
/// semantics would return sums and fail here.
#[test]
fn no_proof_overflow_shadow_cell_retry_matches_llvm() {
    let artifacts = artifacts();
    let (backend, digest) = backend(&artifacts.0);
    for panic in ["abort", "unwind"] {
        native_case(
            &artifacts.0.join(format!("shadow-{panic}")),
            &backend,
            &digest,
            include_str!("overflow_loop_threading/shadow.rs"),
            include_str!("overflow_loop_threading/shadow_driver.rs"),
            "PASS shadow_loop checks=3150\n",
            panic,
            &[("shadow_loop", CELL_RETRY)],
        );
    }
    println!("TCG_OVERFLOW_SHADOW_CELL_RETRY executions=16 checks=50400 backend_sha256={digest}");
}

#[test]
fn overflow_loop_threading_retains_model_boundaries() {
    let artifacts = artifacts();
    let (backend, digest) = backend(&artifacts.0);
    for panic in ["abort", "unwind"] {
        // These controls observe the semantic VC's own verdict. `no-vc-diamond`
        // also turns the SSA-071 cell retry off; the shadow control turns it off
        // explicitly, because the retry admits that loop by storage in memory
        // cells (`no_proof_overflow_shadow_cell_retry_matches_llvm`), not by a
        // threading proof.
        for (name, source, extra, reason) in [
            (
                "disabled",
                include_str!("overflow_loop_threading/corpus.rs"),
                " no-vc-diamond",
                "diamond",
            ),
            (
                "shadow",
                include_str!("overflow_loop_threading/shadow.rs"),
                " no-ssa071-cell-retry",
                "unmodeled call `overflowing_add`",
            ),
        ] {
            let source_path = artifacts.0.join(format!("{name}-{panic}.rs"));
            std::fs::write(&source_path, source).unwrap();
            for lane in ["llvm", "cg"] {
                let dir = artifacts.0.join(format!("{name}-{panic}-{lane}"));
                std::fs::create_dir(&dir).unwrap();
                let mut command = rustc_command();
                command.args([
                    "--crate-type=lib",
                    "--emit=obj",
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
                command
                    .arg(format!("-Cpanic={panic}"))
                    .arg(&source_path)
                    .arg("--out-dir")
                    .arg(&dir);
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
    }
    println!("TCG_OVERFLOW_LOOP_REFUSAL llvm_accepted=4 cg_refused=4 backend_sha256={digest}");
}
