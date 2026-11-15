//! Projected wide-pointer images carry both words across reads, writes and drop glue.
//! Diagnostic codegen only; proof-required admission remains a separate gate.
use super::{Artifacts, TARGET, backend, checked, run_bounded, rustc_command, sha256};
use std::path::{Path, PathBuf};
use std::process::Command;

fn artifacts() -> Artifacts {
    let temp = Command::new("mktemp")
        .args(["-d", "-t", "trust-cg-wide-projection.XXXXXX"])
        .output()
        .expect("mktemp wide_projection artifacts");
    assert!(temp.status.success());
    Artifacts(PathBuf::from(
        String::from_utf8(temp.stdout).unwrap().trim(),
    ))
}

fn native_case(
    root: &Path,
    backend: &Path,
    digest: &str,
    rust: &str,
    driver: &str,
    expected: &str,
    panic_mode: &str,
) {
    std::fs::create_dir(root).unwrap();
    std::fs::write(root.join("corpus.rs"), rust).unwrap();
    std::fs::write(root.join("driver.rs"), driver).unwrap();
    let shared = root.join("libwide_projection_types.rlib");
    std::fs::write(
        root.join("types.rs"),
        include_str!("wide_projection/types.rs"),
    )
    .unwrap();
    checked(
        rustc_command()
            .args([
                "--crate-type=rlib",
                "--crate-name=wide_projection_types",
                "--target",
                TARGET,
            ])
            .arg(format!("-Cpanic={panic_mode}"))
            .arg(root.join("types.rs"))
            .arg("-o")
            .arg(&shared),
        180,
        &root.join("types-compile.log"),
    );
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
            command.arg(format!("-Copt-level={opt}"));
            command.arg(format!(
                "--extern=wide_projection_types={}",
                shared.display()
            ));
            command.arg(format!("-Cpanic={panic_mode}"));
            if lane == "cg" {
                command
                    .arg(format!("-Zcodegen-backend={}", backend.display()))
                    .arg("-Ztrust-ir-cg-args=diag-json no-proof-certs");
            }
            command
                .arg(root.join("corpus.rs"))
                .arg("--out-dir")
                .arg(&dir);
            checked(&mut command, 180, &dir.join("compile.log"));
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
                    .arg(dir.join("libwide_projection.a"))
                    .args(&objects),
                60,
                &dir.join("archive.log"),
            );
            let executable = dir.join("native.elf");
            checked(
                rustc_command()
                    .args(["--target", TARGET])
                    .arg(format!("-Cpanic={panic_mode}"))
                    .arg(root.join("driver.rs"))
                    .arg(format!(
                        "--extern=wide_projection_types={}",
                        shared.display()
                    ))
                    .arg("-L")
                    .arg(&dir)
                    .arg("-lstatic=wide_projection")
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
fn no_proof_wide_projection_matches_llvm() {
    let artifacts = artifacts();
    let (backend, digest) = backend(&artifacts.0);
    native_case(
        &artifacts.0.join("native"),
        &backend,
        &digest,
        include_str!("wide_projection/corpus.rs"),
        include_str!("wide_projection/driver.rs"),
        "PASS wide_projection checks=150528\n",
        "abort",
    );
    println!("TCG_WIDE_PROJECTION_DIAGNOSTIC executions=8 checks=1204224 backend_sha256={digest}");
}
#[test]
fn no_proof_wide_projection_known_refusals_remain_named() {
    let artifacts = artifacts();
    let (backend, digest) = backend(&artifacts.0);
    // `owned.rs` under -Cpanic=unwind ("indirect vtable drop call cannot enter
    // a landing pad") left this list when 8df247a87 lowered indirect calls with
    // a cleanup edge; it is a native positive in
    // `no_proof_wide_projection_owned_matches_llvm` below.
    for (name, source, panic_mode, reason) in [(
        "collection",
        include_str!("wide_projection/negative_collection.rs"),
        "abort",
        "TCG-COLLECTION-IMAGE",
    )] {
        let source_path = artifacts.0.join(format!("{name}.rs"));
        std::fs::write(&source_path, source).unwrap();
        for lane in ["llvm", "cg"] {
            let dir = artifacts.0.join(format!("{name}-{lane}"));
            std::fs::create_dir(&dir).unwrap();
            let mut command = rustc_command();
            command
                .args([
                    "--crate-type=lib",
                    "--emit=obj",
                    "-Copt-level=0",
                    "-Ccodegen-units=1",
                    "--target",
                    TARGET,
                ])
                .arg(format!("-Cpanic={panic_mode}"))
                .arg(&source_path)
                .arg("--out-dir")
                .arg(&dir);
            if lane == "cg" {
                command
                    .arg(format!("-Zcodegen-backend={}", backend.display()))
                    .arg("-Ztrust-ir-cg-args=diag-json no-proof-certs");
                let (result, log) = run_bounded(&mut command, 180, &dir.join("compile.log"));
                assert_eq!(result.status.code(), Some(1), "{name}: {log}");
                assert!(log.contains(reason), "{name}: {log}");
            } else {
                checked(&mut command, 180, &dir.join("compile.log"));
            }
        }
        assert_eq!(sha256(&backend), digest);
    }
    println!("TCG_WIDE_PROJECTION_NEGATIVE cases=1 backend_sha256={digest}");
}

#[test]
fn no_proof_wide_projection_owned_matches_llvm() {
    let artifacts = artifacts();
    let (backend, digest) = backend(&artifacts.0);
    let runtime = super::scalar_cell_runtime::Runtime::build(&artifacts.0);
    let root = artifacts.0.join("owned");
    std::fs::create_dir(&root).unwrap();
    std::fs::write(
        root.join("corpus.rs"),
        include_str!("wide_projection/owned.rs"),
    )
    .unwrap();
    std::fs::write(
        root.join("driver.c"),
        include_str!("wide_projection/owned_driver.c"),
    )
    .unwrap();
    // Under -Cpanic=unwind each Box<dyn> drop calls the vtable drop with a
    // cleanup edge to the box release (formerly refused: "indirect vtable drop
    // call cannot enter a landing pad"). This driver's drops never unwind, so
    // the unwind lanes check the normal path of the landing-pad build; the
    // panicking vtable drop itself executes in
    // `residual_conversion::no_proof_dyn_drop_unwind_matches_llvm`.
    for (opt, panic) in (0..=3).flat_map(|opt| [(opt, "abort"), (opt, "unwind")]) {
        for lane in ["llvm", "cg"] {
            let dir = root.join(format!("{lane}-{panic}-O{opt}"));
            std::fs::create_dir(&dir).unwrap();
            let mut command = rustc_command();
            command.args([
                "--crate-type=lib",
                "--emit=obj,mir",
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
                    .arg("-Ztrust-ir-cg-args=diag-json no-proof-certs");
            }
            command
                .arg(root.join("corpus.rs"))
                .arg("--out-dir")
                .arg(&dir);
            checked(&mut command, 180, &dir.join("compile.log"));
            let mut objects: Vec<_> = std::fs::read_dir(&dir)
                .unwrap()
                .map(|e| e.unwrap().path())
                .filter(|p| p.extension().is_some_and(|e| e == "o"))
                .collect();
            objects.sort();
            assert!(!objects.is_empty());
            let executable = dir.join("native.elf");
            let mut command = Command::new("cc");
            command
                .args(["-std=c11", "-O2"])
                .arg(root.join("driver.c"))
                .args(&objects);
            runtime.link_into(&mut command);
            checked(
                command.arg("-o").arg(&executable),
                180,
                &dir.join("link.log"),
            );
            let output = checked(&mut Command::new(&executable), 20, &dir.join("native.log"));
            assert_eq!(output.stdout, b"PASS wide_projection_owned checks=70658\n");
            assert!(output.stderr.is_empty());
            assert_eq!(sha256(&backend), digest);
        }
    }
    println!("TCG_WIDE_PROJECTION_OWNED executions=16 checks=1130528 backend_sha256={digest}");
}
