//! Construct and replace scalar union values through their actual storage.
use super::{Artifacts, TARGET, backend, checked, rustc_command, sha256};
use std::path::PathBuf;
use std::process::Command;

#[test]
fn no_proof_scalar_union_storage_images_match_llvm() {
    let temp = Command::new("mktemp")
        .args(["-d", "-t", "trust-cg-scalar-union-storage.XXXXXX"])
        .output()
        .unwrap();
    assert!(temp.status.success());
    let artifacts = Artifacts(PathBuf::from(
        String::from_utf8(temp.stdout).unwrap().trim(),
    ));
    let root = &artifacts.0;
    let (backend, digest) = backend(root);
    let runtime = super::scalar_cell_runtime::Runtime::build(root);
    std::fs::write(
        root.join("corpus.rs"),
        include_str!("scalar_union_storage/corpus.rs"),
    )
    .unwrap();
    std::fs::write(
        root.join("driver.c"),
        include_str!("scalar_union_storage/driver.c"),
    )
    .unwrap();
    std::fs::write(
        root.join("refused.rs"),
        include_str!("scalar_union_storage/refused.rs"),
    )
    .unwrap();
    let mut checks = 0;
    let mut executions = 0;
    for panic in ["abort", "unwind"] {
        for opt in 0..=3 {
            for lane in ["llvm", "cg"] {
                let dir = root.join(format!("{panic}-{lane}-O{opt}"));
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
                    .arg(format!("-Cpanic={panic}"))
                    .arg(format!("-Copt-level={opt}"));
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
                    .map(|f| f.unwrap().path())
                    .filter(|f| f.extension().is_some_and(|s| s == "o"))
                    .collect();
                objects.sort();
                assert!(!objects.is_empty());
                let mut linker = Command::new("cc");
                linker
                    .args(["-std=c11", "-O2", "-Wall", "-Wextra", "-Werror"])
                    .arg(root.join("driver.c"))
                    .args(&objects);
                runtime.link_into(&mut linker);
                checked(
                    linker.arg("-o").arg(dir.join("native.elf")),
                    60,
                    &dir.join("link.log"),
                );
                let result = checked(
                    &mut Command::new(dir.join("native.elf")),
                    60,
                    &dir.join("native.log"),
                );
                assert_eq!(result.stdout, b"PASS scalar_union_storage checks=212992\n");
                assert!(result.stderr.is_empty());
                checks += 212992;
                executions += 1;
                assert_eq!(sha256(&backend), digest);
            }
        }
    }
    assert_eq!((checks, executions), (3407872, 16));
    // A failed compile may leave partial objects for supported functions. The
    // unsupported required callee must still prevent a runnable program.
    std::fs::write(
        root.join("refused-driver.c"),
        r#"
#include <stdbool.h>
#include <stdint.h>
typedef struct { uint64_t first, second; } Pair;
extern Pair pair(bool condition, Pair first, Pair second);
int main(void) {
    Pair a = {UINT64_C(0x8000000000000001), 17};
    Pair b = {31, UINT64_C(0xffffffffffffffff)};
    for (int condition = 0; condition < 2; ++condition) {
        Pair got = pair(condition != 0, a, b);
        Pair expected = condition ? a : b;
        if (got.first != expected.first || got.second != expected.second) return 1;
    }
    return 0;
}
"#,
    )
    .unwrap();
    let mut refusals = 0;
    for case in ["pair"] {
        for opt in [0, 2] {
            for lane in ["llvm", "cg"] {
                let dir = root.join(format!("refused-{case}-{lane}-O{opt}"));
                std::fs::create_dir(&dir).unwrap();
                let mut command = rustc_command();
                command
                    .args([
                        "--crate-type=lib",
                        "--emit=obj,mir",
                        "-Cpanic=abort",
                        "-Ccodegen-units=1",
                        "--target",
                        TARGET,
                        "--cfg",
                    ])
                    .arg(format!("case=\"{case}\""))
                    .arg(format!("-Copt-level={opt}"));
                if lane == "cg" {
                    command
                        .arg(format!("-Zcodegen-backend={}", backend.display()))
                        .arg("-Ztrust-ir-cg-args=diag-json no-proof-certs");
                }
                command
                    .arg(root.join("refused.rs"))
                    .arg("--out-dir")
                    .arg(&dir);
                if lane == "llvm" {
                    checked(&mut command, 180, &dir.join("compile.log"));
                } else {
                    let (result, _) =
                        super::run_bounded(&mut command, 180, &dir.join("compile.log"));
                    assert!(!result.status.success());
                    let stderr = String::from_utf8_lossy(&result.stderr);
                    assert!(
                        stderr.contains("unsupported intrinsic `select_unpredictable`"),
                        "{stderr}"
                    );
                    assert!(
                        !stderr.contains("internal compiler error")
                            && !stderr.contains("panicked at")
                    );
                    refusals += 1;
                }
                let objects: Vec<_> = std::fs::read_dir(&dir)
                    .unwrap()
                    .map(|entry| entry.unwrap().path())
                    .filter(|path| path.extension().is_some_and(|ext| ext == "o"))
                    .collect();
                if lane == "llvm" || !objects.is_empty() {
                    let executable = dir.join("refused-native.elf");
                    let mut linker = Command::new("cc");
                    linker
                        .args(["-std=c11", "-O2", "-Wall", "-Wextra", "-Werror"])
                        .arg(root.join("refused-driver.c"))
                        .args(&objects);
                    runtime.link_into(&mut linker);
                    linker.arg("-o").arg(&executable);
                    if lane == "llvm" {
                        checked(&mut linker, 60, &dir.join("link.log"));
                        checked(&mut Command::new(&executable), 60, &dir.join("native.log"));
                    } else {
                        let (result, transcript) =
                            super::run_bounded(&mut linker, 60, &dir.join("link.log"));
                        assert!(!result.status.success(), "{transcript}");
                        assert!(
                            String::from_utf8_lossy(&result.stderr).contains("undefined reference"),
                            "{transcript}"
                        );
                        assert!(
                            String::from_utf8_lossy(&result.stderr).contains("__trust_cg_private"),
                            "the refused required callee must remain undefined: {transcript}"
                        );
                        assert!(
                            !executable.exists(),
                            "a refused required callee must not link"
                        );
                    }
                }
                assert_eq!(sha256(&backend), digest);
            }
        }
    }
    assert_eq!(refusals, 2);
    println!(
        "TCG_SCALAR_UNION_STORAGE executions={executions} checks={checks} refusals={refusals} backend_sha256={digest}"
    );
}
