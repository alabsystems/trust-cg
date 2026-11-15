//! Independent crates share upstream inline helpers, including stored callbacks
//! and vtables. All three compilation lanes execute against an LLVM-built oracle.
use super::{Artifacts, TARGET, backend, checked, rustc_command, sha256};
use std::path::{Path, PathBuf};
use std::process::Command;

/// The number of CGU-private function definitions in a `readelf --wide
/// --syms` listing, asserting that each is a `FUNC GLOBAL HIDDEN` symbol.
///
/// Every symbol table row whose name starts with the private namespace
/// `__trust_cg_private.` is a private function symbol: a definition must be
/// `STT_FUNC`, `STB_GLOBAL`, `STV_HIDDEN` (any other type, binding or
/// visibility fails), and an undefined row is a sibling object's reference.
/// The one other kind of row that names the namespace is an `STT_FILE` row: a
/// partial link (`ld -r`, the bridge's multi-object publication) records each
/// input object's file name, and a per-function object is named after its
/// private symbol (`<crate>.__trust_cg_private.<cgu>.<n>.rcgu.o`). A file row
/// is not a symbol definition; it must be `LOCAL`, `ABS` and must not itself
/// start with the namespace, or the listing fails.
fn private_definitions(listing: &str) -> usize {
    const NAMESPACE: &str = "__trust_cg_private.";
    let mut definitions = 0;
    for line in listing.lines() {
        let fields: Vec<&str> = line.split_whitespace().collect();
        let numbered = fields
            .first()
            .and_then(|n| n.strip_suffix(':'))
            .is_some_and(|n| n.parse::<usize>().is_ok());
        if !numbered || !line.contains(NAMESPACE) {
            continue;
        }
        // Num: Value Size Type Bind Vis Ndx Name (an `st_other` annotation
        // such as `[VARIANT_PCS]` may follow Vis, so the name is last and the
        // section index is read from the end).
        assert!(fields.len() >= 8, "unparsed symbol row: {line}");
        let (kind, bind, visibility) = (fields[3], fields[4], fields[5]);
        let section = fields[fields.len() - 2];
        let name = fields[fields.len() - 1];
        if kind == "FILE" {
            assert!(
                bind == "LOCAL" && section == "ABS" && !name.starts_with(NAMESPACE),
                "a file row naming the private namespace must be a LOCAL ABS object name: {line}"
            );
            continue;
        }
        assert!(
            name.starts_with(NAMESPACE),
            "a symbol names the private namespace other than as its prefix: {line}"
        );
        if section != "UND" {
            assert!(
                (kind, bind, visibility) == ("FUNC", "GLOBAL", "HIDDEN"),
                "private definition has wrong ELF binding: {line}"
            );
            definitions += 1;
        }
    }
    definitions
}

#[test]
fn private_definition_rows_are_function_symbols_and_file_rows_are_object_names() {
    let listing = "\
Symbol table '.symtab' contains 4 entries:
   Num:    Value          Size Type    Bind   Vis      Ndx Name
     1: 0000000000000000     0 FILE    LOCAL  DEFAULT  ABS linkage_left.__trust_cg_private.linkage_left.43c75a0efe78502a-cgu.0.2.rcgu.o
     2: 0000000000000000    20 FUNC    GLOBAL HIDDEN     2 __trust_cg_private.linkage_left.43c75a0efe78502a-cgu.0.2
     3: 0000000000000000     0 NOTYPE  GLOBAL HIDDEN   UND __trust_cg_private.linkage_left.43c75a0efe78502a-cgu.0.3
";
    assert_eq!(private_definitions(listing), 1);
    for (wrong, row) in [
        (
            "default visibility",
            "4: 0000000000000000 20 FUNC GLOBAL DEFAULT 2 __trust_cg_private.c.1",
        ),
        (
            "weak binding",
            "4: 0000000000000000 20 FUNC WEAK HIDDEN 2 __trust_cg_private.c.1",
        ),
        (
            "local binding",
            "4: 0000000000000000 20 FUNC LOCAL DEFAULT 2 __trust_cg_private.c.1",
        ),
        (
            "data type",
            "4: 0000000000000000 8 OBJECT GLOBAL HIDDEN 2 __trust_cg_private.c.1",
        ),
        (
            "untyped definition",
            "4: 0000000000000000 0 NOTYPE GLOBAL HIDDEN 2 __trust_cg_private.c.1",
        ),
        (
            "non-prefix name",
            "4: 0000000000000000 20 FUNC GLOBAL HIDDEN 2 x__trust_cg_private.c.1",
        ),
        (
            "global file row",
            "4: 0000000000000000 0 FILE GLOBAL DEFAULT ABS a.__trust_cg_private.c.1.rcgu.o",
        ),
        (
            "file row in a section",
            "4: 0000000000000000 0 FILE LOCAL DEFAULT 2 a.__trust_cg_private.c.1.rcgu.o",
        ),
        (
            "file row named as the symbol",
            "4: 0000000000000000 0 FILE LOCAL DEFAULT ABS __trust_cg_private.c.1",
        ),
    ] {
        let listing = format!("{listing}     {row}\n");
        assert!(
            std::panic::catch_unwind(|| private_definitions(&listing)).is_err(),
            "the {wrong} row was accepted: {row}"
        );
    }
}

fn objects(dir: &Path) -> Vec<PathBuf> {
    let mut objects: Vec<_> = std::fs::read_dir(dir)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .filter(|path| path.extension().is_some_and(|ext| ext == "o"))
        .collect();
    objects.sort();
    assert!(!objects.is_empty(), "missing objects in {}", dir.display());
    objects
}

#[test]
fn no_proof_private_function_linkage_matches_llvm() {
    let temp = checked(
        Command::new("mktemp").args(["-d", "-t", "trust-cg-function-linkage.XXXXXX"]),
        10,
        &std::env::temp_dir().join("trust-cg-function-linkage-mktemp.log"),
    );
    let artifacts = Artifacts(PathBuf::from(
        String::from_utf8(temp.stdout).unwrap().trim(),
    ));
    let root = &artifacts.0;
    let (backend, digest) = backend(root);
    for (name, source) in [
        ("base.rs", include_str!("function_linkage/base.rs")),
        ("consumer.rs", include_str!("function_linkage/consumer.rs")),
        ("driver.rs", include_str!("function_linkage/driver.rs")),
        (
            "executable.rs",
            include_str!("function_linkage/executable.rs"),
        ),
    ] {
        std::fs::write(root.join(name), source).unwrap();
    }
    let mut runs = Vec::new();
    for opt in [0, 2] {
        for cgus in [1, 8] {
            for lane in ["llvm", "cg-batch", "cg-legacy"] {
                let dir = root.join(format!("{lane}-O{opt}-cgu{cgus}"));
                std::fs::create_dir(&dir).unwrap();
                let mut archives = Vec::new();
                let mut private_symbols = 0;
                for unit in ["base", "left", "right"] {
                    let unit_dir = dir.join(unit);
                    std::fs::create_dir(&unit_dir).unwrap();
                    let mut command = rustc_command();
                    command
                        .args([
                            "--target",
                            TARGET,
                            "--crate-type=rlib",
                            "-Cpanic=abort",
                            "-Cdebug-assertions=no",
                            "-Coverflow-checks=no",
                            "-Zprint-mono-items=yes",
                        ])
                        .arg(format!("-Copt-level={opt}"))
                        .arg(format!("-Ccodegen-units={cgus}"))
                        .arg(format!("--crate-name=linkage_{unit}"))
                        .arg("--out-dir")
                        .arg(&unit_dir);
                    if lane != "llvm" {
                        command.arg(format!("-Zcodegen-backend={}", backend.display()))
                            .arg(if lane == "cg-batch" { "-Ztrust-ir-cg-args=diag-json no-proof-certs batch-trace batch-cgu=1" } else { "-Ztrust-ir-cg-args=diag-json no-proof-certs batch-trace batch-cgu=0" });
                    }
                    if unit == "base" {
                        command
                            .arg("--emit=link,metadata")
                            .arg(root.join("base.rs"));
                    } else {
                        command
                            .arg("--emit=obj")
                            .arg("--cfg")
                            .arg(unit)
                            .arg(format!(
                                "--extern=linkage_base={}",
                                dir.join("base/liblinkage_base.rlib").display()
                            ))
                            .arg(root.join("consumer.rs"));
                    }
                    let output = checked(&mut command, 180, &unit_dir.join("compile.log"));
                    if opt == 0 && cgus == 1 && unit != "base" {
                        let mono = format!(
                            "{}{}",
                            String::from_utf8_lossy(&output.stdout),
                            String::from_utf8_lossy(&output.stderr)
                        );
                        assert!(
                            mono.lines()
                                .any(|line| line.contains("base::shared")
                                    && line.contains("[Internal]")),
                            "fixture did not collect private upstream shared helper"
                        );
                    }
                    let object_dir = if unit == "base" {
                        let extracted = unit_dir.join("archive-members");
                        std::fs::create_dir(&extracted).unwrap();
                        checked(
                            Command::new("ar")
                                .arg("x")
                                .arg(unit_dir.join("liblinkage_base.rlib"))
                                .current_dir(&extracted),
                            30,
                            &unit_dir.join("extract.log"),
                        );
                        extracted
                    } else {
                        unit_dir.clone()
                    };
                    let objects = objects(&object_dir);
                    let symbols = checked(
                        Command::new("readelf")
                            .args(["--wide", "--syms"])
                            .args(&objects),
                        30,
                        &unit_dir.join("symbols.log"),
                    );
                    let symbols = String::from_utf8(symbols.stdout).unwrap();
                    private_symbols += private_definitions(&symbols);
                    if unit != "base" {
                        let archive = unit_dir.join(format!("lib{unit}.a"));
                        checked(
                            Command::new("ar").arg("crs").arg(&archive).args(&objects),
                            30,
                            &unit_dir.join("archive.log"),
                        );
                        archives.push(archive);
                    }
                }
                if lane != "llvm" && opt == 0 {
                    assert!(private_symbols >= 3);
                }
                archives.push(dir.join("base/liblinkage_base.rlib"));
                let executable = dir.join("native.elf");
                let mut linker = rustc_command();
                linker
                    .args(["--target", TARGET, "-Cpanic=abort"])
                    .arg(root.join("driver.rs"))
                    .arg("-o")
                    .arg(&executable);
                for archive in &archives {
                    linker.arg(format!("-Clink-arg={}", archive.display()));
                }
                checked(&mut linker, 180, &dir.join("link.log"));
                let result = checked(&mut Command::new(&executable), 30, &dir.join("native.log"));
                assert_eq!(result.stdout, b"function linkage: 360449 native checks\n");
                assert!(result.stderr.is_empty());
                let mut executable_checks = 0;
                if opt == 0 && cgus == 8 {
                    let executable = dir.join("self-linked.elf");
                    let mut command = rustc_command();
                    command
                        .args([
                            "--target",
                            TARGET,
                            "--crate-type=bin",
                            "--crate-name=linkage_executable",
                            "-Cpanic=abort",
                            "-Copt-level=0",
                            "-Ccodegen-units=8",
                            "-Cdebug-assertions=no",
                            "-Coverflow-checks=no",
                            "-Zprint-mono-items=yes",
                            "-Clink-arg=-lc",
                        ])
                        .arg(format!(
                            "--extern=linkage_base={}",
                            dir.join("base/liblinkage_base.rlib").display()
                        ))
                        .arg(root.join("executable.rs"))
                        .arg("-o")
                        .arg(&executable);
                    if lane != "llvm" {
                        command.arg(format!("-Zcodegen-backend={}", backend.display()))
                            .arg(if lane == "cg-batch" { "-Ztrust-ir-cg-args=diag-json no-proof-certs batch-trace batch-cgu=1" } else { "-Ztrust-ir-cg-args=diag-json no-proof-certs batch-trace batch-cgu=0" });
                    }
                    let output = checked(&mut command, 180, &dir.join("self-linked-compile.log"));
                    let mono = String::from_utf8(output.stdout).unwrap();
                    assert!(
                        mono.lines().any(|line| line.contains("base::repeated")
                            && line.matches("[Internal]").count() >= 2),
                        "fixture must exercise several copies of one reachable function"
                    );
                    let output = checked(
                        &mut Command::new(&executable),
                        30,
                        &dir.join("self-linked-native.log"),
                    );
                    assert!(output.stdout.is_empty() && output.stderr.is_empty());
                    executable_checks = 8192;
                }
                assert_eq!(sha256(&backend), digest);
                runs.push(serde_json::json!({"opt":opt, "cgus":cgus, "lane":lane, "private_definitions":private_symbols, "checks":360449, "executable_checks":executable_checks, "executable_sha256":sha256(&executable)}));
            }
        }
    }
    std::fs::write(
        root.join("results.json"),
        serde_json::to_vec_pretty(&serde_json::json!({"backend_sha256":digest, "runs":runs}))
            .unwrap(),
    )
    .unwrap();
}

#[test]
fn private_function_namespace_refusals() {
    let temp = Command::new("mktemp")
        .args(["-d", "-t", "trust-cg-function-linkage-refusal.XXXXXX"])
        .output()
        .unwrap();
    assert!(temp.status.success());
    let artifacts = Artifacts(PathBuf::from(
        String::from_utf8(temp.stdout).unwrap().trim(),
    ));
    let root = &artifacts.0;
    let (backend, digest) = backend(root);
    for (name, source) in [
        (
            "export",
            "#![no_std]\n#[unsafe(export_name=\"__trust_cg_private.foreign.0\")] pub fn f(x:u64)->u64 { x }\n",
        ),
        (
            "import",
            "#![no_std]\nunsafe extern \"C\" { #[link_name=\"__trust_cg_private.foreign.0\"] fn f(x:u64)->u64; } #[unsafe(no_mangle)] pub fn call(x:u64)->u64 { unsafe { f(x) } }\n",
        ),
    ] {
        let source_path = root.join(format!("{name}.rs"));
        std::fs::write(&source_path, source).unwrap();
        for lane in ["llvm", "cg"] {
            let dir = root.join(format!("{name}-{lane}"));
            std::fs::create_dir(&dir).unwrap();
            let mut command = rustc_command();
            command
                .args([
                    "--crate-type=lib",
                    "--emit=obj",
                    "--target",
                    TARGET,
                    "-Cpanic=abort",
                    "-Ccodegen-units=1",
                ])
                .arg(&source_path)
                .arg("--out-dir")
                .arg(&dir);
            if lane == "cg" {
                command
                    .arg(format!("-Zcodegen-backend={}", backend.display()))
                    .arg("-Ztrust-ir-cg-args=diag-json no-proof-certs");
                let output = command.output().unwrap();
                std::fs::write(
                    dir.join("compile.log"),
                    format!(
                        "command: {command:?}\nstatus: {}\nstdout:\n{}\nstderr:\n{}",
                        output.status,
                        String::from_utf8_lossy(&output.stdout),
                        String::from_utf8_lossy(&output.stderr)
                    ),
                )
                .unwrap();
                assert!(!output.status.success());
                let error = String::from_utf8(output.stderr).unwrap();
                assert!(error.contains("function linkage"));
                assert!(
                    error.contains("reserved private function namespace")
                        || error.contains("collides with an existing module symbol")
                );
            } else {
                checked(&mut command, 60, &dir.join("compile.log"));
            }
        }
    }
    assert_eq!(sha256(&backend), digest);
}
