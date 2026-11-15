// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
// Native GNU/Linux AArch64 reference identity and destructor state, with an
// independent C observer. Other hosts compile no native test.
#![cfg(all(
    target_os = "linux",
    target_env = "gnu",
    target_arch = "aarch64",
    target_pointer_width = "64"
))]

#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

use std::fs::{self, File};
use std::path::Path;
use std::process::{Command, Output, Stdio};
use std::time::{Duration, Instant};

fn execute(
    command: &mut Command,
    directory: &Path,
    name: &str,
    seconds: u64,
) -> Result<Output, String> {
    let stdout = directory.join(format!("{name}.stdout"));
    let stderr = directory.join(format!("{name}.stderr"));
    fs::write(
        directory.join(format!("{name}.command")),
        format!("{command:?}\n"),
    )
    .unwrap();
    command
        .stdin(Stdio::null())
        .stdout(File::create(&stdout).unwrap())
        .stderr(File::create(&stderr).unwrap());
    let mut child = command
        .spawn()
        .map_err(|error| format!("spawn {name}: {error}"))?;
    let start = Instant::now();
    loop {
        if let Some(status) = child.try_wait().map_err(|error| error.to_string())? {
            return Ok(Output {
                status,
                stdout: fs::read(&stdout).unwrap(),
                stderr: fs::read(&stderr).unwrap(),
            });
        }
        if start.elapsed() >= Duration::from_secs(seconds) {
            let _ = child.kill();
            let _ = child.wait();
            return Err(format!("{name} timed out after {seconds} seconds"));
        }
        std::thread::sleep(Duration::from_millis(10));
    }
}

fn sha256(path: &Path) -> String {
    let result = Command::new("sha256sum")
        .arg(path)
        .output()
        .expect("sha256sum");
    assert!(result.status.success());
    let output = String::from_utf8(result.stdout).unwrap();
    let hash = output.split_whitespace().next().unwrap();
    assert_eq!(hash.len(), 64);
    hash.to_owned()
}

#[test]
fn droppable_scalar_references_preserve_identity_mutation_and_cleanup() {
    let temp = Command::new("mktemp")
        .args(["-d", "-t", "trust-cg-droppable-scalar.XXXXXX"])
        .output()
        .expect("mktemp");
    assert!(temp.status.success());
    let directory = std::path::PathBuf::from(String::from_utf8(temp.stdout).unwrap().trim());
    eprintln!(
        "droppable scalar reference artifacts: {}",
        directory.display()
    );
    let source = directory.join("input.rs");
    let observer = directory.join("observer.c");
    let object = directory.join("observer.o");
    fs::write(
        &source,
        include_str!("support/droppable_scalar_reference/input.rs"),
    )
    .unwrap();
    fs::write(
        &observer,
        include_str!("support/droppable_scalar_reference/observer.c"),
    )
    .unwrap();
    let cc = execute(
        Command::new("cc")
            .args(["-std=c11", "-O2", "-c"])
            .arg(&observer)
            .arg("-o")
            .arg(&object),
        &directory,
        "observer-build",
        30,
    )
    .unwrap();
    assert!(
        cc.status.success(),
        "{}",
        String::from_utf8_lossy(&cc.stderr)
    );
    let backend = backend_artifact_support::current_test_backend();
    let backend_sha = sha256(&backend);
    fs::write(
        directory.join("backend-sha256.txt"),
        format!("{backend_sha}\n"),
    )
    .unwrap();
    let mut failures = Vec::new();
    let mut records = Vec::new();
    let mut matched = 0;
    for (family, flag) in [
        ("integer", None),
        ("float", Some("float_home")),
        ("padded", Some("padded_home")),
    ] {
        for opt in 0..=3 {
            for unwind in [false, true] {
                let panic = if unwind { "unwind" } else { "abort" };
                let label = format!("{family}-O{opt}-{panic}");
                let case = directory.join(&label);
                fs::create_dir(&case).unwrap();
                let lane = |name: &str, codegen: Option<&Path>| -> Result<Vec<u8>, String> {
                    let executable = case.join(name);
                    let mut command = toolchain_support::rustc_command();
                    command
                        .args(["--crate-type=bin", "-Ccodegen-units=1"])
                        .arg(format!("-Copt-level={opt}"))
                        .arg(format!("-Cpanic={panic}"))
                        .args([
                            "--check-cfg=cfg(float_home)",
                            "--check-cfg=cfg(padded_home)",
                            "--check-cfg=cfg(scalar_unwind)",
                        ]);
                    if let Some(flag) = flag {
                        command.args(["--cfg", flag]);
                    }
                    if unwind {
                        command.args(["--cfg", "scalar_unwind"]);
                    }
                    if let Some(backend) = codegen {
                        let mut selected = std::ffi::OsString::from("-Zcodegen-backend=");
                        selected.push(backend);
                        command
                            .arg(selected)
                            .arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]));
                    }
                    let mut link = std::ffi::OsString::from("-Clink-arg=");
                    link.push(&object);
                    command.arg(link).arg(&source).arg("-o").arg(&executable);
                    let compile = execute(&mut command, &case, &format!("{name}-compile"), 180)?;
                    if !compile.status.success() {
                        return Err(format!(
                            "{name} compile {}: {}",
                            compile.status,
                            String::from_utf8_lossy(&compile.stderr)
                        ));
                    }
                    let run = execute(
                        &mut Command::new(&executable),
                        &case,
                        &format!("{name}-native"),
                        30,
                    )?;
                    if !run.status.success() {
                        return Err(format!(
                            "{name} native {}: {}",
                            run.status,
                            String::from_utf8_lossy(&run.stderr)
                        ));
                    }
                    if !run.stdout.starts_with(b"2 ")
                        || !run.stdout.ends_with(b" 4\n")
                        || run.stdout.iter().filter(|byte| **byte == b'\n').count() != 1
                    {
                        return Err(format!(
                            "{name} did not finish both destructors and four observations: {:?}",
                            String::from_utf8_lossy(&run.stdout)
                        ));
                    }
                    Ok(run.stdout)
                };
                let oracle = lane("llvm", None);
                let candidate = lane("cg", Some(&backend));
                let status = match (oracle, candidate) {
                    (Ok(a), Ok(b)) if a == b => {
                        matched += 1;
                        "MATCH"
                    }
                    (a, b) => {
                        failures.push(format!("{label}: LLVM={a:?} CG={b:?}"));
                        "FAIL"
                    }
                };
                records.push(format!("{label}\t{status}"));
                fs::write(directory.join("results.tsv"), records.join("\n") + "\n").unwrap();
            }
        }
    }
    assert_eq!(sha256(&backend), backend_sha);
    assert_eq!(records.len(), 24);
    eprintln!(
        "DROPPABLE_SCALAR_REFERENCES cells=24 matched={matched} families=integer,float,padded opts=0,1,2,3 panic=abort,unwind observer=C certs=off"
    );
    assert!(
        failures.is_empty(),
        "{} cells failed:\n{}",
        failures.len(),
        failures.join("\n")
    );
    assert_eq!(matched, 24);
}

#[test]
fn catch_unwind_preserves_foreign_exception_pointer_and_payload_cleanup() {
    let temp = Command::new("mktemp")
        .args(["-d", "-t", "trust-cg-catch-foreign.XXXXXX"])
        .output()
        .expect("mktemp");
    assert!(temp.status.success());
    let directory = std::path::PathBuf::from(String::from_utf8(temp.stdout).unwrap().trim());
    eprintln!("foreign catch artifacts: {}", directory.display());
    let source = directory.join("input.rs");
    let observer = directory.join("observer.cpp");
    let object = directory.join("observer.o");
    fs::write(
        &source,
        include_str!("support/droppable_scalar_reference/foreign.rs"),
    )
    .unwrap();
    fs::write(
        &observer,
        include_str!("support/droppable_scalar_reference/foreign.cpp"),
    )
    .unwrap();
    let build = execute(
        Command::new("c++")
            .args(["-std=c++17", "-O2", "-c"])
            .arg(&observer)
            .arg("-o")
            .arg(&object),
        &directory,
        "observer-build",
        60,
    )
    .unwrap();
    assert!(
        build.status.success(),
        "{}",
        String::from_utf8_lossy(&build.stderr)
    );
    let backend = backend_artifact_support::current_test_backend();
    let backend_sha = sha256(&backend);
    fs::write(
        directory.join("backend-sha256.txt"),
        format!("{backend_sha}\n"),
    )
    .unwrap();
    let mut failures = Vec::new();
    let mut records = Vec::new();
    let mut matched = 0;
    for opt in 0..=3 {
        let case = directory.join(format!("O{opt}"));
        fs::create_dir(&case).unwrap();
        let lane = |name: &str, codegen: Option<&Path>| -> Result<Vec<u8>, String> {
            let executable = case.join(name);
            let mut command = toolchain_support::rustc_command();
            command
                .args(["--crate-type=bin", "-Ccodegen-units=1", "-Cpanic=unwind"])
                .arg(format!("-Copt-level={opt}"));
            if let Some(backend) = codegen {
                let mut selected = std::ffi::OsString::from("-Zcodegen-backend=");
                selected.push(backend);
                command
                    .arg(selected)
                    .arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]));
            }
            let mut link = std::ffi::OsString::from("-Clink-arg=");
            link.push(&object);
            command
                .arg(link)
                .arg("-Clink-arg=-lstdc++")
                .arg(&source)
                .arg("-o")
                .arg(&executable);
            let compile = execute(&mut command, &case, &format!("{name}-compile"), 180)?;
            if !compile.status.success() {
                return Err(format!(
                    "{name} compile {}: {}",
                    compile.status,
                    String::from_utf8_lossy(&compile.stderr)
                ));
            }
            let run = execute(
                &mut Command::new(&executable),
                &case,
                &format!("{name}-native"),
                30,
            )?;
            if !run.status.success() || run.stdout != b"true 91 1\n" {
                return Err(format!(
                    "{name} native {}: stdout={:?} stderr={}",
                    run.status,
                    String::from_utf8_lossy(&run.stdout),
                    String::from_utf8_lossy(&run.stderr)
                ));
            }
            Ok(run.stdout)
        };
        let oracle = lane("llvm", None);
        let candidate = lane("cg", Some(&backend));
        let status = match (oracle, candidate) {
            (Ok(a), Ok(b)) if a == b => {
                matched += 1;
                "MATCH"
            }
            (a, b) => {
                failures.push(format!("O{opt}: LLVM={a:?} CG={b:?}"));
                "FAIL"
            }
        };
        records.push(format!("O{opt}\t{status}"));
        fs::write(directory.join("results.tsv"), records.join("\n") + "\n").unwrap();
    }
    assert_eq!(sha256(&backend), backend_sha);
    assert_eq!(records.len(), 4);
    eprintln!(
        "CATCH_FOREIGN cells=4 matched={matched} opts=0,1,2,3 panic=unwind observer=C++ certs=off"
    );
    assert!(failures.is_empty(), "{}", failures.join("\n"));
    assert_eq!(matched, 4);
}

fn symbol_owner_lane(
    case: &Path,
    source: &Path,
    name: &str,
    opt: u8,
    after: bool,
    backend: Option<&Path>,
) -> Result<std::path::PathBuf, String> {
    let executable = case.join(name);
    let mut command = toolchain_support::rustc_command();
    command
        .args(["--crate-type=bin", "-Ccodegen-units=1", "-Cpanic=unwind"])
        .arg(format!("-Copt-level={opt}"));
    command.arg("--check-cfg=cfg(after_helpers)");
    if after {
        command.args(["--cfg", "after_helpers"]);
    }
    if let Some(backend) = backend {
        let mut selected = std::ffi::OsString::from("-Zcodegen-backend=");
        selected.push(backend);
        command
            .arg(selected)
            .arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]));
    }
    command.arg(source).arg("-o").arg(&executable);
    let compile = execute(&mut command, case, &format!("{name}-compile"), 180)?;
    if !compile.status.success() {
        return Err(format!(
            "{name} compile {}: {}",
            compile.status,
            String::from_utf8_lossy(&compile.stderr)
        ));
    }
    let run = execute(
        &mut Command::new(&executable),
        case,
        &format!("{name}-native"),
        30,
    )?;
    if !run.status.success() || run.stdout != b"false 10\n" {
        return Err(format!(
            "{name} native {}: stdout={:?} stderr={}",
            run.status,
            String::from_utf8_lossy(&run.stdout),
            String::from_utf8_lossy(&run.stderr)
        ));
    }
    Ok(executable)
}

#[test]
fn generated_catch_helpers_keep_identity_when_user_exports_collide() {
    let temp = Command::new("mktemp")
        .args(["-d", "-t", "trust-cg-catch-symbols.XXXXXX"])
        .output()
        .expect("mktemp");
    assert!(temp.status.success());
    let directory = std::path::PathBuf::from(String::from_utf8(temp.stdout).unwrap().trim());
    eprintln!("catch symbol artifacts: {}", directory.display());
    let backend = backend_artifact_support::current_test_backend();
    let backend_sha = sha256(&backend);
    fs::write(
        directory.join("backend-sha256.txt"),
        format!("{backend_sha}\n"),
    )
    .unwrap();
    let fixture = include_str!("support/droppable_scalar_reference/symbols.rs");
    let mut records = Vec::new();
    let mut failures = Vec::new();
    let mut matched = 0;
    for opt in 0..=3 {
        for (order, after) in [("before", false), ("after", true)] {
            let seed = directory.join(format!("O{opt}-{order}-neutral"));
            fs::create_dir(&seed).unwrap();
            let source = seed.join("input.rs");
            fs::write(
                &source,
                fixture
                    .replace("__CATCHER_EXPORT__", "user.fixture.catcher")
                    .replace("__FORWARDER_EXPORT__", "user.fixture.forwarder"),
            )
            .unwrap();
            let llvm = symbol_owner_lane(&seed, &source, "llvm", opt, after, None);
            let cg = symbol_owner_lane(&seed, &source, "cg", opt, after, Some(&backend));
            if llvm.is_ok() && cg.is_ok() {
                matched += 1;
                records.push(format!("O{opt}-{order}-neutral\tMATCH"));
            } else {
                failures.push(format!("O{opt}-{order}-neutral: LLVM={llvm:?} CG={cg:?}"));
                records.push(format!("O{opt}-{order}-neutral\tFAIL"));
            }
            let names = (|| -> Result<(String, String), String> {
                let executable = cg.as_ref().map_err(|error| error.clone())?;
                let nm = execute(Command::new("nm").arg(executable), &seed, "symbols", 30)?;
                if !nm.status.success() {
                    return Err(format!(
                        "nm failed: {}",
                        String::from_utf8_lossy(&nm.stderr)
                    ));
                }
                let output = String::from_utf8(nm.stdout).map_err(|error| error.to_string())?;
                let find = |prefix: &str| -> Result<String, String> {
                    let names: Vec<_> = output
                        .lines()
                        .filter_map(|line| {
                            let fields: Vec<_> = line.split_whitespace().collect();
                            (fields.len() == 3 && fields[1] == "t" && fields[2].starts_with(prefix))
                                .then(|| fields[2].to_owned())
                        })
                        .collect();
                    if names.len() != 1 {
                        return Err(format!(
                            "expected one private {prefix} helper, got {names:?}"
                        ));
                    }
                    Ok(names[0].clone())
                };
                Ok((
                    find("trustcg.catch_unwind.catch_entry.")?,
                    find("trustcg.indirect_unwind.catch_entry.")?,
                ))
            })();
            match names {
                Ok((catcher, forwarder)) => {
                    fs::write(
                        seed.join("helper-names.txt"),
                        format!("{catcher}\n{forwarder}\n"),
                    )
                    .unwrap();
                    for (mode, catcher_name, forwarder_name) in [
                        ("catcher", catcher.as_str(), "user.fixture.forwarder"),
                        ("forwarder", "user.fixture.catcher", forwarder.as_str()),
                    ] {
                        let label = format!("O{opt}-{order}-{mode}");
                        let case = directory.join(&label);
                        fs::create_dir(&case).unwrap();
                        let source = case.join("input.rs");
                        fs::write(
                            &source,
                            fixture
                                .replace("__CATCHER_EXPORT__", catcher_name)
                                .replace("__FORWARDER_EXPORT__", forwarder_name),
                        )
                        .unwrap();
                        let llvm = symbol_owner_lane(&case, &source, "llvm", opt, after, None);
                        let cg =
                            symbol_owner_lane(&case, &source, "cg", opt, after, Some(&backend));
                        if llvm.is_ok() && cg.is_ok() {
                            matched += 1;
                            records.push(format!("{label}\tMATCH"));
                        } else {
                            failures.push(format!("{label}: LLVM={llvm:?} CG={cg:?}"));
                            records.push(format!("{label}\tFAIL"));
                        }
                    }
                }
                Err(error) => {
                    failures.push(format!("O{opt}-{order} helper discovery: {error}"));
                    records.push(format!("O{opt}-{order}-catcher\tNOT_REACHED"));
                    records.push(format!("O{opt}-{order}-forwarder\tNOT_REACHED"));
                }
            }
            fs::write(directory.join("results.tsv"), records.join("\n") + "\n").unwrap();
        }
    }
    assert_eq!(sha256(&backend), backend_sha);
    assert_eq!(records.len(), 24);
    eprintln!(
        "CATCH_SYMBOL_OWNERSHIP cells=24 matched={matched} opts=0,1,2,3 modes=neutral,catcher,forwarder order=before,after certs=off"
    );
    assert!(failures.is_empty(), "{}", failures.join("\n"));
    assert_eq!(matched, 24);
}
