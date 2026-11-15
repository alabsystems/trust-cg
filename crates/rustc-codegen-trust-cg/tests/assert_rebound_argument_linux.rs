//! A later sole assignment to a runtime argument cannot license an earlier bounds assert.
//! Four Linux AArch64 LLVM/CG O0/O2 cells use independent LLVM provider and caller.
//! MIR optimization is explicitly disabled so each cell must retain the causal argument read
//! before the later zero write. Runtime checks and constant-object symbol checks are distinct.
#![cfg(all(target_os = "linux", target_arch = "aarch64"))]

#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

use std::collections::HashMap;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitStatus, Stdio};
use std::time::{Duration, Instant};

const PROVIDER: &str = include_str!("support/constant_assert_rebound/provider.rs");
const CALLEE: &str = include_str!("support/constant_assert_rebound/callee.rs");
const CALLER: &str = include_str!("support/constant_assert_rebound/caller.rs");
const CONSTANT: &str = include_str!("support/constant_assert_rebound/constant.rs");

fn run(command: &mut Command, log: &Path, limit: Duration) -> ExitStatus {
    let mut output = std::fs::File::create(log).expect("create constant-assert log");
    writeln!(output, "{command:?}").expect("record command");
    command
        .stdout(Stdio::from(output.try_clone().unwrap()))
        .stderr(Stdio::from(output.try_clone().unwrap()));
    let mut child = command.spawn().expect("execute constant-assert command");
    let started = Instant::now();
    loop {
        match child.try_wait().expect("poll constant-assert command") {
            Some(status) => {
                writeln!(output, "status={status:?}").expect("record status");
                return status;
            }
            None if started.elapsed() >= limit => {
                let _ = child.kill();
                let _ = child.wait();
                panic!("constant-assert command timed out; {}", log.display());
            }
            None => std::thread::sleep(Duration::from_millis(5)),
        }
    }
}

struct Compile<'a> {
    name: &'a str,
    source: &'a Path,
    output: &'a Path,
    opt: u8,
    backend: Option<&'a Path>,
    mode: &'a str,
    externs: &'a [(&'a str, &'a Path)],
    mir: Option<&'a Path>,
}

fn compile(root: &Path, request: Compile<'_>) {
    let mut command = toolchain_support::rustc_command_with_edition("2021");
    command
        .args([
            "-Cpanic=abort",
            "-Coverflow-checks=off",
            "-Ccodegen-units=1",
            // Keep the paired raw MIR spelling explicit across backend printer scopes.
            "-Ztrim-diagnostic-paths=no",
            "-Zmir-opt-level=0",
        ])
        .arg(format!("-Copt-level={}", request.opt))
        .arg(format!("--crate-name={}", request.name))
        .arg(format!("-Ldependency={}", root.display()));
    match request.mode {
        "rlib" => {
            command.arg("--crate-type=rlib");
        }
        "object" => {
            command.args(["--crate-type=lib", "--emit=obj"]);
        }
        "bin" => {}
        _ => panic!("invalid compile mode"),
    }
    if let Some(backend) = request.backend {
        command
            .arg(format!("-Zcodegen-backend={}", backend.display()))
            .arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]));
    }
    if let Some(mir) = request.mir {
        command
            .arg("-Zdump-mir=rebinding_bounds")
            .arg(format!("-Zdump-mir-dir={}", mir.display()));
    }
    for (name, path) in request.externs {
        command
            .arg("--extern")
            .arg(format!("{name}={}", path.display()));
    }
    for (key, _) in std::env::vars_os() {
        let name = key.to_string_lossy();
        if name.starts_with("TCG_")
            || name.starts_with("AY_")
            || name.starts_with("TRUST_IR_CG_")
            || name.starts_with("TRUST_CG_")
        {
            command.env_remove(key);
        }
    }
    command
        .env_remove("CARGO_MAKEFLAGS")
        .arg(request.source)
        .arg("-o")
        .arg(request.output)
        .current_dir(root);
    let log = request.output.with_extension("compile.log");
    let status = run(&mut command, &log, Duration::from_secs(240));
    assert!(
        status.success(),
        "constant-assert compile failed: {status:?}; {}",
        log.display()
    );
}

// A deliberately bounded reader of this exact emitted MIR fixture. It does not infer
// a general MIR SSA theorem: the one incoming argument must flow to the bounds compare,
// with the sole assignment to that argument occurring textually after the assert in bb0/bb1.
fn require_causal_mir(dir: &Path) -> String {
    let paths: Vec<_> = std::fs::read_dir(dir)
        .expect("read MIR directory")
        .map(|entry| entry.unwrap().path())
        .filter(|path| {
            path.file_name()
                .unwrap()
                .to_string_lossy()
                .contains("runtime-optimized.after.mir")
        })
        .collect();
    assert_eq!(
        paths.len(),
        1,
        "exact one optimized rebinding_bounds MIR required: {paths:?}"
    );
    let text = std::fs::read_to_string(&paths[0]).expect("read causal MIR");
    assert!(
        text.contains("fn rebinding_bounds(_1: usize) -> u64"),
        "unexpected argument identity: {text}"
    );
    let lines: Vec<_> = text.lines().map(str::trim).collect();
    let writes: Vec<_> = lines
        .iter()
        .enumerate()
        .filter(|(_, line)| line.starts_with("_1 = "))
        .collect();
    assert_eq!(
        writes.len(),
        1,
        "runtime argument must have one later assignment: {text}"
    );
    assert_eq!(
        *writes[0].1, "_1 = const 0_usize;",
        "causal later zero write missing: {text}"
    );
    let (assert_at, assert_line) = lines
        .iter()
        .enumerate()
        .find(|(_, line)| line.starts_with("assert(") && line.contains("index out of bounds"))
        .expect("bounds Assert must remain in optimized MIR");
    assert!(
        assert_at < writes[0].0,
        "argument overwrite must be after the bounds Assert: {text}"
    );
    let mut defs: HashMap<&str, &str> = HashMap::new();
    for line in &lines {
        if let Some((lhs, rhs)) = line.strip_suffix(';').unwrap_or(line).split_once(" = ") {
            if lhs.starts_with('_') && lhs[1..].chars().all(|ch| ch.is_ascii_digit()) {
                assert!(
                    defs.insert(lhs, rhs).is_none(),
                    "fixture must keep single bare definitions: {lhs}"
                );
            }
        }
    }
    fn resolve<'a>(operand: &'a str, defs: &HashMap<&'a str, &'a str>, depth: u8) -> &'a str {
        assert!(depth < 8, "fixture operand trace exceeded bound");
        let operand = operand.trim();
        if let Some(local) = operand
            .strip_prefix("copy ")
            .or_else(|| operand.strip_prefix("move "))
        {
            if local == "_1" {
                return local;
            }
            resolve(
                defs.get(local).expect("one operand definition required"),
                defs,
                depth + 1,
            )
        } else {
            operand
        }
    }
    let condition = assert_line
        .strip_prefix("assert(")
        .unwrap()
        .split(',')
        .next()
        .unwrap();
    let local = condition
        .strip_prefix("move ")
        .or_else(|| condition.strip_prefix("copy "))
        .expect("fixture bounds condition must be a bare local");
    let compare = defs.get(local).expect("bounds compare definition");
    let operands = compare
        .strip_prefix("Lt(")
        .and_then(|s| s.strip_suffix(')'))
        .expect("bounds condition must use unsigned Lt");
    let (index, len) = operands.split_once(',').expect("two bounds operands");
    assert_eq!(
        resolve(index, &defs, 0),
        "_1",
        "bounds must read the incoming argument"
    );
    assert_eq!(
        resolve(len, &defs, 0),
        "const 2_usize",
        "array extent must stay two"
    );
    text
}

#[test]
fn later_argument_assignment_never_folds_an_earlier_assert() {
    let backend = backend_artifact_support::current_test_backend();
    let backend_before = std::fs::read(&backend).expect("read exact backend");
    let compiler = PathBuf::from(toolchain_support::rustc_driver_command().get_program());
    let compiler_before = std::fs::read(&compiler).expect("read exact compiler");
    let temp = Command::new("mktemp")
        .args(["-d", "-t", "trust-cg-assert-rebound.XXXXXX"])
        .output()
        .expect("create constant-assert directory");
    assert!(temp.status.success());
    let root = PathBuf::from(String::from_utf8(temp.stdout).unwrap().trim());
    eprintln!("constant-assert retained artifacts: {}", root.display());
    let sources = [
        (root.join("provider.rs"), PROVIDER),
        (root.join("callee.rs"), CALLEE),
        (root.join("caller.rs"), CALLER),
        (root.join("constant.rs"), CONSTANT),
    ];
    for (path, source) in &sources {
        std::fs::write(path, source).unwrap();
    }
    let provider = root.join("libassert_rebound_provider.rlib");
    compile(
        &root,
        Compile {
            name: "assert_rebound_provider",
            source: &sources[0].0,
            output: &provider,
            opt: 0,
            backend: None,
            mode: "rlib",
            externs: &[],
            mir: None,
        },
    );
    let mut cells = 0;
    let mut native = 0;
    let mut constant_objects = 0;
    for opt in [0, 2] {
        let mut llvm_mir = None;
        for cg in [false, true] {
            let tag = format!("O{opt}-{}", if cg { "cg" } else { "llvm" });
            let mir = root.join(format!("mir-{tag}"));
            std::fs::create_dir(&mir).unwrap();
            let callee = root.join(format!("libassert_rebound_callee_{tag}.rlib"));
            compile(
                &root,
                Compile {
                    name: "assert_rebound_callee",
                    source: &sources[1].0,
                    output: &callee,
                    opt,
                    backend: cg.then_some(backend.as_path()),
                    mode: "rlib",
                    externs: &[("assert_rebound_provider", provider.as_path())],
                    mir: Some(&mir),
                },
            );
            let causal_mir = require_causal_mir(&mir);
            if cg {
                assert_eq!(
                    Some(&causal_mir),
                    llvm_mir.as_ref(),
                    "paired frontend MIR must match"
                );
            } else {
                llvm_mir = Some(causal_mir);
            }
            let caller = root.join(format!("caller-{tag}"));
            compile(
                &root,
                Compile {
                    name: "assert_rebound_caller",
                    source: &sources[2].0,
                    output: &caller,
                    opt,
                    backend: None,
                    mode: "bin",
                    externs: &[
                        ("assert_rebound_provider", provider.as_path()),
                        ("assert_rebound_callee", callee.as_path()),
                    ],
                    mir: None,
                },
            );
            for (case, index, code, marker) in [
                (
                    "rebound-safe",
                    "1",
                    0,
                    "ASSERT_REBOUND|case=rebound-safe|value=11|hook=0",
                ),
                (
                    "rebound-panic",
                    "2",
                    73,
                    "ASSERT_REBOUND|case=rebound-panic|hook=1|kind=bounds|len=2|index=2",
                ),
                (
                    "dynamic-panic",
                    "2",
                    73,
                    "ASSERT_REBOUND|case=dynamic-panic|hook=1|kind=bounds|len=2|index=2",
                ),
                (
                    "local-constant",
                    "0",
                    0,
                    "ASSERT_REBOUND|case=local-constant|value=18|hook=0",
                ),
            ] {
                let log = root.join(format!("run-{tag}-{case}.log"));
                let status = run(
                    Command::new(&caller).args([case, index]),
                    &log,
                    Duration::from_secs(30),
                );
                assert_eq!(
                    status.code(),
                    Some(code),
                    "{tag}/{case} wrong native verdict; {}",
                    log.display()
                );
                let output = std::fs::read_to_string(&log).unwrap();
                assert_eq!(
                    output
                        .lines()
                        .filter(|line| line.starts_with("ASSERT_REBOUND|"))
                        .collect::<Vec<_>>(),
                    [marker]
                );
                assert!(
                    !output
                        .lines()
                        .any(|line| line.trim_start().starts_with("SKIP"))
                );
                native += 1;
                assert_eq!(std::fs::read(&backend).unwrap(), backend_before);
                assert_eq!(std::fs::read(&compiler).unwrap(), compiler_before);
                for (path, source) in &sources {
                    assert_eq!(std::fs::read_to_string(path).unwrap(), *source);
                }
            }
            let object = root.join(format!("constant-{tag}.o"));
            compile(
                &root,
                Compile {
                    name: "assert_rebound_constant",
                    source: &sources[3].0,
                    output: &object,
                    opt,
                    backend: cg.then_some(backend.as_path()),
                    mode: "object",
                    externs: &[],
                    mir: None,
                },
            );
            // The native bridge emits a CGU-named object for --emit=obj. Bind
            // the one actual object from this cell, including LLVM's exact -o.
            let object_prefix = format!("constant-{tag}");
            let objects: Vec<_> = std::fs::read_dir(&root)
                .unwrap()
                .map(|entry| entry.unwrap().path())
                .filter(|path| {
                    path.file_name()
                        .unwrap()
                        .to_string_lossy()
                        .starts_with(&object_prefix)
                        && path.extension().is_some_and(|extension| extension == "o")
                })
                .collect();
            assert_eq!(objects.len(), 1, "one actual constant object per cell");
            let object = &objects[0];
            assert!(object.is_file() && object.metadata().unwrap().len() > 0);
            let log = root.join(format!("symbols-{tag}.log"));
            assert!(
                run(
                    Command::new("nm").arg("-u").arg(&object),
                    &log,
                    Duration::from_secs(30)
                )
                .success()
            );
            assert!(
                !std::fs::read_to_string(&log)
                    .unwrap()
                    .contains("panic_bounds_check"),
                "immutable local constant must preserve the no-panic-entry object control: {}",
                log.display()
            );
            assert_eq!(std::fs::read(&backend).unwrap(), backend_before);
            assert_eq!(std::fs::read(&compiler).unwrap(), compiler_before);
            for (path, source) in &sources {
                assert_eq!(std::fs::read_to_string(path).unwrap(), *source);
            }
            constant_objects += 1;
            cells += 1;
        }
    }
    assert_eq!((cells, native, constant_objects), (4, 16, 4));
    eprintln!(
        "ASSERT_REBOUND_NATIVE cells=4 native_runs=16 panic_hooks=8 safe_returns=8 causal_mir=4 constant_objects=4 opts=0,2 mir_opt=0 provider=LLVM caller=LLVM certs=off"
    );
}
