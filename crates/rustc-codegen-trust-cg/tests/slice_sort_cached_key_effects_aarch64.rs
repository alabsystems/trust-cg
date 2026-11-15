// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Cached-key sorting must preserve its observable key-call bound.
//! This is an ARM64/macOS native differential with certificates OFF, not a
//! source-to-native proof. A named refusal retains an explicit coverage gap.
#![cfg(all(target_os = "macos", target_arch = "aarch64"))]

#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/darwin_native_prerequisites.rs"]
mod darwin_native;
#[path = "support/positive_evidence.rs"]
mod positive_evidence;
#[path = "support/toolchain.rs"]
mod toolchain_support;

use std::path::Path;
use std::process::Command;
use std::time::{Duration, SystemTime, UNIX_EPOCH};

// The callback closure is a ZST, yet its actual out-of-line callee mutates a
// static. Its key is still exactly the element value, so the input is valid
// and its reverse order forces every insertion-sort inner shift. The old
// uncached interception called it 3 + (1 + 2 + 3) = 9 times. Std caches four
// keys before sorting; the LLVM oracle below independently must return 4.
const SOURCE: &str = r#"
static mut CALLS: u32 = 0;
#[inline(never)]
fn key(x: &u32) -> u32 {
    unsafe { CALLS = CALLS.wrapping_add(1); }
    *x
}
fn main() {
    let mut values = vec![std::hint::black_box(4u32), 3, 2, 1];
    values.sort_by_cached_key(|x| key(x));
    std::process::exit(unsafe { CALLS } as i32);
}
"#;

enum Outcome {
    Exit(i32),
    Refused(String),
}

fn compile_and_run(dir: &Path, backend: Option<&Path>, opt: u32) -> Outcome {
    let label = if backend.is_some() { "tcg" } else { "llvm" };
    let cell = dir.join(format!("{label}-O{opt}"));
    std::fs::create_dir(&cell).expect("fresh cell directory");
    let source = cell.join("main.rs");
    std::fs::write(&source, SOURCE).expect("write bounded counter fixture");
    let executable = cell.join("counter");
    let mut command = toolchain_support::rustc_command_with_edition("2021");
    command
        .args([
            "--target",
            "aarch64-apple-darwin",
            "-Cpanic=abort",
            "-Ccodegen-units=1",
        ])
        .arg(format!("-Copt-level={opt}"))
        .arg("-o")
        .arg(&executable)
        .arg(&source);
    if let Some(backend) = backend {
        let mut argument = std::ffi::OsString::from("-Zcodegen-backend=");
        argument.push(backend);
        command
            .arg(argument)
            .arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]));
    }
    let built = darwin_native::run_with_deadline(&mut command, Duration::from_secs(180))
        .unwrap_or_else(|output| {
            panic!(
                "{label} O{opt}: compiler deadline, not a refusal: {}",
                String::from_utf8_lossy(&output.stderr),
            )
        });
    std::fs::write(cell.join("compile.stderr"), &built.stderr).expect("retain compile diagnostic");
    std::fs::write(cell.join("compile.stdout"), &built.stdout).expect("retain compile output");
    if !built.status.success() {
        let stderr = String::from_utf8_lossy(&built.stderr);
        assert!(backend.is_some(), "LLVM O{opt} failed: {stderr}");
        let tag = stderr
            .split('[')
            .skip(1)
            .find_map(|rest| {
                let tag = rest.split(']').next()?;
                tag.starts_with("TCG-").then(|| tag.to_owned())
            })
            .unwrap_or_default();
        assert!(
            !tag.is_empty(),
            "CG O{opt}: failure without named refusal: {stderr}"
        );
        return Outcome::Refused(tag);
    }
    let output =
        darwin_native::run_with_deadline(&mut Command::new(&executable), Duration::from_secs(10))
            .unwrap_or_else(|_| panic!("{label} O{opt}: native deadline, not a refusal"));
    Outcome::Exit(
        output
            .status
            .code()
            .expect("counter must exit normally, not by signal"),
    )
}

#[test]
fn cached_key_counter_calls_once_per_element_or_refuses_by_name() {
    darwin_native::require("slice_sort_cached_key_effects_aarch64", &[]);
    let backend = backend_artifact_support::current_test_backend();
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("clock after epoch")
        .as_nanos();
    let dir = std::env::temp_dir().join(format!(
        "tcg_cached_key_counter_{}_{nonce}",
        std::process::id(),
    ));
    std::fs::create_dir(&dir).expect("fresh retained fixture directory");
    let (mut matched, mut refused) = (0, 0);
    for opt in 0..=3 {
        let Outcome::Exit(oracle) = compile_and_run(&dir, None, opt) else {
            panic!("LLVM must compile and run the counter");
        };
        assert_eq!(
            oracle, 4,
            "LLVM O{opt}: four cached-key calls are the actual oracle"
        );
        match compile_and_run(&dir, Some(&backend), opt) {
            Outcome::Exit(actual) => {
                assert_eq!(
                    actual, oracle,
                    "CG O{opt}: callback count changed; the old insertion path produced nine calls"
                );
                matched += 1;
            }
            Outcome::Refused(tag) => {
                eprintln!("CACHED_KEY_COUNTER O{opt} refused=[{tag}]");
                refused += 1;
            }
        }
    }
    assert_eq!(matched + refused, 4);
    eprintln!(
        "CACHED_KEY_COUNTER cells=4 matched={matched} refused={refused} certs=off artifacts={}",
        dir.display()
    );
    positive_evidence::record(
        if matched == 0 {
            positive_evidence::Evidence::ExpectedRefusal
        } else {
            positive_evidence::Evidence::NativeRun
        },
        positive_evidence::Certs::Off,
    );
}
