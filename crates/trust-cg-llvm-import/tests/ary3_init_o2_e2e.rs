#![cfg(feature = "driver")]

// trust-cg-llvm-import / tests / ary3_init_o2_e2e.rs
//
// Deterministic imported-O0 ary3 initialization coverage for #922 and
// TRUSTCG-18. Both fixtures are `for (i = start; i < end; i++) a[i] = i + 1`
// loops that trust-cg-opt's i32 induction-store rewrite turns into a NEON ST1
// main loop in front of the scalar loop. The linked programs check every
// written element and every untouched sentinel. The second fixture's loops
// start at nonzero, negative and i32::MAX-adjacent indices, which the rewrite
// used to store at a[0] and guard with a wrapping i32 `index + 3`. Each
// fixture compiles for this host's explicit triple (ELF on AArch64 Linux GNU,
// Mach-O on AArch64 macOS); `/usr/bin/objdump` (binutils on Linux, LLVM on
// macOS) reads it back and the linked program runs natively.

mod common;

use std::fs;
use std::path::Path;
use std::process::{Command, Stdio};
use std::thread;
use std::time::{Duration, Instant};

use common::{compile_for_host, describe_status, native_host_or_skip, unique_temp_dir};
use trust_cg_codegen::pipeline::OptLevel;

const ARY3_INIT_LL: &str = include_str!("fixtures/ary3_init_clang_o0.ll");
const ARY3_INIT_OFFSET_LL: &str = include_str!("fixtures/ary3_init_offset_clang_o0.ll");

fn run_command_output(mut command: Command, timeout: Duration) -> std::process::Output {
    command.stdout(Stdio::piped()).stderr(Stdio::piped());
    let mut child = command.spawn().expect("spawn command");
    let started = Instant::now();
    loop {
        match child.try_wait().expect("poll command") {
            Some(status) => {
                let output = child.wait_with_output().expect("collect command output");
                assert_eq!(
                    output.status, status,
                    "wait status should match poll status"
                );
                return output;
            }
            None if started.elapsed() >= timeout => {
                let _ = child.kill();
                let output = child.wait_with_output().expect("collect killed command");
                panic!(
                    "command timed out after {:?}\nstdout:\n{}\nstderr:\n{}",
                    timeout,
                    String::from_utf8_lossy(&output.stdout),
                    String::from_utf8_lossy(&output.stderr)
                );
            }
            None => thread::sleep(Duration::from_millis(10)),
        }
    }
}

fn disassemble_object(obj_path: &Path) -> String {
    let mut command = Command::new("/usr/bin/objdump");
    command.arg("-d").arg(obj_path);
    let output = run_command_output(command, Duration::from_secs(10));
    assert!(
        output.status.success(),
        "objdump failed with {}\nstdout:\n{}\nstderr:\n{}",
        describe_status(output.status),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8(output.stdout).expect("objdump output should be utf8")
}

fn link_with_cc(obj_path: &Path, bin_path: &Path) {
    let mut command = common::native_c_command();
    command.arg(obj_path).arg("-o").arg(bin_path);
    let output = run_command_output(command, Duration::from_secs(10));
    assert!(
        output.status.success(),
        "cc failed with {}\nstdout:\n{}\nstderr:\n{}",
        describe_status(output.status),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

/// Compile `src` at O2 for this host's triple, require the NEON ST1 main loop
/// and the scalar tail's STR, then link and run it; the fixture's `main` exits
/// 0 only when every element and sentinel is what the scalar loop writes.
fn assert_vectorized_fixture_runs(test: &str, src: &str, module_name: &str, tag: &str) {
    if !native_host_or_skip(test) {
        return;
    }
    if !Path::new("/usr/bin/objdump").exists() {
        eprintln!("SKIP {test}: /usr/bin/objdump is not available to read the object");
        return;
    }

    let dir = unique_temp_dir(tag);
    let obj_path = dir.join(format!("{module_name}.trust-cg.o"));
    let bin_path = dir.join(format!("{module_name}.trust-cg"));
    let object = compile_for_host(src, module_name, OptLevel::O2);
    fs::write(&obj_path, object).expect("write fixture object");

    let disassembly = disassemble_object(&obj_path);
    let lowercase_disassembly = disassembly.to_ascii_lowercase();
    // Both objdumps print a tab before the mnemonic (`\tst1\t{ v0.4s }, ...`),
    // so the object's path in the header cannot satisfy this check.
    assert!(
        lowercase_disassembly.contains("\tst1"),
        "the i32 induction-store loop should contain a NEON ST1 vector store:\n{disassembly}"
    );
    assert!(
        lowercase_disassembly.contains("\tstr\t"),
        "the scalar loop must remain as the tail:\n{disassembly}"
    );

    link_with_cc(&obj_path, &bin_path);
    let command = Command::new(&bin_path);
    let output = run_command_output(command, Duration::from_secs(10));
    assert!(
        output.status.success(),
        "linked {module_name} fixture failed with {}\nstdout:\n{}\nstderr:\n{}\ndisassembly:\n{}",
        describe_status(output.status),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
        disassembly
    );
    assert!(
        output.stdout.is_empty(),
        "fixture should be silent on success, got stdout:\n{}",
        String::from_utf8_lossy(&output.stdout)
    );
}

#[test]
fn ary3_init_imported_o0_o2_vectorizes_and_preserves_tails() {
    assert_vectorized_fixture_runs(
        "ary3_init_imported_o0_o2_vectorizes_and_preserves_tails",
        ARY3_INIT_LL,
        "ary3_init_clang_o0",
        "ary3-init-o2",
    );
}

#[test]
fn ary3_init_offset_imported_o0_o2_vectorizes_from_nonzero_and_edge_entries() {
    assert_vectorized_fixture_runs(
        "ary3_init_offset_imported_o0_o2_vectorizes_from_nonzero_and_edge_entries",
        ARY3_INIT_OFFSET_LL,
        "ary3_init_offset_clang_o0",
        "ary3-init-offset-o2",
    );
}
