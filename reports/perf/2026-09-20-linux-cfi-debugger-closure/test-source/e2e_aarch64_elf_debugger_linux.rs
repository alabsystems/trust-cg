// trust-cg-codegen/tests/e2e_aarch64_elf_debugger_linux.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Linux AArch64 debugger/source correspondence through trust-cg frames.
//!
//! The shared DWARF fixture is compiled with `-g` (`emit_debug`) for
//! `aarch64-unknown-linux-gnu` at O0-O3, linked with the host `cc` against a
//! C harness, executed natively, and then driven by the host debugger (gdb,
//! or lldb when gdb is absent) in batch mode:
//!
//! * a breakpoint in the C callee `spill_barrier` must backtrace THROUGH the
//!   trust-cg frame (its `.eh_frame` FDE) to `main`, naming the fixture's
//!   call line;
//! * a `file:line` breakpoint on a body line must stop there, map the PC back
//!   to that line, and read the constant local; at O0 the stack-resident
//!   accumulator must hold the value the preceding lines computed;
//! * stepping over the line must land on the next body line (O0) or another
//!   fixture body line (O1-O3);
//! * the program must exit normally with the harness-checked result.
//!
//! A missing `cc` or debugger FAILS: this target is Linux-floor evidence and
//! a skipped leg cannot establish it. The ELF object-level DWARF and CFI
//! checks that do not need a Linux host are `aarch64_elf_dwarf` and
//! `aarch64_elf_cfi_differential`.

#![cfg(all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"))]

#[path = "common/elf_debug_fixture.rs"]
mod elf_debug_fixture;
#[path = "common/rosetta.rs"]
mod process;

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::Duration;

use elf_debug_fixture::{
    BARRIER, BARRIER_LINE, BODY_LINES, FIRST_BODY_LINE, FIXTURE, FIXTURE_FILE, HARNESS_ARG,
    RETURN_LINE, TAIL_CONST, acc_before_body_line, expected_result, lir_fixture,
    write_fixture_source,
};
use trust_cg_codegen::pipeline::{DispatchVerifyMode, OptLevel, Pipeline, PipelineConfig};

const TRIPLE: &str = "aarch64-unknown-linux-gnu";
const LEVELS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];
/// The body line the debugger stops on (third accumulator update).
const STOP_K: u32 = 2;
const STOP_LINE: u32 = FIRST_BODY_LINE + STOP_K;
// The O0 step-over expects the body line after the stop.
const _: () = assert!(
    BODY_LINES > STOP_K + 1,
    "fixture must have a line after the stop"
);
const DEBUGGER_TIMEOUT: Duration = Duration::from_secs(120);

fn scratch(tag: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!(
        "trust_cg_elf_debugger_{tag}_{}",
        std::process::id()
    ));
    fs::create_dir_all(&dir).expect("create scratch dir");
    dir
}

fn on_path(names: &[&str]) -> Option<PathBuf> {
    let path = std::env::var_os("PATH")?;
    std::env::split_paths(&path).find_map(|dir| {
        names
            .iter()
            .map(|name| dir.join(name))
            .find(|candidate| candidate.is_file())
    })
}

const HARNESS: &str = r#"
#include <stdio.h>
extern long long elf_debug_fixture(long long);
__attribute__((noinline)) long long spill_barrier(long long v) {
    __asm__ __volatile__("" ::: "memory");
    return v + 1;
}
int main(void) {
    long long r = elf_debug_fixture(7);
    printf("result=%lld\n", r);
    return 0;
}
"#;

fn build(dir: &Path, level: OptLevel) -> PathBuf {
    let object = Pipeline::new(PipelineConfig {
        opt_level: level,
        emit_debug: true,
        verify_dispatch: DispatchVerifyMode::Off,
        ..PipelineConfig::for_target(TRIPLE)
    })
    .compile_function(&lir_fixture())
    .unwrap_or_else(|e| panic!("{level:?}: compile: {e}"));
    let obj = dir.join(format!("fixture_{level:?}.o"));
    fs::write(&obj, object).expect("write object");
    let harness = dir.join("harness.c");
    fs::write(&harness, HARNESS).expect("write harness");
    let exe = dir.join(format!("fixture_{level:?}"));
    let cc = on_path(&["cc", "gcc", "clang"]).expect("a C compiler (cc) is required");
    let mut link = Command::new(cc);
    link.current_dir(dir)
        .args(["-g", "-O0", "-o"])
        .arg(&exe)
        .arg(&harness)
        .arg(&obj);
    let out = process::command_output_with_timeout(&mut link, process::codegen_link_timeout())
        .expect("run cc");
    assert!(
        !out.timed_out && out.output.status.success(),
        "{level:?}: link failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&out.output.stdout),
        String::from_utf8_lossy(&out.output.stderr)
    );
    exe
}

enum Debugger {
    Gdb(PathBuf),
    Lldb(PathBuf),
}

fn debugger() -> Debugger {
    if let Some(gdb) = on_path(&["gdb"]) {
        return Debugger::Gdb(gdb);
    }
    let lldb_names: Vec<String> = std::iter::once("lldb".to_string())
        .chain((14..=22).rev().map(|major| format!("lldb-{major}")))
        .collect();
    let names: Vec<&str> = lldb_names.iter().map(String::as_str).collect();
    on_path(&names)
        .map(Debugger::Lldb)
        .expect("gdb or lldb is required for the Linux debugger correspondence floor")
}

fn run_debugger(dir: &Path, exe: &Path) -> String {
    let mut command = match debugger() {
        Debugger::Gdb(gdb) => {
            let mut command = Command::new(gdb);
            command.args(["-nx", "-batch"]);
            for line in [
                "set pagination off".to_string(),
                "set confirm off".to_string(),
                format!("break {BARRIER}"),
                format!("break {FIXTURE_FILE}:{STOP_LINE}"),
                "run".to_string(),
                "bt".to_string(),
                "continue".to_string(),
                "info line *$pc".to_string(),
                "print acc".to_string(),
                "print tail_const".to_string(),
                "next".to_string(),
                "info line *$pc".to_string(),
                "delete".to_string(),
                "continue".to_string(),
            ] {
                command.arg("-ex").arg(line);
            }
            command.arg(exe);
            command
        }
        Debugger::Lldb(lldb) => {
            let mut command = Command::new(lldb);
            command.arg("--batch");
            for line in [
                format!("breakpoint set -n {BARRIER}"),
                format!("breakpoint set -f {FIXTURE_FILE} -l {STOP_LINE}"),
                "process launch".to_string(),
                "thread backtrace".to_string(),
                "process continue".to_string(),
                "frame info".to_string(),
                "frame variable acc tail_const".to_string(),
                "thread step-over".to_string(),
                "frame info".to_string(),
                "breakpoint delete --force".to_string(),
                "process continue".to_string(),
            ] {
                command.arg("-o").arg(line);
            }
            command.arg("--").arg(exe);
            command
        }
    };
    command.current_dir(dir);
    let out =
        process::command_output_with_timeout(&mut command, DEBUGGER_TIMEOUT).expect("run debugger");
    let text = format!(
        "{}\n{}",
        String::from_utf8_lossy(&out.output.stdout),
        String::from_utf8_lossy(&out.output.stderr)
    );
    assert!(!out.timed_out, "debugger timed out:\n{text}");
    text
}

/// Fixture source lines the debugger reports for the current PC, in order.
fn reported_lines(text: &str) -> Vec<u32> {
    let needle = format!("{FIXTURE_FILE}:");
    let mut lines = Vec::new();
    for row in text.lines() {
        // gdb: `Line 22 of "./elf_debug_fixture.rs" starts at ...`
        if let Some(rest) = row.strip_prefix("Line ")
            && row.contains(FIXTURE_FILE)
            && let Some(n) = rest.split_whitespace().next().and_then(|n| n.parse().ok())
        {
            lines.push(n);
            continue;
        }
        // lldb: `frame #0: ... at elf_debug_fixture.rs:22:13`
        if row.trim_start().starts_with("frame #0")
            && let Some(at) = row.find(&needle)
        {
            let digits: String = row[at + needle.len()..]
                .chars()
                .take_while(char::is_ascii_digit)
                .collect();
            if let Ok(n) = digits.parse() {
                lines.push(n);
            }
        }
    }
    // lldb reports the same frame on the stop and on `frame info`.
    lines.dedup();
    lines
}

#[test]
fn debugger_backtraces_breaks_steps_and_reads_locals_through_cg_frames() {
    let dir = scratch("correspondence");
    write_fixture_source(&dir);
    for level in LEVELS {
        let context = format!("{level:?}");
        let exe = build(&dir, level);

        // Native execution first: the object the debugger reads computes.
        let run = process::run_executable_with_timeout(&exe, process::codegen_run_timeout())
            .unwrap_or_else(|e| panic!("{context}: run: {e}"));
        let stdout = String::from_utf8_lossy(&run.output.stdout).into_owned();
        assert!(
            run.output.status.success(),
            "{context}: exit {:?}\n{stdout}",
            run.output.status
        );
        assert_eq!(
            stdout.trim(),
            format!("result={}", expected_result(HARNESS_ARG)),
            "{context}: native result"
        );

        let text = run_debugger(&dir, &exe);

        // Unwinding from the C callee through the trust-cg frame to main.
        let frame1 = text
            .lines()
            .find(|row| {
                (row.starts_with("#1") || row.trim_start().starts_with("frame #1"))
                    && row.contains(FIXTURE)
            })
            .unwrap_or_else(|| panic!("{context}: no trust-cg caller frame:\n{text}"));
        assert!(
            frame1.contains(&format!("{FIXTURE_FILE}:{BARRIER_LINE}")),
            "{context}: the caller frame must name the call line {BARRIER_LINE}: {frame1}"
        );
        assert!(
            text.lines().any(|row| (row.starts_with("#2")
                || row.trim_start().starts_with("frame #2"))
                && row.contains("main")),
            "{context}: the backtrace must reach main through the trust-cg frame:\n{text}"
        );

        // Break on the body line, map the PC back, then step.
        let lines = reported_lines(&text);
        assert!(
            lines.len() >= 2,
            "{context}: expected the stop line and the stepped line:\n{text}"
        );
        assert_eq!(lines[0], STOP_LINE, "{context}: stop line:\n{text}");
        if level == OptLevel::O0 {
            assert_eq!(
                lines[1],
                STOP_LINE + 1,
                "{context}: step-over line:\n{text}"
            );
        } else {
            assert!(
                (FIRST_BODY_LINE..=RETURN_LINE).contains(&lines[1]),
                "{context}: stepped to {} outside the body:\n{text}",
                lines[1]
            );
        }

        // The constant local is available everywhere; the stack accumulator
        // holds the value the preceding lines stored at O0 (optimized levels
        // may keep it in registers and leave the slot stale).
        assert!(
            text.contains(&format!("= {TAIL_CONST}")),
            "{context}: tail_const must read {TAIL_CONST}:\n{text}"
        );
        if level == OptLevel::O0 {
            let acc = acc_before_body_line(HARNESS_ARG, STOP_K);
            assert!(
                text.contains(&format!("= {acc}")),
                "{context}: acc must read {acc} before line {STOP_LINE}:\n{text}"
            );
        } else {
            assert!(
                !text.contains("No symbol \"acc\"") && !text.contains("no variable named 'acc'"),
                "{context}: acc must be named:\n{text}"
            );
        }
        assert!(
            text.contains("exited normally") || text.contains("exited with status = 0"),
            "{context}: the debugged program must exit normally:\n{text}"
        );
    }
    let _ = fs::remove_dir_all(dir);
}
