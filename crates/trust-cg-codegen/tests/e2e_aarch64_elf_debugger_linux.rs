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
//! A second leg links a WHOLE-MODULE object (the leaf, then the fixture)
//! emitted through `compile_module_emission_with_debug_provenance` and drives
//! gdb over it at O0-O3. gdb first reads the location lists statically
//! (`info scope`): `x` must be described from the fixture's entry and
//! `reg_probe` must have a range. The live session then checks exactly these
//! values: the parameter `x` reads the harness argument at the fixture's
//! first instruction; at the body-line stop the constant local reads its
//! value, and the spilled probe reads its source value when gdb's static
//! ranges cover the stop and `<optimized out>` when they do not (at O0 a
//! range must cover it); the register-held probe reads its source value at
//! the start of its first described range only. The backtrace, the body-line
//! stop and the step are checked as above. From O1 the accumulator's frame
//! slot is described (gdb's own range covers the stop) although the
//! optimizer removed its stores, so gdb reads a stale value and only its
//! name is checked there (on both legs). No other probe or address is
//! checked against gdb's ranges.
//!
//! A missing `cc` or debugger FAILS: this target is Linux-floor evidence and
//! a skipped leg cannot establish it (the module leg requires gdb). The ELF
//! object-level DWARF and CFI checks that do not need a Linux host are
//! `aarch64_elf_dwarf` and `aarch64_elf_cfi_differential`. None of this is a
//! proof that a described location holds its source value on every path.

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
    RETURN_LINE, TAIL_CONST, acc_before_body_line, expected_result, lir_fixture, lir_fixture_leaf,
    write_fixture_source,
};
use trust_cg_codegen::pipeline::{
    DispatchVerifyMode, ModuleSymbolLinkage, OptLevel, Pipeline, PipelineConfig,
};

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

fn debug_pipeline(level: OptLevel) -> Pipeline {
    Pipeline::new(PipelineConfig {
        opt_level: level,
        emit_debug: true,
        verify_dispatch: DispatchVerifyMode::Off,
        ..PipelineConfig::for_target(TRIPLE)
    })
}

fn build(dir: &Path, level: OptLevel) -> PathBuf {
    let object = debug_pipeline(level)
        .compile_function(&lir_fixture())
        .unwrap_or_else(|e| panic!("{level:?}: compile: {e}"));
    let obj = dir.join(format!("fixture_{level:?}.o"));
    fs::write(&obj, object).expect("write object");
    link(dir, level, &obj, &format!("fixture_{level:?}"))
}

/// The leaf and the fixture prepared with `-g` and emitted as ONE module
/// object through `compile_module_emission_with_debug_provenance`, leaf
/// first: every fixture parameter and variable range was moved past the
/// leaf, onto the fixture's text offset.
fn build_module(dir: &Path, level: OptLevel) -> PathBuf {
    let pipeline = debug_pipeline(level);
    let mut functions = Vec::new();
    let mut metrics = Vec::new();
    for lir in [lir_fixture_leaf(), lir_fixture()] {
        let (func, prepared) = pipeline
            .prepare_function_with_metrics(&lir, None)
            .unwrap_or_else(|e| panic!("{level:?}: prepare {}: {e}", lir.name));
        functions.push(func);
        metrics.push(prepared);
    }
    let layouts: Vec<_> = metrics.iter().map(|m| m.frame_layout.clone()).collect();
    let provenance: Vec<_> = metrics
        .iter()
        .map(|m| m.debug_provenance.as_ref())
        .collect();
    assert!(
        provenance.iter().all(Option::is_some),
        "{level:?}: a -g preparation retains each function's register-debug provenance"
    );
    let emission = pipeline
        .compile_module_emission_with_debug_provenance(
            &functions,
            &[],
            &layouts,
            &ModuleSymbolLinkage::default(),
            &provenance,
        )
        .unwrap_or_else(|e| panic!("{level:?}: module emission: {e}"))
        .into_emission();
    let fixture = emission
        .text_extents
        .iter()
        .find(|extent| extent.name == FIXTURE)
        .expect("fixture text extent");
    assert!(
        fixture.offset > 0,
        "{level:?}: the fixture must sit past the leaf: {fixture:?}"
    );
    let obj = dir.join(format!("module_{level:?}.o"));
    fs::write(&obj, emission.object).expect("write module object");
    link(dir, level, &obj, &format!("module_{level:?}"))
}

fn link(dir: &Path, level: OptLevel, obj: &Path, name: &str) -> PathBuf {
    let harness = dir.join("harness.c");
    fs::write(&harness, HARNESS).expect("write harness");
    let exe = dir.join(name);
    let cc = on_path(&["cc", "gcc", "clang"]).expect("a C compiler (cc) is required");
    let mut link = Command::new(cc);
    link.current_dir(dir)
        .args(["-g", "-O0", "-o"])
        .arg(&exe)
        .arg(&harness)
        .arg(obj);
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
    run_debugger_script(
        dir,
        exe,
        &[
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
        ],
        &[
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
        ],
    )
}

fn run_debugger_script(
    dir: &Path,
    exe: &Path,
    gdb_lines: &[String],
    lldb_lines: &[String],
) -> String {
    match debugger() {
        Debugger::Gdb(gdb) => run_gdb_with(&gdb, dir, exe, gdb_lines),
        Debugger::Lldb(lldb) => {
            let mut command = Command::new(lldb);
            command.arg("--batch");
            for line in lldb_lines {
                command.arg("-o").arg(line);
            }
            command.arg("--").arg(exe);
            capture(dir, command)
        }
    }
}

fn run_gdb_with(gdb: &Path, dir: &Path, exe: &Path, lines: &[String]) -> String {
    let mut command = Command::new(gdb);
    command.args(["-nx", "-batch"]);
    for line in lines {
        command.arg("-ex").arg(line);
    }
    command.arg(exe);
    capture(dir, command)
}

fn capture(dir: &Path, mut command: Command) -> String {
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

/// The module leg reads location ranges through gdb's `info scope`, so it
/// needs gdb itself; a missing gdb FAILS it like a missing debugger fails
/// the single-function leg.
fn module_gdb() -> PathBuf {
    on_path(&["gdb"]).expect("gdb is required for the module-object debugger leg")
}

/// gdb's static reading (no process) of the module executable's DWARF for
/// the fixture: its link-time address and each symbol's location-list
/// ranges, `[start, end)` link-time addresses.
#[derive(Debug)]
struct StaticScope {
    function: u64,
    ranges: std::collections::BTreeMap<String, Vec<(u64, u64)>>,
    transcript: String,
}

fn hex_field(text: &str) -> Option<u64> {
    let digits = text.trim().trim_start_matches("0x");
    let digits: String = digits.chars().take_while(char::is_ascii_hexdigit).collect();
    u64::from_str_radix(&digits, 16).ok()
}

fn static_scope(gdb: &Path, dir: &Path, exe: &Path) -> StaticScope {
    let transcript = run_gdb_with(
        gdb,
        dir,
        exe,
        &[
            format!("info address {FIXTURE}"),
            format!("info scope *{FIXTURE}"),
        ],
    );
    // `Symbol "elf_debug_fixture" is a function at address 0x7a8.`
    let function = transcript
        .lines()
        .find_map(|row| {
            row.strip_prefix(&format!("Symbol \"{FIXTURE}\" is a function at address "))
                .and_then(hex_field)
        })
        .unwrap_or_else(|| panic!("no static address for {FIXTURE}:\n{transcript}"));
    let mut ranges: std::collections::BTreeMap<String, Vec<(u64, u64)>> =
        std::collections::BTreeMap::new();
    let mut current = None;
    for row in transcript.lines() {
        // `Symbol spill_probe is multi-location:` then `  Range 0xA-0xB: ...`
        if let Some(rest) = row.strip_prefix("Symbol ") {
            current = rest.split_whitespace().next().map(str::to_string);
            if let Some(name) = &current {
                ranges.entry(name.clone()).or_default();
            }
        } else if let Some(rest) = row.trim_start().strip_prefix("Range ")
            && let Some(name) = &current
            && let Some((start, end)) = rest.split_once('-')
            && let (Some(start), Some(end)) = (hex_field(start), hex_field(end))
        {
            ranges.entry(name.clone()).or_default().push((start, end));
        }
    }
    StaticScope {
        function,
        ranges,
        transcript,
    }
}

impl StaticScope {
    fn ranges(&self, name: &str) -> &[(u64, u64)] {
        self.ranges.get(name).map_or(&[], Vec::as_slice)
    }

    fn covers(&self, name: &str, address: u64) -> bool {
        self.ranges(name)
            .iter()
            .any(|(start, end)| (*start..*end).contains(&address))
    }
}

/// Prefix of every value the module leg's gdb session reads.
const PROBE: &str = "trust-cg-probe";

/// The module leg's live session: it stops at the fixture's first
/// instruction (before any prologue, where the parameter is in X0) and reads
/// the parameter, backtraces from the barrier, reads the locals at the
/// body-line stop, steps, then stops at `register_probe_offset` (the start of
/// the register-held probe's first described range) and reads it.
fn run_module_debugger(gdb: &Path, dir: &Path, exe: &Path, register_probe_offset: u64) -> String {
    // `output` prints `<optimized out>` where no range covers the PC, where
    // `printf` would abort the line.
    let probe = |name: &str| {
        [
            format!("echo {PROBE} {name}="),
            format!("output {name}"),
            "echo \\n".to_string(),
        ]
    };
    let mut lines = vec![
        "set pagination off".to_string(),
        "set confirm off".to_string(),
        format!("break *{FIXTURE}"),
        format!("break {BARRIER}"),
        format!("break {FIXTURE_FILE}:{STOP_LINE}"),
        format!("break *{FIXTURE}+{register_probe_offset}"),
        "run".to_string(),
    ];
    lines.extend(probe("x"));
    // gdb's reading of the relocated location lists, for the record.
    for name in ["x", "acc", "spill_probe", "reg_probe"] {
        lines.push(format!("info address {name}"));
    }
    lines.extend(["continue", "bt", "continue", "info line *$pc"].map(String::from));
    for name in ["tail_const", "acc", "spill_probe"] {
        lines.extend(probe(name));
    }
    lines.extend(["next", "info line *$pc", "continue"].map(String::from));
    lines.extend(probe("reg_probe"));
    lines.extend(["delete", "continue"].map(String::from));
    run_gdb_with(gdb, dir, exe, &lines)
}

/// The value the module leg's gdb session printed for `name`.
fn read_value(text: &str, name: &str) -> Option<String> {
    let prefix = format!("{PROBE} {name}=");
    text.lines().find_map(|row| {
        row.strip_prefix(&prefix)
            .map(|value| value.trim().to_string())
    })
}

/// Link-time address of the body-line breakpoint, from gdb's
/// `Breakpoint N at 0x910: file ./elf_debug_fixture.rs, line 22.`
fn stop_line_address(text: &str) -> u64 {
    let suffix = format!("{FIXTURE_FILE}, line {STOP_LINE}.");
    text.lines()
        .find(|row| row.starts_with("Breakpoint ") && row.ends_with(&suffix))
        .and_then(|row| row.split(" at ").nth(1))
        .and_then(hex_field)
        .unwrap_or_else(|| panic!("no body-line breakpoint address:\n{text}"))
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

/// The same correspondence through a WHOLE-MODULE object whose DWARF
/// describes parameters and variables (`compile_module_emission_with_debug_provenance`),
/// with the fixture placed after the leaf so every range gdb reads was moved
/// onto a non-zero text offset. gdb first reads the executable's location
/// lists statically (`info scope`). The live session then checks: `x` at the
/// fixture's first instruction; at the body-line stop, `tail_const`,
/// `spill_probe` (its source value if a static range covers the stop,
/// `<optimized out>` if none does, and at O0 a range must cover it) and
/// `acc` (its value at O0; from O1 only its name, because its described frame
/// slot is stale although gdb's range covers the stop); and `reg_probe` at
/// the start of its first range only. It does not check a probe at every
/// address a range claims, nor unavailability outside the ranges except for
/// `spill_probe` at that one stop.
#[test]
fn debugger_reads_parameters_and_locals_from_module_objects() {
    let gdb = module_gdb();
    let dir = scratch("module");
    write_fixture_source(&dir);
    for level in LEVELS {
        let context = format!("module {level:?}");
        let exe = build_module(&dir, level);

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

        let scope = static_scope(&gdb, &dir, &exe);
        let scope_text = &scope.transcript;
        // The parameter is described in X0 from the fixture's first
        // instruction, which the module placed past the leaf.
        assert!(
            scope.ranges("x").first().map(|range| range.0) == Some(scope.function),
            "{context}: `x` must be described from the fixture's entry:\n{scope_text}"
        );
        let register_probe = scope
            .ranges("reg_probe")
            .first()
            .copied()
            .unwrap_or_else(|| panic!("{context}: `reg_probe` has no range:\n{scope_text}"));
        assert!(
            scope_text.contains("a variable in $x"),
            "{context}: expected register locations:\n{scope_text}"
        );

        let text = run_module_debugger(&gdb, &dir, &exe, register_probe.0 - scope.function);

        // The parameter, read at the fixture's first instruction.
        assert_eq!(
            read_value(&text, "x"),
            Some(HARNESS_ARG.to_string()),
            "{context}: parameter `x` at entry:\n{text}"
        );

        // Unwinding from the C callee through the module's trust-cg frame.
        let frame1 = text
            .lines()
            .find(|row| row.starts_with("#1") && row.contains(FIXTURE))
            .unwrap_or_else(|| panic!("{context}: no trust-cg caller frame:\n{text}"));
        assert!(
            frame1.contains(&format!("{FIXTURE_FILE}:{BARRIER_LINE}")),
            "{context}: the caller frame must name the call line {BARRIER_LINE}: {frame1}"
        );
        assert!(
            text.lines()
                .any(|row| row.starts_with("#2") && row.contains("main")),
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

        // The locals at the body-line stop.
        let stop = stop_line_address(&text);
        assert_eq!(
            read_value(&text, "tail_const"),
            Some(TAIL_CONST.to_string()),
            "{context}: tail_const:\n{text}"
        );
        // The spilled probe holds its value wherever a range covers the stop
        // and is unavailable elsewhere; at O0 its spill slot is described
        // from the store onward, so a range must cover the stop.
        let spill_probe = HARNESS_ARG.wrapping_add(4096).to_string();
        let expected_spill = if scope.covers("spill_probe", stop) {
            spill_probe.as_str()
        } else {
            "<optimized out>"
        };
        assert!(
            level != OptLevel::O0 || scope.covers("spill_probe", stop),
            "{context}: at O0 a spill-slot range must cover {stop:#x}:\n{scope_text}"
        );
        assert_eq!(
            read_value(&text, "spill_probe").as_deref(),
            Some(expected_spill),
            "{context}: spill_probe at {stop:#x}:\n{scope_text}\n{text}"
        );
        // The stack accumulator holds the value the preceding lines stored at
        // O0. From O1 the optimizer removes its stores while the frame slot
        // stays described, so gdb reads a stale slot there: only the name is
        // checked, as on the single-function leg.
        if level == OptLevel::O0 {
            let acc = acc_before_body_line(HARNESS_ARG, STOP_K);
            assert_eq!(
                read_value(&text, "acc"),
                Some(acc.to_string()),
                "{context}: acc before line {STOP_LINE}:\n{text}"
            );
        } else {
            assert!(
                read_value(&text, "acc").is_some() && !text.contains("No symbol \"acc\""),
                "{context}: acc must be named:\n{text}"
            );
        }

        // The register-held probe at the start of its first described range.
        let reg_probe = acc_before_body_line(HARNESS_ARG, BODY_LINES).wrapping_add(TAIL_CONST);
        assert_eq!(
            read_value(&text, "reg_probe"),
            Some(reg_probe.to_string()),
            "{context}: reg_probe at {:#x}:\n{scope_text}\n{text}",
            register_probe.0
        );
        assert!(
            text.contains("exited normally"),
            "{context}: the debugged program must exit normally:\n{text}"
        );
    }
    let _ = fs::remove_dir_all(dir);
}
