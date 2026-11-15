#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// Integration test: a bridge-compiled `print!` / `println!` / `eprint!` /
// `eprintln!` writes through std's own stdout and stderr.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// THE HAZARD. The bridge decodes a `print!`'s `fmt::Arguments` and formats the
// bytes itself. It used to write them with a raw `write(2)` to fd 1/2
// (`__trustcg_write_all`), around std's global `Stdout`, which is ALWAYS a
// `LineWriter`. Whatever std was still holding (a partial line from LLVM code,
// `stdout().write_all`, `write!(stdout().lock(), ..)`, the tail of a
// multi-line `print!`) was overtaken, and bytes the bridge printed escaped an
// `abort()` that discards std's buffer. Measured on f349c8652 (proofs-off lane,
// LLVM caller, bridge library): `print!("a:"); klib::show(5); println!("end")`
// printed "5\na:end\n" where LLVM prints "a:5\nend\n", for every decoded
// placeholder kind (u8..u128, i128, usize, bool, char, const `&str`, two
// arguments), at -O0 and -O3, exit status 0. libtest's output capture was
// bypassed as well, and a failed write exited 0 where std panics.
//
// THE GATE. One library of `#[inline(never)]` printing functions is compiled
// by LLVM (the oracle) and by the bridge, at -O0 and -O3, under panic=abort and
// panic=unwind; one LLVM-compiled driver calls it, a case per process. For
// every case the oracle's stdout, stderr and exit status are asserted against
// the literal expectation first, so no case passes vacuously, and the bridge
// build must then reproduce all three byte for byte. The bridge must compile
// the library: every shape here was compiled before the repair, so a refusal is
// a regression, not a fail-closed outcome. A disagreement means the bridge
// wrote around std again: hand the bytes to std's `_print`/`_eprint`, or refuse
// the shape with [TCG-PRINT-SINK]; never relax these assertions.
//
// HOST-NATIVE: no `--target` is passed. The bridge side passes `no-proof-certs`
// for the reason `fat_thin_cast_differential.rs` gives: with certificates on,
// AArch64 objects stop at `[TCG-PROOF-465]` after lowering and would pin nothing.

use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};
use std::time::{Duration, Instant};

const RUN_TIMEOUT: Duration = Duration::from_secs(30);

/// The library under test. Every function prints through one of the four
/// macros; `mixed` also buffers a partial line through `Stdout::write_all`.
const LIB_SOURCE: &str = r#"use std::io::Write;
#[inline(never)] pub fn show(x: u32) { println!("{}", x); }
#[inline(never)] pub fn show_const() { println!("k"); }
#[inline(never)] pub fn part(x: u32) { print!("{}", x); }
#[inline(never)] pub fn two_lines(x: u32) { print!("x={}\ny=", x); }
#[inline(never)] pub fn mixed(x: u32) { let mut out = std::io::stdout(); let _ = out.write_all(b"a:"); println!("{}", x); }
#[inline(never)] pub fn empty() { print!(""); }
#[inline(never)] pub fn p_u8(x: u8) { println!("{}", x); }
#[inline(never)] pub fn p_i16(x: i16) { println!("{}", x); }
#[inline(never)] pub fn p_i64(x: i64) { println!("{}", x); }
#[inline(never)] pub fn p_u64(x: u64) { println!("{}", x); }
#[inline(never)] pub fn p_i128(x: i128) { println!("{}", x); }
#[inline(never)] pub fn p_u128(x: u128) { println!("{}", x); }
#[inline(never)] pub fn p_usize(x: usize) { println!("{}", x); }
#[inline(never)] pub fn p_bool(x: bool) { println!("{}", x); }
#[inline(never)] pub fn p_char(x: char) { println!("{}", x); }
#[inline(never)] pub fn p_str() { println!("{}", "lit"); }
#[inline(never)] pub fn p_two(a: u32, b: i32) { println!("{} {}", a, b); }
#[inline(never)] pub fn e_show(x: i32) { eprintln!("{}", x); }
#[inline(never)] pub fn e_part(x: i32) { eprint!("{}", x); }
pub struct Guard(pub u32);
impl Drop for Guard { fn drop(&mut self) { println!("drop {}", self.0); } }
#[inline(never)] pub fn guarded(x: u32) { let _g = Guard(x); print!("g{}:", x); }
pub struct ErrGuard(pub u32);
impl Drop for ErrGuard { fn drop(&mut self) { eprintln!("guard {}", self.0); } }
#[inline(never)] pub fn err_guarded(x: u32) { let _g = ErrGuard(x); println!("{}", x); }
"#;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Status {
    Code(i32),
    /// Killed by `SIGABRT` (`process::abort`, a panic under panic=abort).
    Abort,
    /// A panic that reached `main`'s caller: abort under panic=abort, exit
    /// status 101 under panic=unwind.
    Panicked,
    /// Killed by another signal (observed only; never expected).
    Signal(i32),
}

struct Case {
    name: &'static str,
    /// The driver's statements for this case.
    body: &'static str,
    stdout: String,
    stderr: &'static str,
    /// What the panicking frame's cleanup adds to `stderr` under panic=unwind
    /// only; under panic=abort no cleanup runs.
    unwind_stderr: &'static str,
    status: Status,
}

impl Case {
    fn expected_stderr(&self, config: Config) -> String {
        let cleanup = if config.panic == "unwind" {
            self.unwind_stderr
        } else {
            ""
        };
        format!("{}{cleanup}", self.stderr)
    }
}

fn case(name: &'static str, body: &'static str, stdout: &str) -> Case {
    Case {
        name,
        body,
        stdout: stdout.to_owned(),
        stderr: "",
        unwind_stderr: "",
        status: Status::Code(0),
    }
}

fn cases() -> Vec<Case> {
    let mut cases = vec![
        // A partial line std holds when the bridge prints, from each writer.
        case(
            "driver_partial_line",
            r#"print!("a:"); klib::show(bb(5)); println!("end");"#,
            "a:5\nend\n",
        ),
        case(
            "klib_only_partial_line",
            r#"klib::mixed(bb(7)); println!("end");"#,
            "a:7\nend\n",
        ),
        case(
            "const_println",
            r#"print!("a:"); klib::show_const(); println!("end");"#,
            "a:k\nend\n",
        ),
        case(
            "klib_print_no_newline",
            r#"print!("a"); klib::part(bb(5)); println!("end");"#,
            "a5end\n",
        ),
        case(
            "klib_partial_then_driver",
            r#"klib::part(bb(5)); print!("b"); klib::show(bb(6));"#,
            "5b6\n",
        ),
        case(
            "multiline_partial",
            r#"print!("l1\nl2:"); klib::show(bb(5)); println!("end");"#,
            "l1\nl2:5\nend\n",
        ),
        case(
            "klib_trailing_piece",
            r#"klib::two_lines(bb(3)); println!("end");"#,
            "x=3\ny=end\n",
        ),
        case(
            "partial_1000",
            r#"print!("{}", "x".repeat(bb(1000))); klib::show(bb(5)); println!("end");"#,
            &format!("{}5\nend\n", "x".repeat(1000)),
        ),
        case(
            "partial_2000",
            r#"print!("{}", "x".repeat(bb(2000))); klib::show(bb(5)); println!("end");"#,
            &format!("{}5\nend\n", "x".repeat(2000)),
        ),
        case(
            "lock_write_partial",
            r#"{ let mut l = std::io::stdout().lock(); let _ = write!(l, "a:"); } klib::show(bb(5)); println!("end");"#,
            "a:5\nend\n",
        ),
        // Leaving the process: `exit` flushes std's buffer, `abort` discards it.
        Case {
            status: Status::Code(3),
            ..case(
                "exit_flushes",
                r#"print!("a:"); klib::part(bb(5)); std::process::exit(3);"#,
                "a:5",
            )
        },
        Case {
            status: Status::Abort,
            ..case(
                "abort_drops_buffered",
                r#"print!("a:"); klib::part(bb(5)); std::process::abort();"#,
                "",
            )
        },
        // Controls: no partial line is pending when the bridge prints.
        case(
            "control_flush",
            r#"print!("a:"); let _ = std::io::stdout().flush(); klib::show(bb(5)); println!("end");"#,
            "a:5\nend\n",
        ),
        case(
            "control_full_line",
            r#"println!("a:"); klib::show(bb(5)); println!("end");"#,
            "a:\n5\nend\n",
        ),
        case(
            "control_klib_only_lines",
            r#"klib::show(bb(1)); klib::show_const(); klib::show(bb(2));"#,
            "1\nk\n2\n",
        ),
        case(
            "empty_print",
            r#"print!("a:"); klib::empty(); println!("end");"#,
            "a:end\n",
        ),
        // Every placeholder kind the interception decodes.
        case(
            "u8",
            r#"print!("a:"); klib::p_u8(bb(200)); println!("end");"#,
            "a:200\nend\n",
        ),
        case(
            "i16",
            r#"print!("a:"); klib::p_i16(bb(-300)); println!("end");"#,
            "a:-300\nend\n",
        ),
        case(
            "i64",
            r#"print!("a:"); klib::p_i64(bb(-9_000_000_000)); println!("end");"#,
            "a:-9000000000\nend\n",
        ),
        case(
            "u64",
            r#"print!("a:"); klib::p_u64(bb(u64::MAX)); println!("end");"#,
            "a:18446744073709551615\nend\n",
        ),
        case(
            "i128",
            r#"print!("a:"); klib::p_i128(bb(i128::MIN)); println!("end");"#,
            "a:-170141183460469231731687303715884105728\nend\n",
        ),
        case(
            "u128",
            r#"print!("a:"); klib::p_u128(bb(u128::MAX)); println!("end");"#,
            "a:340282366920938463463374607431768211455\nend\n",
        ),
        case(
            "usize",
            r#"print!("a:"); klib::p_usize(bb(12345)); println!("end");"#,
            "a:12345\nend\n",
        ),
        case(
            "bool",
            r#"print!("a:"); klib::p_bool(bb(true)); println!("end");"#,
            "a:true\nend\n",
        ),
        case(
            "char",
            r#"print!("a:"); klib::p_char(bb('\u{e9}')); println!("end");"#,
            "a:\u{e9}\nend\n",
        ),
        case(
            "str",
            r#"print!("a:"); klib::p_str(); println!("end");"#,
            "a:lit\nend\n",
        ),
        case(
            "two",
            r#"print!("a:"); klib::p_two(bb(3), bb(-4)); println!("end");"#,
            "a:3 -4\nend\n",
        ),
        // `eprint!` reaches std's stderr, beside a partial stdout line.
        Case {
            stderr: "e:-5\nend\n",
            ..case(
                "eprint_partial",
                r#"eprint!("e:"); klib::e_show(bb(-5)); eprintln!("end");"#,
                "",
            )
        },
        Case {
            stderr: "9|\n",
            ..case("eprint_part", r#"klib::e_part(bb(9)); eprintln!("|");"#, "")
        },
        Case {
            stderr: "1\n",
            ..case(
                "stdout_and_stderr",
                r#"print!("o:"); klib::e_show(bb(1)); klib::show(bb(2));"#,
                "o:2\n",
            )
        },
        // A print in a frame with a live `Drop` guard (a cleanup edge under
        // panic=unwind).
        case(
            "guarded",
            r#"print!("a:"); klib::guarded(bb(5)); println!("end");"#,
            "a:g5:drop 5\nend\n",
        ),
    ];
    // The write error: run with stdout a pipe whose read end is closed
    // (`run_case`). std panics with this message; nothing reaches stdout.
    cases.push(Case {
        stderr: "failed printing to stdout",
        status: Status::Panicked,
        ..case(
            WRITE_ERROR_CASE,
            r#"klib::show(bb(5)); println!("after");"#,
            "",
        )
    });
    // The same write error in a frame with a live guard: under panic=unwind
    // std's panic leaves `_print` through the call's cleanup edge, so the
    // guard's `Drop` runs before the panic reaches `main`; under panic=abort
    // it never runs.
    cases.push(Case {
        stderr: "failed printing to stdout",
        unwind_stderr: "\nguard 5",
        status: Status::Panicked,
        ..case(
            WRITE_ERROR_GUARDED_CASE,
            r#"klib::err_guarded(bb(5)); println!("after");"#,
            "",
        )
    });
    cases
}

const WRITE_ERROR_CASE: &str = "write_error";
const WRITE_ERROR_GUARDED_CASE: &str = "write_error_guarded";

fn is_write_error_case(name: &str) -> bool {
    name == WRITE_ERROR_CASE || name == WRITE_ERROR_GUARDED_CASE
}

fn driver_source(cases: &[Case]) -> String {
    let mut arms = String::new();
    for case in cases {
        arms.push_str(&format!("        {:?} => {{ {} }}\n", case.name, case.body));
    }
    format!(
        "use std::hint::black_box as bb;\n\
         #[allow(unused_imports)]\n\
         use std::io::Write;\n\
         fn main() {{\n\
         \x20   let arg = std::env::args().nth(1).unwrap_or_default();\n\
         \x20   match arg.as_str() {{\n\
         {arms}\
         \x20       _ => std::process::exit(2),\n\
         \x20   }}\n\
         }}\n"
    )
}

#[derive(Clone, Copy, Debug)]
struct Config {
    opt: &'static str,
    panic: &'static str,
}

impl Config {
    fn label(self) -> String {
        format!("O{}-{}", self.opt, self.panic)
    }

    fn status(self, status: Status) -> Status {
        match (status, self.panic) {
            (Status::Panicked, "abort") => Status::Abort,
            (Status::Panicked, _) => Status::Code(101),
            (other, _) => other,
        }
    }
}

const CONFIGS: [Config; 4] = [
    Config {
        opt: "0",
        panic: "abort",
    },
    Config {
        opt: "3",
        panic: "abort",
    },
    Config {
        opt: "0",
        panic: "unwind",
    },
    Config {
        opt: "3",
        panic: "unwind",
    },
];

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("tcg_print_order_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

fn base_command(config: Config) -> Command {
    let mut cmd = toolchain_support::rustc_command();
    cmd.arg(format!("-Cpanic={}", config.panic));
    cmd.arg("-Ccodegen-units=1");
    cmd.arg(format!("-Copt-level={}", config.opt));
    cmd
}

fn add_backend(cmd: &mut Command, dylib: &Path) {
    let mut backend_arg = std::ffi::OsString::from("-Zcodegen-backend=");
    backend_arg.push(dylib);
    cmd.arg(backend_arg);
    cmd.arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]));
}

fn compile(mut cmd: Command) -> Result<(), String> {
    let output = cmd.output().expect("spawn the compiler");
    if output.status.success() {
        Ok(())
    } else {
        Err(String::from_utf8_lossy(&output.stderr).into_owned())
    }
}

/// Compile `src` as the rlib `klib`; `Err` carries the compiler's stderr.
fn compile_lib(
    config: Config,
    src: &Path,
    backend: Option<&Path>,
    rlib: &Path,
) -> Result<(), String> {
    let mut cmd = base_command(config);
    cmd.args(["--crate-type", "rlib", "--crate-name", "klib"]);
    if let Some(dylib) = backend {
        add_backend(&mut cmd, dylib);
    }
    cmd.arg("-o").arg(rlib).arg(src);
    compile(cmd)
}

/// Link an LLVM-compiled crate of `crate_type` from `src` against `rlib`.
fn compile_llvm_user(config: Config, src: &Path, rlib: &Path, crate_type: &str, bin: &Path) {
    let mut cmd = base_command(config);
    if crate_type == "test" {
        cmd.arg("--test");
    } else {
        cmd.args(["--crate-type", crate_type]);
    }
    let mut extern_arg = std::ffi::OsString::from("klib=");
    extern_arg.push(rlib);
    cmd.arg("--extern").arg(extern_arg);
    cmd.arg("-o").arg(bin).arg(src);
    if let Err(stderr) = compile(cmd) {
        panic!(
            "{}: the LLVM-compiled caller did not build: <<<{stderr}>>>",
            config.label()
        );
    }
}

fn run_with_timeout(mut command: Command) -> Option<Output> {
    let mut child = command
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn the compiled program");
    let start = Instant::now();
    loop {
        if child
            .try_wait()
            .expect("poll the compiled program")
            .is_some()
        {
            return Some(child.wait_with_output().expect("collect program output"));
        }
        if start.elapsed() >= RUN_TIMEOUT {
            child.kill().expect("kill the timed-out program");
            let _ = child.wait_with_output();
            return None;
        }
        std::thread::sleep(Duration::from_millis(20));
    }
}

/// Run one case. A write-error case gets a stdout pipe whose read end is
/// already closed, so its first write fails with `EPIPE` (Rust programs
/// ignore `SIGPIPE`); every other case gets a fresh pipe.
fn run_case(bin: &Path, case: &str) -> Option<Output> {
    let mut command = Command::new(bin);
    command.arg(case);
    if is_write_error_case(case) {
        let (reader, writer) = std::io::pipe().expect("create a pipe");
        drop(reader);
        command.stdout(writer);
    } else {
        command.stdout(Stdio::piped());
    }
    run_with_timeout(command)
}

fn status_of(output: &Output) -> Status {
    use std::os::unix::process::ExitStatusExt;
    match (output.status.code(), output.status.signal()) {
        (Some(code), _) => Status::Code(code),
        (None, Some(6)) => Status::Abort,
        (None, signal) => Status::Signal(signal.unwrap_or(-1)),
    }
}

/// `(status, stdout, stderr)` of a run. A write-error case's stderr is
/// reduced to whether it carries std's panic message, which also names the
/// panicking thread, followed by every `guard` line a cleanup printed.
fn observed(case: &Case, output: &Output) -> (Status, String, String) {
    let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
    let stderr = if is_write_error_case(case.name) {
        if stderr.contains(case.stderr) {
            let cleanup: String = stderr
                .lines()
                .filter(|line| line.starts_with("guard "))
                .map(|line| format!("\n{line}"))
                .collect();
            format!("{}{cleanup}", case.stderr)
        } else {
            stderr
        }
    } else {
        stderr
    };
    (
        status_of(output),
        String::from_utf8_lossy(&output.stdout).into_owned(),
        stderr,
    )
}

/// Every `[TCG-...]` code in `stderr`.
fn refusal_codes(stderr: &str) -> Vec<String> {
    let mut codes = Vec::new();
    let mut rest = stderr;
    while let Some(start) = rest.find("[TCG-") {
        let tail = &rest[start + 1..];
        let Some(end) = tail.find(']') else {
            break;
        };
        codes.push(tail[..end].to_owned());
        rest = &tail[end..];
    }
    codes
}

fn check_config(dylib: &Path, config: Config, cases: &[Case]) -> Vec<String> {
    let label = config.label();
    let dir = workdir(&label);
    let lib_src = dir.join("klib.rs");
    std::fs::write(&lib_src, LIB_SOURCE).expect("write library source");
    let driver_src = dir.join("kmain.rs");
    std::fs::write(&driver_src, driver_source(cases)).expect("write driver source");
    let oracle_rlib = dir.join("llvm").join("libklib.rlib");
    let bridge_rlib = dir.join("bridge").join("libklib.rlib");
    std::fs::create_dir_all(oracle_rlib.parent().unwrap()).expect("create oracle dir");
    std::fs::create_dir_all(bridge_rlib.parent().unwrap()).expect("create bridge dir");

    compile_lib(config, &lib_src, None, &oracle_rlib)
        .unwrap_or_else(|e| panic!("{label}: the LLVM oracle library did not build: <<<{e}>>>"));
    let oracle_bin = dir.join("llvm_kmain");
    compile_llvm_user(config, &driver_src, &oracle_rlib, "bin", &oracle_bin);

    if let Err(stderr) = compile_lib(config, &lib_src, Some(dylib), &bridge_rlib) {
        panic!(
            "{label}: the bridge refused the printing library (codes {:?}); every shape in it \
             compiled before the print sink was repaired, so this is a regression: \
             <<<{stderr}>>>",
            refusal_codes(&stderr)
        );
    }
    let bridge_bin = dir.join("bridge_kmain");
    compile_llvm_user(config, &driver_src, &bridge_rlib, "bin", &bridge_bin);

    let mut report = Vec::new();
    for case in cases {
        let row = format!("{}@{label}", case.name);
        let want = (
            config.status(case.status),
            case.stdout.clone(),
            case.expected_stderr(config),
        );
        let oracle = run_case(&oracle_bin, case.name)
            .unwrap_or_else(|| panic!("row {row}: the LLVM oracle did not finish"));
        assert_eq!(
            observed(case, &oracle),
            want,
            "row {row}: the LLVM oracle must print exactly the expected bytes"
        );
        let bridge = run_case(&bridge_bin, case.name).unwrap_or_else(|| {
            panic!("row {row}: the bridge-compiled library did not finish within {RUN_TIMEOUT:?}")
        });
        assert_eq!(
            observed(case, &bridge),
            want,
            "row {row}: the bridge-compiled library's output disagrees with LLVM. A print \
             that does not go through std's own `_print`/`_eprint` overtakes the bytes std is \
             still buffering: route it through std or refuse the shape with \
             [TCG-PRINT-SINK], rather than relaxing this assertion. Full stderr \
             <<<{}>>>",
            String::from_utf8_lossy(&bridge.stderr)
        );
        report.push(format!("{row} MATCHED LLVM"));
    }
    let _ = std::fs::remove_dir_all(&dir);
    report
}

#[test]
fn bridge_prints_interleave_with_std_stdout_like_llvm() {
    if toolchain_support::skip_without_backend_knobs(
        "bridge_prints_interleave_with_std_stdout_like_llvm",
    ) {
        return;
    }
    let dylib = backend_artifact_support::current_test_backend();
    let cases = cases();
    let mut report = Vec::new();
    for config in CONFIGS {
        report.extend(check_config(&dylib, config, &cases));
    }
    assert_eq!(report.len(), CONFIGS.len() * cases.len());
    eprintln!("print order rows ({}): {report:#?}", report.len());
}

/// The whole program compiled by the bridge: std's own `write_all` buffers a
/// partial line, and every print in `main` is the bridge's. Measured on
/// f349c8652: "7\nb:-1 true\ntaila:" at -O0 and -O3 (the partial line moved
/// to the flush at exit).
#[test]
fn whole_program_prints_match_llvm() {
    if toolchain_support::skip_without_backend_knobs("whole_program_prints_match_llvm") {
        return;
    }
    let dylib = backend_artifact_support::current_test_backend();
    let dir = workdir("whole_program");
    let src = dir.join("whole.rs");
    std::fs::write(
        &src,
        "use std::hint::black_box as bb;\n\
         use std::io::Write;\n\
         fn main() {\n\
         \x20   let _ = std::io::stdout().write_all(b\"a:\");\n\
         \x20   println!(\"{}\", bb(7u32));\n\
         \x20   print!(\"b:\");\n\
         \x20   println!(\"{} {}\", bb(-1i128), bb(true));\n\
         \x20   eprint!(\"e:\");\n\
         \x20   eprintln!(\"{}\", bb('x'));\n\
         \x20   print!(\"tail\");\n\
         }\n",
    )
    .expect("write program source");
    for opt in ["0", "3"] {
        let config = Config {
            opt,
            panic: "abort",
        };
        let build = |backend: Option<&Path>, bin: &Path| -> Result<(), String> {
            let mut cmd = base_command(config);
            cmd.args(["--crate-type", "bin", "--crate-name", "whole"]);
            if let Some(dylib) = backend {
                add_backend(&mut cmd, dylib);
            }
            cmd.arg("-o").arg(bin).arg(&src);
            compile(cmd)
        };
        let run = |bin: &Path| -> (Option<i32>, String, String) {
            let mut command = Command::new(bin);
            command.stdout(Stdio::piped());
            let output = run_with_timeout(command)
                .unwrap_or_else(|| panic!("O{opt}: {bin:?} did not finish"));
            (
                output.status.code(),
                String::from_utf8_lossy(&output.stdout).into_owned(),
                String::from_utf8_lossy(&output.stderr).into_owned(),
            )
        };
        let oracle_bin = dir.join(format!("llvm_whole_O{opt}"));
        build(None, &oracle_bin)
            .unwrap_or_else(|e| panic!("O{opt}: the LLVM oracle did not build: <<<{e}>>>"));
        let want = (
            Some(0),
            "a:7\nb:-1 true\ntail".to_owned(),
            "e:x\n".to_owned(),
        );
        assert_eq!(run(&oracle_bin), want, "O{opt}: the LLVM oracle");
        let bridge_bin = dir.join(format!("bridge_whole_O{opt}"));
        build(Some(&dylib), &bridge_bin).unwrap_or_else(|e| {
            panic!(
                "O{opt}: the bridge must compile the whole program (codes {:?}): <<<{e}>>>",
                refusal_codes(&e)
            )
        });
        assert_eq!(
            run(&bridge_bin),
            want,
            "O{opt}: the bridge-compiled program's output disagrees with LLVM"
        );
        eprintln!("whole program O{opt}: MATCHED LLVM");
    }
    let _ = std::fs::remove_dir_all(&dir);
}

/// libtest captures what a passing test prints through std (`OUTPUT_CAPTURE`).
/// The library's prints are the bridge's; the test harness is LLVM-built.
/// Measured on f349c8652: the bridge's "5" leaked into the runner's stdout
/// (`test prints ... 5\nok`). With `--show-output` the captured bytes are
/// printed back, which pins that they reached the capture buffer.
#[test]
fn libtest_captures_bridge_prints() {
    if toolchain_support::skip_without_backend_knobs("libtest_captures_bridge_prints") {
        return;
    }
    let dylib = backend_artifact_support::current_test_backend();
    let dir = workdir("libtest_capture");
    let lib_src = dir.join("klib.rs");
    std::fs::write(&lib_src, LIB_SOURCE).expect("write library source");
    let test_src = dir.join("t.rs");
    std::fs::write(
        &test_src,
        "#[test]\n\
         fn prints() {\n\
         \x20   klib::show(std::hint::black_box(5));\n\
         \x20   klib::e_show(std::hint::black_box(6));\n\
         }\n",
    )
    .expect("write test source");
    // libtest's summary carries the elapsed time; nothing else varies.
    let normalize = |text: &[u8]| -> String {
        String::from_utf8_lossy(text)
            .lines()
            .map(|line| match line.find("; finished in ") {
                Some(at) => &line[..at],
                None => line,
            })
            .collect::<Vec<_>>()
            .join("\n")
    };
    for opt in ["0", "3"] {
        let config = Config {
            opt,
            panic: "unwind",
        };
        let mut outputs = Vec::new();
        for backend in [None, Some(dylib.as_path())] {
            let side = if backend.is_some() { "bridge" } else { "llvm" };
            let rlib = dir.join(side).join("libklib.rlib");
            std::fs::create_dir_all(rlib.parent().unwrap()).expect("create rlib dir");
            compile_lib(config, &lib_src, backend, &rlib).unwrap_or_else(|e| {
                panic!(
                    "O{opt} {side}: the library did not build (codes {:?}): <<<{e}>>>",
                    refusal_codes(&e)
                )
            });
            let bin = dir.join(format!("t_{side}_O{opt}"));
            compile_llvm_user(config, &test_src, &rlib, "test", &bin);
            let mut runs = Vec::new();
            for extra in [None, Some("--show-output")] {
                let mut command = Command::new(&bin);
                command.arg("--test-threads=1").stdout(Stdio::piped());
                command.args(extra);
                let output = run_with_timeout(command)
                    .unwrap_or_else(|| panic!("O{opt} {side}: the test binary did not finish"));
                runs.push((
                    output.status.code(),
                    normalize(&output.stdout),
                    normalize(&output.stderr),
                ));
            }
            outputs.push(runs);
        }
        let (oracle, bridge) = (&outputs[0], &outputs[1]);
        assert!(
            oracle[0].0 == Some(0)
                && oracle[0].1.contains("test prints ... ok")
                && !oracle[0].1.contains('5')
                && !oracle[0].2.contains('6')
                && oracle[1].1.contains("---- prints stdout ----\n5\n6\n"),
            "O{opt}: the LLVM oracle must capture both prints: {oracle:?}"
        );
        assert_eq!(
            bridge, oracle,
            "O{opt}: the bridge-compiled library's prints escaped libtest's capture (or never \
             reached it)"
        );
        eprintln!("libtest capture O{opt}: MATCHED LLVM");
    }
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn refusal_codes_lists_every_bracketed_code() {
    let stderr = "error: [TCG-MIR-UNSUPPORTED] cannot compile\n  - _RNvCs0_4klib4show \
                  (reachable): [TCG-PRINT-SINK] `std::io::_print`: detail";
    assert_eq!(
        refusal_codes(stderr),
        vec![
            "TCG-MIR-UNSUPPORTED".to_owned(),
            "TCG-PRINT-SINK".to_owned()
        ]
    );
    assert!(refusal_codes("no codes").is_empty());
}
