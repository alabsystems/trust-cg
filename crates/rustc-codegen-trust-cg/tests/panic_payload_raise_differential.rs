#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// Integration test: a panic whose ARGUMENT is the payload raises that payload.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// THE HAZARD. A diverging call into a `#[track_caller]` std panic entry is
// replaced by a raise of `core::panicking::panic(&str)` carrying a synthesized
// message (`block_diverges_via_panic` and the `#[track_caller]` diverging-call
// lane). For the message entries (`panic_fmt`, `assert_failed`, ...) that
// changes only the message text. `std::panic::panic_any(v)` and
// `std::panicking::begin_panic(v)` (what edition-2015/2018 `panic!(expr)` calls)
// raise `v` ITSELF: the substitution handed the panic hook and `catch_unwind` a
// `&str` ("panic raised via `panic_any` (message not lowered by trust-cg)")
// where the program raised an `i32`, a `u64`, a user struct or a different
// `&'static str`, so `downcast` took the other branch — a silent wrong value.
// Measured on upstream 6a57e8ab9 (proofs-off lane, LLVM caller, bridge
// library): `panic_any(3i32)` and 2018 `panic!(3u32)` reached `catch_unwind`
// and the hook as `str` at -O0..-O3 under `panic=unwind`, and reached the hook
// as `str` under `panic=abort`. `resume_unwind(Box::new(..))` is not
// `#[track_caller]`, kept its real call, and matched; it stays as a control.
//
// THE GATE, per row. Each row is ONE library kernel compiled by LLVM (the
// oracle) and by the bridge; the caller is always compiled by LLVM. The caller
// runs the kernel for slices of 0, 1, 3 and 5 elements (the kernel panics for
// 3 and more) and prints the result or the payload, and every location the
// kernel may write: a `Cell`, a `RefCell`, a `&mut u64`, a `Box<u64>` and a
// `static mut`. The panic hook prints the payload and the caller Location it
// sees (under `panic=abort` before the process aborts); under `panic=unwind`
// `catch_unwind` reads the payload again. `NOUNWIND_ROW` under `panic=unwind`
// raises in a nounwind frame: on a host whose bridge lowers the Rust terminate
// pad (`TERMINATE_PAD_HOST`) the real payload raise runs the hook, then the
// unwind reaches the frame's terminate pad, which runs the hook again for
// "panic in a function that cannot unwind" and aborts, and the row pins that
// transcript; elsewhere that edge traps without the hook, so the row's hook is
// silent and the row pins only the abort. Each
// row runs in its own process, so an abort is compared too. A row must compile
// and print exactly what the oracle prints and end the same way (exit code or
// signal); a different stdout or ending (the miscompile), a run past
// `RUN_TIMEOUT`, an ICE or any refusal fails it. The kernels of one
// optimization level and edition share one library, so one refused kernel
// fails them all. The oracle is asserted to raise in every row, so no row
// passes without the panic it is about.
//
// HOST-NATIVE: no `--target` is passed. The bridge side passes `no-proof-certs`
// for the reason `fat_thin_cast_differential.rs` gives: with certificates on,
// AArch64 objects stop at `[TCG-PROOF-465]` after lowering and would pin nothing.

use std::os::unix::process::ExitStatusExt;
use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};
use std::time::{Duration, Instant};

const RUN_TIMEOUT: Duration = Duration::from_secs(30);
const OPTS: [&str; 4] = ["0", "1", "2", "3"];
const EDITIONS: [&str; 3] = ["2021", "2018", "2015"];

/// The row whose payload raise sits in a nounwind (`extern "C"`) frame. Under
/// `panic=unwind` that edge raises into the terminate pad where the target has
/// one (`TERMINATE_PAD_HOST`) and traps elsewhere, where its hook is silent; it
/// must abort exactly as LLVM does.
const NOUNWIND_ROW: &str = "panic_any_in_nounwind_aborts";

/// Whether this host's bridge lowers a `Terminate` unwind edge as rustc does,
/// an `Invoke` into the Rust terminate pad (`supports_rust_terminate_filter`:
/// AArch64 Linux and Darwin). There a raise in a nounwind frame runs the panic
/// hook before the pad aborts, as under LLVM.
const TERMINATE_PAD_HOST: bool = cfg!(all(
    target_arch = "aarch64",
    any(target_os = "macos", target_os = "linux")
));

/// The kernel signature every row shares.
const SIGNATURE: &str = "(a: &[u64], log: &Cell<u64>, cell: &RefCell<u64>, m: &mut u64, \
                         bx: &mut Box<u64>) -> u64";

/// Library items a kernel may use, included only by the kernels that name them.
const ITEMS: [(&str, &str); 1] = [(
    "G",
    "pub struct G<'a> { pub log: &'a Cell<u64>, pub n: u64 }\n\
     impl<'a> Drop for G<'a> { fn drop(&mut self) { self.log.set(self.log.get() * 100 + self.n % 97 + 1); } }\n",
)];

struct Row {
    name: &'static str,
    /// The library's edition: 2015/2018 `panic!(expr)` calls `begin_panic`.
    edition: &'static str,
    body: &'static str,
}

fn rows() -> Vec<Row> {
    vec![
        // Controls: `resume_unwind` is not `#[track_caller]` and keeps its
        // real call; its boxed payload reaches the catch unchanged.
        Row {
            edition: "2021",
            name: "resume_unwind_noguard",
            body: "if a.len() >= 3 { log.set(34); std::panic::resume_unwind(Box::new(a.len() as u32)) } 13",
        },
        Row {
            edition: "2021",
            name: "resume_unwind_guard",
            body: "let g = G { log, n: 5 }; if a.len() >= 3 { log.set(34); std::panic::resume_unwind(Box::new(a.len() as u32)) } let _ = &g; 13",
        },
        // `panic_any(v)`: the payload is `v`. With a guard the call's unwind
        // action is `Cleanup(pad)`; without one it is `Continue`.
        Row {
            edition: "2021",
            name: "panic_any_guard",
            body: "let g = G { log, n: 5 }; if a.len() >= 3 { log.set(35); std::panic::panic_any(a.len() as i32) } let _ = &g; 14",
        },
        Row {
            edition: "2021",
            name: "panic_any_noguard",
            body: "if a.len() >= 3 { *m = 55; std::panic::panic_any(a.len() as i32) } 34",
        },
        Row {
            edition: "2021",
            name: "panic_any_u64",
            body: "if a.len() >= 3 { **bx = 57; std::panic::panic_any(a.len() as u64 * 1000) } 15",
        },
        Row {
            edition: "2021",
            name: "panic_any_struct",
            body: "if a.len() >= 3 { std::panic::panic_any(Tok(a.len() as u64 + 40)) } 17",
        },
        // A `&'static str` payload keeps its own text, not a synthesized one.
        Row {
            edition: "2021",
            name: "panic_any_static_str",
            body: "if a.len() >= 3 { log.set(37); std::panic::panic_any(\"lit-payload\") } 18",
        },
        // A payload raise that cannot unwind out of its frame (an `extern "C"`
        // body: `UnwindAction::Terminate`) aborts on both sides.
        Row {
            edition: "2021",
            name: NOUNWIND_ROW,
            body: "extern \"C\" fn raise(n: u64, log: &Cell<u64>) { log.set(n); if n >= 3 { std::panic::panic_any(n as u32) } } raise(a.len() as u64, log); 35",
        },
        // Edition 2015/2018 `panic!(expr)` raises `expr` itself through
        // `std::panicking::begin_panic`; a lone literal is a `&'static str`
        // payload with the literal's text.
        Row {
            edition: "2018",
            name: "e2018_panic_u32_guard",
            body: "let g = G { log, n: 5 }; if a.len() >= 3 { log.set(52); panic!(a.len() as u32) } let _ = &g; 31",
        },
        Row {
            edition: "2018",
            name: "e2018_panic_u32_noguard",
            body: "if a.len() >= 3 { *m = 53; panic!(a.len() as u32) } 32",
        },
        Row {
            edition: "2018",
            name: "e2018_panic_lit_guard",
            body: "let g = G { log, n: 5 }; if a.len() >= 3 { log.set(51); panic!(\"lit\") } let _ = &g; 30",
        },
        // Control: a formatted 2018 panic calls `panic_fmt`, a message entry.
        Row {
            edition: "2018",
            name: "e2018_panic_fmt_guard",
            body: "let g = G { log, n: 5 }; if a.len() >= 3 { log.set(54); panic!(\"n={}\", a.len()) } let _ = &g; 33",
        },
        Row {
            edition: "2015",
            name: "e2015_panic_u32_noguard",
            body: "if a.len() >= 3 { *m = 56; panic!(a.len() as u32) } 36",
        },
    ]
}

/// Whether `body` names the identifier `word`.
fn names_identifier(body: &str, word: &str) -> bool {
    let ident = |c: Option<char>| c.is_some_and(|c| c.is_alphanumeric() || c == '_');
    body.match_indices(word).any(|(at, _)| {
        !ident(body[..at].chars().next_back()) && !ident(body[at + word.len()..].chars().next())
    })
}

/// The library items `bodies` use, in `ITEMS` order.
fn kernel_items<'a>(bodies: impl IntoIterator<Item = &'a str> + Clone) -> String {
    ITEMS
        .iter()
        .filter(|(name, _)| {
            bodies
                .clone()
                .into_iter()
                .any(|body| names_identifier(body, name))
        })
        .map(|(_, item)| *item)
        .collect()
}

/// One library holding `rows`' kernels, `k_<name>` each. `Tok` is always
/// defined: the caller downcasts to it.
fn lib_source(rows: &[&Row]) -> String {
    let mut src = String::from(
        "#![allow(unused)]\n\
         use std::cell::{Cell, RefCell};\n\
         pub static mut S: u64 = 0;\n\
         pub struct Tok(pub u64);\n",
    );
    src.push_str(&kernel_items(rows.iter().map(|row| row.body)));
    for row in rows {
        src.push_str(&format!(
            "#[inline(never)]\npub fn k_{}{SIGNATURE} {{\n    {}\n}}\n",
            row.name, row.body
        ));
    }
    src
}

/// The literal `&str` payloads the rows raise; the caller prints these texts
/// and reports any other `&str`/`String` payload only as `str`.
const LITERAL_PAYLOADS: [&str; 2] = ["lit", "lit-payload"];

/// The LLVM-compiled caller: `kmain <row>` runs that row's kernel. The hook
/// prints the payload and its caller Location (line:column), and under
/// `panic=unwind` the catch prints the payload too. Only `NOUNWIND_ROW` under
/// `panic=unwind` off a `TERMINATE_PAD_HOST` has a silent hook (see the module
/// comment).
fn main_source(rows: &[&Row], panic: &str) -> String {
    let arms: String = rows
        .iter()
        .map(|row| {
            format!(
                "            \"{0}\" => klib::k_{0}(a, &log, &cell, &mut m, &mut bx),\n",
                row.name
            )
        })
        .collect();
    let quiet_row = if panic == "unwind" && !TERMINATE_PAD_HOST {
        NOUNWIND_ROW
    } else {
        ""
    };
    let literals = LITERAL_PAYLOADS
        .iter()
        .map(|text| format!("{text:?}"))
        .collect::<Vec<_>>()
        .join(", ");
    format!(
        "use std::any::Any;\n\
         use std::cell::{{Cell, RefCell}};\n\
         use std::hint::black_box;\n\
         fn kind(e: &(dyn Any + Send)) -> String {{\n\
         \x20   if let Some(v) = e.downcast_ref::<u32>() {{ format!(\"u32:{{}}\", v) }}\n\
         \x20   else if let Some(v) = e.downcast_ref::<i32>() {{ format!(\"i32:{{}}\", v) }}\n\
         \x20   else if let Some(v) = e.downcast_ref::<u64>() {{ format!(\"u64:{{}}\", v) }}\n\
         \x20   else if let Some(v) = e.downcast_ref::<klib::Tok>() {{ format!(\"Tok:{{}}\", v.0) }}\n\
         \x20   else if let Some(s) = e.downcast_ref::<&str>().filter(|s| [{literals}].contains(*s)) {{ format!(\"str:{{}}\", s) }}\n\
         \x20   else if e.downcast_ref::<&str>().is_some() || e.downcast_ref::<String>().is_some() {{ \"str\".to_owned() }}\n\
         \x20   else {{ \"other\".to_owned() }}\n\
         }}\n\
         fn main() {{\n\
         \x20   let case = std::env::args().nth(1).expect(\"row name\");\n\
         \x20   let quiet = case == \"{quiet_row}\";\n\
         \x20   std::panic::set_hook(Box::new(move |info| if !quiet {{\n\
         \x20       let l = info.location().expect(\"hook location\");\n\
         \x20       println!(\"hook payload {{}} at {{}}:{{}}\", kind(info.payload()), l.line(), l.column());\n\
         \x20   }}));\n\
         \x20   let all = [10u64, 20, 30, 40, 50];\n\
         \x20   for n in [0usize, 1, 3, 5] {{\n\
         \x20       unsafe {{ *std::ptr::addr_of_mut!(klib::S) = 0; }}\n\
         \x20       let log = Cell::new(0u64);\n\
         \x20       let cell = RefCell::new(1u64);\n\
         \x20       let mut m = 7u64;\n\
         \x20       let mut bx = Box::new(8u64);\n\
         \x20       let a = black_box(&all[..n]);\n\
         \x20       let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| match case.as_str() {{\n\
         {arms}\
         \x20           other => panic!(\"no row {{other}}\"),\n\
         \x20       }}));\n\
         \x20       let r = match r {{ Ok(v) => format!(\"{{}}\", v), Err(e) => format!(\"panicked({{}})\", kind(&*e)) }};\n\
         \x20       let b = match cell.try_borrow_mut() {{ Ok(v) => *v, Err(_) => 999999 }};\n\
         \x20       let s = unsafe {{ *std::ptr::addr_of!(klib::S) }};\n\
         \x20       println!(\"n={{}} r={{}} log={{}} cell={{}} m={{}} bx={{}} S={{}}\", n, r, log.get(), b, m, *bx, s);\n\
         \x20   }}\n\
         }}\n"
    )
}

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("tcg_panic_payload_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

fn base_command(opt: &str, panic: &str, edition: &str) -> Command {
    let mut cmd = toolchain_support::rustc_command_with_edition(edition);
    cmd.arg(format!("-Cpanic={panic}"));
    cmd.arg("-Ccodegen-units=1");
    cmd.arg(format!("-Copt-level={opt}"));
    cmd
}

fn add_backend(cmd: &mut Command, dylib: &Path) {
    let mut backend_arg = std::ffi::OsString::from("-Zcodegen-backend=");
    backend_arg.push(dylib);
    cmd.arg(backend_arg);
    cmd.arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]));
}

/// Compile a library; `Err` carries the compiler's stderr.
fn compile_lib(
    dir: &Path,
    src: &str,
    (opt, panic, edition): (&str, &str, &str),
    backend: Option<&Path>,
    rlib: &Path,
) -> Result<(), String> {
    let path = dir.join("klib.rs");
    std::fs::write(&path, src).expect("write library source");
    let mut cmd = base_command(opt, panic, edition);
    cmd.args(["--crate-type", "rlib", "--crate-name", "klib"]);
    if let Some(dylib) = backend {
        add_backend(&mut cmd, dylib);
    }
    cmd.arg("-o").arg(rlib).arg(&path);
    let output = cmd.output().expect("spawn the compiler");
    if output.status.success() {
        Ok(())
    } else {
        Err(String::from_utf8_lossy(&output.stderr).into_owned())
    }
}

/// Link the LLVM-compiled caller against `rlib`.
fn compile_main(dir: &Path, src: &str, opt: &str, panic: &str, rlib: &Path, bin: &Path) {
    let path = dir.join("kmain.rs");
    std::fs::write(&path, src).expect("write caller source");
    let mut cmd = base_command(opt, panic, "2021");
    cmd.args(["--crate-type", "bin", "--crate-name", "kmain"]);
    let mut extern_arg = std::ffi::OsString::from("klib=");
    extern_arg.push(rlib);
    cmd.arg("--extern").arg(extern_arg);
    cmd.arg("-o").arg(bin).arg(&path);
    let output = cmd.output().expect("spawn the compiler");
    assert!(
        output.status.success(),
        "{}: the LLVM-compiled caller did not build: <<<{}>>>",
        dir.display(),
        String::from_utf8_lossy(&output.stderr)
    );
}

fn run_with_timeout(bin: &Path, arg: &str) -> Option<Output> {
    let mut child = Command::new(bin)
        .arg(arg)
        .stdout(Stdio::piped())
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

/// How a program ended: its exit code, or the signal that killed it.
fn ending(output: &Output) -> String {
    match (output.status.code(), output.status.signal()) {
        (Some(code), _) => format!("exit {code}"),
        (None, Some(signal)) => format!("signal {signal}"),
        (None, None) => "unknown".to_owned(),
    }
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

/// Run `rows` (one edition) through the oracle and the bridge at one level;
/// `report` gets one verdict per row.
fn check_library(dylib: &Path, rows: &[&Row], opt: &str, panic: &str, report: &mut Vec<String>) {
    let edition = rows[0].edition;
    assert!(
        rows.iter().all(|row| row.edition == edition),
        "one library has one edition"
    );
    let stem = format!("{panic}_O{opt}_e{edition}");
    let dir = workdir(&stem);
    let lib = lib_source(rows);
    let main = main_source(rows, panic);
    let oracle_rlib = dir.join("llvm").join("libklib.rlib");
    let bridge_rlib = dir.join("bridge").join("libklib.rlib");
    std::fs::create_dir_all(oracle_rlib.parent().unwrap()).expect("create oracle dir");
    std::fs::create_dir_all(bridge_rlib.parent().unwrap()).expect("create bridge dir");
    compile_lib(&dir, &lib, (opt, panic, edition), None, &oracle_rlib)
        .unwrap_or_else(|e| panic!("{stem}: the LLVM oracle library did not build: <<<{e}>>>"));
    let oracle_bin = dir.join("llvm_kmain");
    compile_main(&dir, &main, opt, panic, &oracle_rlib, &oracle_bin);
    if let Err(stderr) = compile_lib(&dir, &lib, (opt, panic, edition), Some(dylib), &bridge_rlib) {
        assert!(
            !stderr.contains("internal compiler error") && !stderr.contains("panicked at"),
            "{stem}: the bridge crashed instead of failing closed: <<<{stderr}>>>"
        );
        panic!(
            "{stem}: every payload kernel must compile and match LLVM, but the library was \
             refused (codes {:?}): <<<{stderr}>>>",
            refusal_codes(&stderr)
        );
    }
    let bridge_bin = dir.join("bridge_kmain");
    compile_main(&dir, &main, opt, panic, &bridge_rlib, &bridge_bin);
    for row in rows {
        let label = format!("{}@O{opt} panic={panic}", row.name);
        let oracle = run_with_timeout(&oracle_bin, row.name)
            .unwrap_or_else(|| panic!("row {label}: the LLVM oracle did not finish"));
        let oracle_stdout = String::from_utf8_lossy(&oracle.stdout).into_owned();
        // Every row raises for the 3-element slice: under `panic=unwind` the
        // caller prints `panicked(..)` or the process aborts mid-row; under
        // `panic=abort` the process aborts after the two non-panicking lines.
        // The hook reports the payload in every row except `resume_unwind`,
        // which runs no hook, and `NOUNWIND_ROW` under `panic=unwind` off a
        // `TERMINATE_PAD_HOST`, whose hook is silent.
        let raised = oracle_stdout.contains("r=panicked(") || !oracle.status.success();
        assert!(
            row.name.starts_with("resume_unwind")
                || (panic == "unwind" && row.name == NOUNWIND_ROW && !TERMINATE_PAD_HOST)
                || oracle_stdout.contains("\nhook payload "),
            "row {label}: the LLVM oracle's hook must report the payload; \
             stdout <<<{oracle_stdout}>>>"
        );
        assert!(
            raised && oracle_stdout.starts_with("n=0 ") && oracle_stdout.contains("\nn=1 "),
            "row {label}: the LLVM oracle must run the non-panicking slices and then raise; \
             {}, stdout <<<{oracle_stdout}>>>",
            ending(&oracle)
        );
        let Some(run) = run_with_timeout(&bridge_bin, row.name) else {
            panic!(
                "row {label}: the bridge-compiled kernel did not finish within {RUN_TIMEOUT:?}; \
                 oracle printed <<<{oracle_stdout}>>>"
            );
        };
        let stdout = String::from_utf8_lossy(&run.stdout).into_owned();
        assert_eq!(
            (ending(&run), stdout.as_str()),
            (ending(&oracle), oracle_stdout.as_str()),
            "row {label}: the bridge-compiled kernel disagrees with LLVM. A raise entry whose \
             argument is the payload must raise that payload: call the real entry, or refuse \
             the shape by name, rather than relaxing this assertion. stderr <<<{}>>>",
            String::from_utf8_lossy(&run.stderr)
        );
        eprintln!("row {label}: MATCHED LLVM");
        report.push(format!("{label} MATCHED LLVM"));
    }
    let _ = std::fs::remove_dir_all(&dir);
}

fn check_all(panic: &str) {
    let dylib = backend_artifact_support::current_test_backend();
    let rows = rows();
    let mut report = Vec::new();
    for opt in OPTS {
        for edition in EDITIONS {
            let group: Vec<&Row> = rows.iter().filter(|row| row.edition == edition).collect();
            check_library(&dylib, &group, opt, panic, &mut report);
        }
    }
    assert_eq!(
        report.len(),
        rows.len() * OPTS.len(),
        "every row ran at every level"
    );
    eprintln!("panic={panic} rows ({}): {report:#?}", report.len());
}

#[test]
fn payload_raise_keeps_its_payload_under_unwind() {
    if toolchain_support::skip_without_backend_knobs("payload_raise_keeps_its_payload_under_unwind")
    {
        return;
    }
    check_all("unwind");
}

#[test]
fn payload_raise_keeps_its_payload_under_abort() {
    if toolchain_support::skip_without_backend_knobs("payload_raise_keeps_its_payload_under_abort")
    {
        return;
    }
    check_all("abort");
}

#[test]
fn every_edition_has_rows_and_kernels_include_only_the_items_they_name() {
    let rows = rows();
    for edition in EDITIONS {
        assert!(
            rows.iter().any(|row| row.edition == edition),
            "edition {edition} has no row"
        );
    }
    let noguard = rows
        .iter()
        .find(|row| row.name == "panic_any_noguard")
        .unwrap();
    assert_eq!(kernel_items([noguard.body]), "");
    let guard = rows
        .iter()
        .find(|row| row.name == "panic_any_guard")
        .unwrap();
    assert_eq!(kernel_items([guard.body]), ITEMS[0].1);
    assert!(lib_source(&[noguard]).contains("pub struct Tok("));
    let names: std::collections::BTreeSet<_> = rows.iter().map(|row| row.name).collect();
    assert_eq!(names.len(), rows.len(), "row names are unique");
}
