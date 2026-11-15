// Compiled only on an aarch64-apple-darwin host: another host builds this
// target with no test in it, never one that passes without running (L06-P10).
#![cfg(all(target_os = "macos", target_arch = "aarch64"))]

#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/darwin_native_prerequisites.rs"]
mod darwin_native;
#[path = "support/positive_evidence.rs"]
mod positive_evidence;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// E2E (aarch64-apple-darwin): DWARF line tables through the rustc bridge, and
// the named verdict of every codegen option the bridge does not honour
// (ledger L06-P7).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// WHAT THIS PINS. `-C debuginfo=line-tables-only` emits, per object, a DWARF 4
// line program (`__debug_line`) whose rows map emitted code to the MIR source
// spans of each function's own file, and one subprogram DIE per function named
// by its crate-qualified def-path (`__debug_info` / `__debug_abbrev` /
// `__debug_str`). rustc's own Mach-O handling then runs `dsymutil`
// (`-C split-debuginfo=packed`, the macOS default). The test checks the
// `.dSYM` with `dwarfdump --verify`, its line rows for both source files of a
// two-file crate, and drives `lldb` in batch mode: a breakpoint set by
// `file:line` in the second file stops there, and the backtrace names every
// frame of the crate by its def-path at `file:line`. `unpacked` keeps the
// objects the debug map names, and `lldb` resolves the same breakpoint from
// them. The other two tests pin the option matrix: every refused option
// (LTO, instrumented and sample PGO, coverage, debuginfo beyond line tables,
// sanitizers, stack protector, branch protection, mcount, a
// patchable-function-entry sled, a function alignment above four bytes, code
// model, jump tables) is refused by its `[TCG-OPT-*]` code before anything is
// lowered, and every note or warning the table can print is printed by a
// compile that succeeds.
//
// PROOFS-OFF DIAGNOSTIC. The debug compiles pass the backend's
// `no-proof-certs` knob: with certificates on, a `-C debuginfo` request is
// itself refused by name (`TCG-OPT-DEBUGINFO`, asserted below), because the
// certified-object relocation inventory refuses every object with DWARF
// sections; and every function body with a frame is refused at proof promotion
// anyway (`[TCG-PROOF-465]`, the proof wall of ledger L07-P2). The refusal
// test compiles with certificates on: its verdicts are printed before any
// proof work. Nothing here is a proof claim.

use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};
use std::time::{Duration, Instant};

use darwin_native::TARGET;

/// The crate root. `helper.rs` (below) is its second source file, so one
/// compile unit's functions come from two files.
const MAIN_RS: &str = "\
mod helper;

#[inline(never)]
fn accumulate(n: u32) -> u32 {
    let mut total = 0u32;
    let mut i = 1u32;
    while i <= n {
        total = total.wrapping_add(helper::scale(i));
        i = i.wrapping_add(1);
    }
    total
}

fn main() {
    let total = accumulate(std::hint::black_box(4));
    std::process::exit(total as i32);
}
";
/// The line of `MAIN_RS` that calls `helper::scale`.
const MAIN_CALL_LINE: u32 = 8;
/// The line of `MAIN_RS` that calls `accumulate`.
const MAIN_ENTRY_LINE: u32 = 15;

const HELPER_RS: &str = "\
#[inline(never)]
pub fn scale(x: u32) -> u32 {
    let tripled = x.wrapping_mul(3);
    tripled.wrapping_add(1)
}
";
/// The first statement line of `scale`.
const HELPER_LINE: u32 = 3;
/// `accumulate(4)`: the sum of `3 * i + 1` for `i` in `1..=4`.
const EXPECTED_EXIT: i32 = 34;

/// A library whose `#[inline(always)]` callee rustc's MIR inliner (on from
/// `-Copt-level=2`) inlines into its caller, so no mono item of the callee
/// remains: every instruction of its body is an inlined copy, which the line
/// table attributes to the outermost call site (`debug_source_span`).
const INLINE_RS: &str = "\
#[inline(always)]
fn callee(x: u32) -> u32 {
    (x ^ 0x5a5a).rotate_left(3)
}
#[inline(never)]
#[no_mangle]
pub extern \"C\" fn tcg_inline_caller(x: u32) -> u32 {
    callee(x).wrapping_add(1)
}
";
/// The line of the callee's body in `INLINE_RS`: its `^` is a statement of
/// the callee's own MIR, so a row would name this line if the inlined copy
/// were not attributed to its call site.
const INLINE_CALLEE_LINE: u32 = 3;
/// The line of `INLINE_RS` that calls the callee.
const INLINE_CALL_LINE: u32 = 8;

/// A scratch directory, removed when the test that made it succeeds.
struct Scratch(PathBuf);

impl Scratch {
    fn new(stem: &str) -> Self {
        let path =
            std::env::temp_dir().join(format!("tcg_debuginfo_a64_{stem}_{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&path);
        std::fs::create_dir_all(&path).expect("create scratch directory");
        Self(path)
    }
}

impl Drop for Scratch {
    fn drop(&mut self) {
        if !std::thread::panicking() {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }
}

fn backend_arg() -> std::ffi::OsString {
    let mut arg = std::ffi::OsString::from("-Zcodegen-backend=");
    arg.push(backend_artifact_support::current_test_backend());
    arg
}

fn text(output: &Output) -> String {
    format!(
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    )
}

/// Run `command` to completion under `limit`, killing it past the limit.
fn run_bounded(mut command: Command, limit: Duration) -> Output {
    let mut child = command
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn bounded command");
    let start = Instant::now();
    loop {
        if child.try_wait().expect("poll bounded command").is_some() {
            return child.wait_with_output().expect("collect bounded command");
        }
        if start.elapsed() > limit {
            let _ = child.kill();
            let output = child.wait_with_output().expect("collect killed command");
            panic!("command exceeded {limit:?}:\n{}", text(&output));
        }
        std::thread::sleep(Duration::from_millis(50));
    }
}

/// Write the two-file crate into `dir` and compile it through the bridge with
/// line tables and `split`, proofs off. Returns the executable.
fn compile_debug_crate(dir: &Path, split: &str) -> PathBuf {
    std::fs::write(dir.join("dbg.rs"), MAIN_RS).expect("write dbg.rs");
    std::fs::write(dir.join("helper.rs"), HELPER_RS).expect("write helper.rs");
    let exe = dir.join("dbg");
    let output = toolchain_support::rustc_command()
        .current_dir(dir)
        .arg(backend_arg())
        .arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]))
        .args(["--target", TARGET, "-Copt-level=0"])
        .arg("-Cdebuginfo=line-tables-only")
        .arg(format!("-Csplit-debuginfo={split}"))
        .arg("-o")
        .arg(&exe)
        .arg("dbg.rs")
        .output()
        .expect("spawn trustc");
    assert!(
        output.status.success(),
        "bridge compile with line tables ({split}) failed:\n{}",
        text(&output)
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !stderr.contains("[TCG-OPT-"),
        "line-tables-only is the honoured lane and must print no option verdict:\n{stderr}"
    );
    exe
}

fn dwarfdump(args: &[&str], path: &Path) -> String {
    let output = Command::new("dwarfdump")
        .args(args)
        .arg(path)
        .output()
        .expect("run dwarfdump");
    assert!(
        output.status.success(),
        "dwarfdump {args:?} {path:?} failed:\n{}",
        text(&output)
    );
    text(&output)
}

/// The `(line, file name)` rows of a `dwarfdump --debug-line` dump, with each
/// row's file index resolved through its own line table's file list.
fn line_rows(dump: &str) -> Vec<(u32, String)> {
    let mut rows = Vec::new();
    let mut files: Vec<(u32, String)> = Vec::new();
    let mut pending_index = None;
    for line in dump.lines() {
        let trimmed = line.trim();
        if trimmed.starts_with("debug_line[") {
            files.clear();
        } else if let Some(rest) = trimmed.strip_prefix("file_names[") {
            pending_index = rest
                .split(']')
                .next()
                .and_then(|index| index.trim().parse().ok());
        } else if let Some(name) = trimmed.strip_prefix("name: ") {
            if let Some(index) = pending_index.take() {
                files.push((index, name.trim_matches('"').to_owned()));
            }
        } else if trimmed.starts_with("0x") {
            let mut fields = trimmed.split_whitespace();
            let _address = fields.next();
            let line_number = fields.next().and_then(|field| field.parse().ok());
            let _column = fields.next();
            let file = fields.next().and_then(|field| field.parse::<u32>().ok());
            if let (Some(line_number), Some(file)) = (line_number, file) {
                if let Some((_, name)) = files.iter().find(|(index, _)| *index == file) {
                    rows.push((line_number, name.clone()));
                }
            }
        }
    }
    rows
}

/// `lldb` in batch mode: break at `helper.rs:HELPER_LINE`, run, print the
/// backtrace, then delete the breakpoint (the loop would hit it again) and
/// continue to exit.
fn lldb_session(exe: &Path) -> String {
    let mut command = Command::new("lldb");
    command
        .arg("--batch")
        .arg("-o")
        .arg(format!(
            "breakpoint set --file helper.rs --line {HELPER_LINE}"
        ))
        .args(["-o", "run", "-o", "bt"])
        .args(["-o", "breakpoint delete --force 1", "-o", "continue"])
        .arg(exe);
    let output = run_bounded(command, Duration::from_secs(180));
    text(&output)
}

/// The backtrace checks every lldb session must pass: the breakpoint resolved
/// by `file:line`, stopped there, and every frame of the crate is named by its
/// def-path at its `file:line`; the process then exits with the program's own
/// status.
fn check_lldb_session(session: &str, label: &str) {
    for needle in [
        "where = dbg`dbg::helper::scale + ".to_owned(),
        format!("at helper.rs:{HELPER_LINE}:"),
        "stop reason = breakpoint 1.1".to_owned(),
        format!("dbg`dbg::helper::scale at helper.rs:{HELPER_LINE}:"),
        format!("dbg`dbg::accumulate at dbg.rs:{MAIN_CALL_LINE}:"),
        format!("dbg`dbg::main at dbg.rs:{MAIN_ENTRY_LINE}:"),
        format!("exited with status = {EXPECTED_EXIT}"),
    ] {
        assert!(
            session.contains(&needle),
            "{label}: lldb session lacks {needle:?}:\n{session}"
        );
    }
    assert!(
        !session.contains("__trust_cg_private"),
        "{label}: a frame is named by its bridge-private object symbol:\n{session}"
    );
}

#[test]
fn line_tables_drive_dsymutil_dwarfdump_and_lldb_by_file_line() {
    darwin_native::require(
        "debuginfo_dwarf_aarch64",
        &["cc", "dwarfdump", "dsymutil", "lldb"],
    );
    let scratch = Scratch::new("packed");
    let dir = &scratch.0;
    let exe = compile_debug_crate(dir, "packed");

    // The program itself.
    let run = Command::new(&exe).output().expect("run dbg");
    assert_eq!(run.status.code(), Some(EXPECTED_EXIT), "{}", text(&run));

    // rustc ran dsymutil over the bridge objects' DWARF.
    let dsym = dir.join("dbg.dSYM");
    assert!(dsym.is_dir(), "split-debuginfo=packed left no {dsym:?}");
    let verify = dwarfdump(&["--verify"], &dsym);
    assert!(
        verify.contains("No errors."),
        "dwarfdump --verify:\n{verify}"
    );

    // Rows of both source files, each attributed to its own file.
    let lines = dwarfdump(&["--debug-line"], &dsym);
    let rows = line_rows(&lines);
    let main_path = dir.join("dbg.rs");
    let helper_path = dir.join("helper.rs");
    for (line, path) in [
        (HELPER_LINE, &helper_path),
        (MAIN_CALL_LINE, &main_path),
        (MAIN_ENTRY_LINE, &main_path),
    ] {
        let canonical = path.canonicalize().expect("canonical source path");
        assert!(
            rows.iter().any(|(row_line, file)| *row_line == line
                && (Path::new(file) == path.as_path() || Path::new(file) == canonical.as_path())),
            "no line-{line} row in {path:?}: {rows:?}"
        );
    }

    // One subprogram per crate function, named by its def-path.
    let info = dwarfdump(&["--debug-info"], &dsym);
    for name in ["dbg::helper::scale", "dbg::accumulate", "dbg::main"] {
        assert!(
            info.contains(&format!("DW_AT_name\t(\"{name}\")")),
            "no subprogram named {name}:\n{info}"
        );
    }

    check_lldb_session(&lldb_session(&exe), "packed");
    inlined_code_is_attributed_to_its_call_site(dir);
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}

/// Compile `INLINE_RS` at `-Copt-level=2` with line tables (proofs off) and
/// check its object's line rows: the MIR-inlined callee's statements are
/// rows at the call site's line, and no row names the callee's own line.
fn inlined_code_is_attributed_to_its_call_site(dir: &Path) {
    let out = dir.join("inline_out");
    std::fs::create_dir_all(&out).expect("create inline output directory");
    let source = dir.join("inl.rs");
    std::fs::write(&source, INLINE_RS).expect("write inl.rs");
    let output = toolchain_support::rustc_command()
        .current_dir(dir)
        .arg(backend_arg())
        .arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]))
        .args(["--target", TARGET, "--crate-type", "lib", "--emit=obj"])
        .args([
            "-Copt-level=2",
            "-Cpanic=abort",
            "-Cdebuginfo=line-tables-only",
        ])
        .arg("--out-dir")
        .arg(&out)
        .arg("inl.rs")
        .output()
        .expect("spawn trustc");
    assert!(
        output.status.success(),
        "O2 line-table compile failed:\n{}",
        text(&output)
    );
    let canonical = source.canonicalize().expect("canonical inl.rs");
    let mut rows = Vec::new();
    for entry in std::fs::read_dir(&out).expect("read inline output") {
        let object = entry.expect("inline output entry").path();
        if object.extension().is_some_and(|ext| ext == "o") {
            let verify = dwarfdump(&["--verify"], &object);
            assert!(verify.contains("No errors."), "{object:?}:\n{verify}");
            rows.extend(
                line_rows(&dwarfdump(&["--debug-line"], &object))
                    .into_iter()
                    .filter(|(_, file)| {
                        Path::new(file) == source.as_path()
                            || Path::new(file) == canonical.as_path()
                    })
                    .map(|(line, _)| line),
            );
        }
    }
    assert!(
        rows.contains(&INLINE_CALL_LINE),
        "no row at the call site's line {INLINE_CALL_LINE}: {rows:?}"
    );
    assert!(
        !rows.contains(&INLINE_CALLEE_LINE),
        "inlined code must be attributed to its call site, not to the callee's line \
         {INLINE_CALLEE_LINE}: {rows:?}"
    );
}

#[test]
fn unpacked_split_debuginfo_keeps_objects_lldb_resolves_by_file_line() {
    darwin_native::require("debuginfo_dwarf_aarch64", &["cc", "dwarfdump", "lldb"]);
    let scratch = Scratch::new("unpacked");
    let dir = &scratch.0;
    let exe = compile_debug_crate(dir, "unpacked");
    let run = Command::new(&exe).output().expect("run dbg");
    assert_eq!(run.status.code(), Some(EXPECTED_EXIT), "{}", text(&run));
    assert!(
        !dir.join("dbg.dSYM").exists(),
        "split-debuginfo=unpacked must not run dsymutil"
    );
    // The objects the debug map names are kept, and each carries verified
    // DWARF: every bridge object of the crate's code has a line program.
    let objects: Vec<PathBuf> = std::fs::read_dir(dir)
        .expect("read scratch directory")
        .filter_map(|entry| entry.ok().map(|entry| entry.path()))
        .filter(|path| path.extension().is_some_and(|ext| ext == "o"))
        .collect();
    assert!(!objects.is_empty(), "unpacked kept no objects in {dir:?}");
    let mut with_lines = 0;
    for object in &objects {
        let verify = dwarfdump(&["--verify"], object);
        assert!(
            verify.contains("No errors."),
            "{object:?}: dwarfdump --verify:\n{verify}"
        );
        if !line_rows(&dwarfdump(&["--debug-line"], object)).is_empty() {
            with_lines += 1;
        }
    }
    assert!(
        with_lines >= 1,
        "no kept object has a line row: {objects:?}"
    );
    check_lldb_session(&lldb_session(&exe), "unpacked");
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}

/// The trivial library every option compile builds.
const OPTION_LIB: &str = "#![crate_type = \"lib\"]\n#[no_mangle]\npub extern \"C\" fn \
                          tcg_opt_probe(x: i32) -> i32 { x.wrapping_add(1) }\n";

/// One option compile of a trivial library; returns its output and whether
/// any object was written.
fn option_compile(dir: &Path, options: &[&str], knobs: Option<&[&str]>) -> (Output, bool) {
    option_compile_source(dir, "optp", OPTION_LIB, options, knobs)
}

/// [`option_compile`] of `text` as the crate `stem`.
fn option_compile_source(
    dir: &Path,
    stem: &str,
    text: &str,
    options: &[&str],
    knobs: Option<&[&str]>,
) -> (Output, bool) {
    let out = dir.join(format!(
        "out{}{}",
        if stem == "optp" { "" } else { stem },
        options
            .join("_")
            .replace(['=', '-', '/', '.'], "")
            .chars()
            .take(80)
            .collect::<String>()
    ));
    std::fs::create_dir_all(&out).expect("create option output directory");
    let source = dir.join(format!("{stem}.rs"));
    std::fs::write(&source, text).expect("write option crate");
    let mut command = toolchain_support::rustc_command();
    command.arg(backend_arg());
    if let Some(knobs) = knobs {
        command.arg(toolchain_support::backend_knobs_arg(knobs));
    }
    let output = command
        .args([
            "--target",
            TARGET,
            "-Cpanic=abort",
            "--emit=obj",
            "--out-dir",
        ])
        .arg(&out)
        .args(options)
        .arg(&source)
        .output()
        .expect("spawn trustc");
    let wrote_object = std::fs::read_dir(&out)
        .expect("read option output directory")
        .filter_map(|entry| entry.ok())
        .any(|entry| entry.path().extension().is_some_and(|ext| ext == "o"));
    (output, wrote_object)
}

#[test]
fn unhonoured_codegen_options_are_refused_by_name_before_lowering() {
    darwin_native::require("debuginfo_dwarf_aarch64", &[]);
    let scratch = Scratch::new("refusals");
    let dir = &scratch.0;
    std::fs::write(dir.join("empty.profdata"), b"").expect("write empty profile");
    let profile_use = format!("-Cprofile-use={}", dir.join("empty.profdata").display());
    std::fs::write(dir.join("empty.prof"), b"").expect("write empty sample profile");
    let sample_option = if cfg!(rustc_codegen_sample_profile) {
        "-C"
    } else {
        "-Z"
    };
    let sample_use = format!(
        "{sample_option}profile-sample-use={}",
        dir.join("empty.prof").display()
    );
    let rows: [(&[&str], &str); 18] = [
        (&["-Clto=fat"], "TCG-OPT-LTO"),
        (&["-Clto=thin"], "TCG-OPT-LTO"),
        (&["-Clinker-plugin-lto"], "TCG-OPT-LINKER-PLUGIN-LTO"),
        (&["-Cprofile-generate"], "TCG-OPT-PGO"),
        (&[profile_use.as_str()], "TCG-OPT-PGO"),
        (&[sample_use.as_str()], "TCG-OPT-PGO"),
        (&["-Cinstrument-coverage"], "TCG-OPT-COVERAGE"),
        (&["-Cdebuginfo=full"], "TCG-OPT-DEBUGINFO"),
        // With proof certificates on, every debuginfo level is refused: the
        // certified-object relocation inventory refuses DWARF sections.
        (&["-Cdebuginfo=line-tables-only"], "TCG-OPT-DEBUGINFO"),
        (&["-Cdebuginfo=limited"], "TCG-OPT-DEBUGINFO"),
        (&["-Zsanitizer=address"], "TCG-OPT-SANITIZER"),
        (&["-Zstack-protector=all"], "TCG-OPT-STACK-PROTECTOR"),
        // A target modifier: the sysroot was built without it, so rustc
        // itself refuses the mix unless told to allow it.
        (
            &[
                "-Zbranch-protection=bti",
                "-Cunsafe-allow-abi-mismatch=branch-protection",
            ],
            "TCG-OPT-BRANCH-PROTECTION",
        ),
        (&["-Zinstrument-mcount"], "TCG-OPT-PROFILING-HOOK"),
        // LLVM starts the function with the NOP sled a runtime patcher
        // overwrites; this backend would leave real instructions there.
        (&["-Zpatchable-function-entry=4"], "TCG-OPT-PROFILING-HOOK"),
        (
            &["-Zmin-function-alignment=64"],
            "TCG-OPT-FUNCTION-ALIGNMENT",
        ),
        (&["-Ccode-model=large"], "TCG-OPT-CODE-MODEL"),
        (&["-Cjump-tables=no"], "TCG-OPT-JUMP-TABLES"),
    ];
    for (options, code) in rows {
        let (output, wrote_object) = option_compile(dir, options, None);
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            !output.status.success(),
            "{options:?} must be refused:\n{stderr}"
        );
        assert!(
            stderr.contains(&format!("error: [{code}] rustc_codegen_trust_cg: ")),
            "{options:?} must be refused as [{code}]:\n{stderr}"
        );
        assert!(
            !stderr.contains("[TCG-PROOF-465]") && !stderr.contains("[TCG-MIR-UNSUPPORTED]"),
            "{options:?} must be refused before anything is lowered:\n{stderr}"
        );
        assert!(!wrote_object, "{options:?} wrote an object");
    }
    positive_evidence::record(
        positive_evidence::Evidence::ExpectedRefusal,
        positive_evidence::Certs::On,
    );
}

#[test]
fn honoured_options_note_or_warn_and_another_dwarf_version_is_refused() {
    darwin_native::require("debuginfo_dwarf_aarch64", &["dwarfdump"]);
    let scratch = Scratch::new("verdicts");
    let dir = &scratch.0;
    let knobs: &[&str] = &["no-proof-certs"];

    let (refused, wrote_object) = option_compile(
        dir,
        &["-Cdebuginfo=limited", "-Zdwarf-version=5"],
        Some(knobs),
    );
    let stderr = String::from_utf8_lossy(&refused.stderr);
    assert!(!refused.status.success() && !wrote_object, "{stderr}");
    assert!(
        stderr.contains("error: [TCG-OPT-DWARF-VERSION] rustc_codegen_trust_cg: DWARF version 5"),
        "{stderr}"
    );
    let (full, wrote_object) = option_compile(dir, &["-Cdebuginfo=full"], Some(knobs));
    let stderr = String::from_utf8_lossy(&full.stderr);
    assert!(!full.status.success() && !wrote_object, "{stderr}");
    assert!(
        stderr.contains("error: [TCG-OPT-DEBUGINFO] rustc_codegen_trust_cg: `-C debuginfo=full`"),
        "{stderr}"
    );

    // Honoured with a note or a warning: the compile succeeds and says how.
    for (options, verdict) in [
        (
            &["-Cdebuginfo=limited"][..],
            "note: [TCG-OPT-DEBUGINFO-LINES] rustc_codegen_trust_cg: ",
        ),
        (
            &["-Zthinlto=yes", "-Ccodegen-units=4", "-Copt-level=2"],
            "note: [TCG-OPT-THINLTO-LOCAL] rustc_codegen_trust_cg: ",
        ),
        (
            &["-Cembed-bitcode=yes"],
            "warning: [TCG-OPT-EMBED-BITCODE] rustc_codegen_trust_cg: ",
        ),
        (
            &["-Cllvm-args=-unused-by-trust-cg"],
            "warning: [TCG-OPT-LLVM-ONLY] rustc_codegen_trust_cg: ",
        ),
        (
            &["-Cforce-frame-pointers=yes"],
            "warning: [TCG-OPT-FRAME-POINTERS] rustc_codegen_trust_cg: ",
        ),
        (
            &["-Crelocation-model=static"],
            "note: [TCG-OPT-RELOC-MODEL] rustc_codegen_trust_cg: ",
        ),
    ] {
        let (output, wrote_object) = option_compile(dir, options, Some(knobs));
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            output.status.success() && wrote_object,
            "{options:?} must compile:\n{stderr}"
        );
        assert!(
            stderr.contains(verdict),
            "{options:?} lacks {verdict:?}:\n{stderr}"
        );
    }
    // `-C link-dead-code` on an executable: lowering is demand-driven.
    let (output, wrote_object) = option_compile_source(
        dir,
        "optbin",
        "fn main() { std::process::exit(7) }\n",
        &["-Clink-dead-code"],
        Some(knobs),
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(output.status.success() && wrote_object, "{stderr}");
    assert!(
        stderr.contains("warning: [TCG-OPT-LINK-DEAD-CODE] rustc_codegen_trust_cg: "),
        "{stderr}"
    );
    // `-C lto=off`, the default and a minimum function alignment every
    // AArch64 function already has are the honoured lane: no verdict at all.
    for options in [&["-Clto=off"][..], &[], &["-Zmin-function-alignment=4"]] {
        let (output, wrote_object) = option_compile(dir, options, Some(knobs));
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            output.status.success() && wrote_object,
            "{options:?}:\n{stderr}"
        );
        assert!(!stderr.contains("[TCG-OPT-"), "{options:?}:\n{stderr}");
    }
    // The `limited` compile's object carries verified DWARF.
    let limited = std::fs::read_dir(dir.join("outCdebuginfolimited"))
        .expect("read limited output")
        .filter_map(|entry| entry.ok().map(|entry| entry.path()))
        .find(|path| path.extension().is_some_and(|ext| ext == "o"))
        .expect("limited object");
    let verify = dwarfdump(&["--verify"], &limited);
    assert!(verify.contains("No errors."), "{verify}");
    let info = dwarfdump(&["--debug-info"], &limited);
    assert!(
        info.contains("DW_AT_name\t(\"optp::tcg_opt_probe\")"),
        "{info}"
    );
    positive_evidence::record(
        positive_evidence::Evidence::Compiled,
        positive_evidence::Certs::Off,
    );
}
