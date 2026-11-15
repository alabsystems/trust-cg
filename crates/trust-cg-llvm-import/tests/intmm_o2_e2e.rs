#![cfg(feature = "driver")]

// trust-cg-llvm-import / tests / intmm_o2_e2e.rs
//
// O2 linked-binary regression coverage for the IntMM Initmatrix shape. Each C
// program's clang -O0 LLVM IR is imported, compiled at O2 for this host's
// explicit triple (ELF on AArch64 Linux GNU, Mach-O on AArch64 macOS), linked
// with `cc` and run natively; its stdout must equal the C program's own.
//
// The IR comes from the host `clang` when one is on PATH, and the reference
// binary from that clang. Otherwise (the Linux AArch64 floor host installs
// only GCC) the IR is the committed clang 18.1.3 -O0 output in
// tests/fixtures/intmm_*_clang_o0.ll, whose header must reproduce the C
// source here, and the reference binary comes from the host `cc`. Either way
// the reference stdout must also equal the pinned expected output.
//
// A host clang that defaults to `-fcommon` (Apple clang) spells the programs'
// uninitialized file-scope globals as `common` tentative definitions. The
// importer refuses that linkage by name (trust-ir has none for it), and the
// test requires exactly that refusal before it re-emits the IR, and builds the
// reference, with `-fno-common`.

mod common;

use std::fs;
use std::io;
use std::path::Path;
use std::process::{Command, Stdio};
use std::thread;
use std::time::{Duration, Instant};

use common::{compile_for_host, describe_status, native_host_or_skip, unique_temp_dir};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_llvm_import::{Error, import_text};

const INTMM_INITMATRIX_C: &str = r#"
#include <stdio.h>

#define rowsize 40

long seed;
int ima[rowsize + 1][rowsize + 1];

void Initrand(void) {
    seed = 74755L;
}

int Rand(void) {
    seed = (seed * 1309L + 13849L) & 65535L;
    return (int)seed;
}

void Initmatrix(int m[rowsize + 1][rowsize + 1]) {
    int temp, i, j;
    for (i = 1; i <= rowsize; i++) {
        for (j = 1; j <= rowsize; j++) {
            temp = Rand();
            m[i][j] = temp - (temp / 120) * 120 - 60;
        }
    }
}

int main(void) {
    int first = 1;
    int last = rowsize;
    Initrand();
    Initmatrix(ima);
    printf("%d %d\n", ima[first][first], ima[last][last]);
    return 0;
}
"#;

const INTMM_MAIN_LOOP_C: &str = r#"
#include <stdio.h>

#define rowsize 40

long seed;
int ima[rowsize + 1][rowsize + 1];
int imb[rowsize + 1][rowsize + 1];
int imr[rowsize + 1][rowsize + 1];

void Initrand(void) {
    seed = 74755L;
}

int Rand(void) {
    seed = (seed * 1309L + 13849L) & 65535L;
    return (int)seed;
}

void Initmatrix(int m[rowsize + 1][rowsize + 1]) {
    int temp, i, j;
    for (i = 1; i <= rowsize; i++) {
        for (j = 1; j <= rowsize; j++) {
            temp = Rand();
            m[i][j] = temp - (temp / 120) * 120 - 60;
        }
    }
}

void Innerproduct(int *result, int a[rowsize + 1][rowsize + 1],
                  int b[rowsize + 1][rowsize + 1], int row, int column) {
    int i;
    *result = 0;
    for (i = 1; i <= rowsize; i++) {
        *result += a[row][i] * b[i][column];
    }
}

void Intmm(int run) {
    int i, j;
    Initrand();
    Initmatrix(ima);
    Initmatrix(imb);
    for (i = 1; i <= rowsize; i++) {
        for (j = 1; j <= rowsize; j++) {
            Innerproduct(&imr[i][j], ima, imb, i, j);
        }
    }
    printf("%d\n", imr[run + 1][run + 1]);
}

int main(void) {
    int i;
    for (i = 0; i < 10; i++) {
        Intmm(i);
    }
    return 0;
}
"#;

/// clang 18.1.3 -O0 IR of [`INTMM_INITMATRIX_C`] for aarch64-unknown-linux-gnu.
const INTMM_INITMATRIX_CLANG_O0_LL: &str = include_str!("fixtures/intmm_initmatrix_clang_o0.ll");
/// clang 18.1.3 -O0 IR of [`INTMM_MAIN_LOOP_C`] for aarch64-unknown-linux-gnu.
const INTMM_MAIN_LOOP_CLANG_O0_LL: &str = include_str!("fixtures/intmm_main_loop_clang_o0.ll");

/// The C programs' output (LP64 `long`; identical under clang and GCC).
const INTMM_INITMATRIX_STDOUT: &str = "36 -33\n";
const INTMM_MAIN_LOOP_STDOUT: &str =
    "-6984\n5732\n8656\n-2156\n-3040\n-2684\n-8664\n852\n560\n300\n";

/// Whether a working `clang` is available (the selected developer compiler
/// on Darwin, PATH elsewhere). A compiler that fails `--version` is broken,
/// not absent.
fn clang_available() -> bool {
    #[cfg(target_os = "macos")]
    let mut command = common::native_c_command();
    #[cfg(not(target_os = "macos"))]
    let mut command = Command::new("clang");
    match command.arg("--version").output() {
        Ok(output) if output.status.success() => true,
        Ok(output) => {
            panic!(
                "clang --version failed with {}\nstdout:\n{}\nstderr:\n{}",
                describe_status(output.status),
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr)
            );
        }
        Err(err) if err.kind() == io::ErrorKind::NotFound => false,
        Err(err) => panic!("run clang --version: {err}"),
    }
}

/// Run the C compiler `driver` with `args`, requiring success.
fn run_c_compiler(driver: &str, args: &[&str]) {
    #[cfg(target_os = "macos")]
    let mut command = common::native_c_command();
    #[cfg(not(target_os = "macos"))]
    let mut command = Command::new(driver);
    let output = command
        .args(args)
        .output()
        .unwrap_or_else(|e| panic!("run {driver}: {e}"));
    assert!(
        output.status.success(),
        "{driver} {:?} failed with {}\nstdout:\n{}\nstderr:\n{}",
        args,
        describe_status(output.status),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

/// The C source embedded in a committed fixture's `; | ` header block.
fn fixture_c_source(fixture: &str) -> String {
    let mut source = String::new();
    for line in fixture
        .lines()
        .skip_while(|line| !line.starts_with("; |"))
        .take_while(|line| line.starts_with("; |"))
    {
        let text = line.strip_prefix("; | ").unwrap_or_else(|| {
            assert_eq!(line, "; |", "malformed fixture source line {line:?}");
            ""
        });
        source.push_str(text);
        source.push('\n');
    }
    source
}

fn link_with_cc(obj_path: &Path, bin_path: &Path) {
    let output = common::native_c_command()
        .arg(obj_path)
        .arg("-o")
        .arg(bin_path)
        .output()
        .expect("run cc");
    assert!(
        output.status.success(),
        "cc failed with {}\nstdout:\n{}\nstderr:\n{}",
        describe_status(output.status),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

fn run_binary(bin_path: &Path) -> Vec<u8> {
    run_binary_with_timeout(bin_path, Duration::from_secs(10))
}

fn run_binary_with_timeout(bin_path: &Path, timeout: Duration) -> Vec<u8> {
    let mut child = Command::new(bin_path)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn linked binary");
    let started = Instant::now();

    loop {
        match child.try_wait().expect("poll linked binary") {
            Some(status) => {
                let output = child.wait_with_output().expect("collect linked binary");
                assert_eq!(
                    output.status, status,
                    "wait status should match completed status"
                );
                assert!(
                    output.status.success(),
                    "linked binary failed with {}\nstdout:\n{}\nstderr:\n{}",
                    describe_status(output.status),
                    String::from_utf8_lossy(&output.stdout),
                    String::from_utf8_lossy(&output.stderr)
                );
                return output.stdout;
            }
            None if started.elapsed() >= timeout => {
                let _ = child.kill();
                let output = child.wait_with_output().expect("collect killed binary");
                panic!(
                    "linked binary timed out after {:?}\nstdout prefix:\n{}\nstderr prefix:\n{}",
                    timeout,
                    String::from_utf8_lossy(&output.stdout),
                    String::from_utf8_lossy(&output.stderr)
                );
            }
            None => thread::sleep(Duration::from_millis(10)),
        }
    }
}

fn assert_o2_linked_binary_matches_clang_stdout(
    test: &str,
    src: &str,
    committed_ll: &str,
    expected_stdout: &str,
    name: &str,
) {
    assert_eq!(
        fixture_c_source(committed_ll),
        src,
        "{name}: the committed clang -O0 fixture was generated from another C source; \
         regenerate it with the command in its header"
    );
    if !native_host_or_skip(test) {
        return;
    }

    let dir = unique_temp_dir(name);
    let c_path = dir.join(format!("{name}.c"));
    let ll_path = dir.join(format!("{name}.ll"));
    let reference_bin = dir.join(format!("{name}.reference"));
    let trust_cg_obj = dir.join(format!("{name}.trust-cg.o"));
    let trust_cg_bin = dir.join(format!("{name}.trust-cg"));
    fs::write(&c_path, src).expect("write C source");
    let c_arg = c_path.to_str().expect("c path utf8");

    let (ll_src, reference_compiler, c_flags): (String, &str, &[&str]) = if clang_available() {
        let emit_ll = |flags: &[&str]| {
            let mut args = vec!["-O0"];
            args.extend_from_slice(flags);
            args.extend([
                "-S",
                "-emit-llvm",
                "-o",
                ll_path.to_str().expect("ll utf8"),
                c_arg,
            ]);
            run_c_compiler("clang", &args);
            fs::read_to_string(&ll_path).expect("read generated ll")
        };
        let default_ll = emit_ll(&[]);
        match import_text(&default_ll, name) {
            Ok(_) => (default_ll, "clang", &[]),
            // A clang that defaults to `-fcommon` (Apple clang for Darwin
            // targets; upstream clang before 11) spells these file-scope
            // tentative definitions `common`, which the importer refuses by
            // name: trust-ir has no linkage for a definition the linker
            // merges by largest size. The same program with `-fno-common`
            // (the upstream default, and the committed fixture's IR) defines
            // each one as an ordinary zero-initialized global, which links
            // the same way in this one-object program.
            Err(Error::Unsupported(reason))
                if reason
                    .starts_with("global `@seed`: linkage `common` (a tentative definition") =>
            {
                assert!(
                    default_ll.contains("@seed = common global i64 0, align 8"),
                    "{name}: the importer refused `common` for a module that does not spell \
                     it: {reason}"
                );
                let no_common_ll = emit_ll(&["-fno-common"]);
                assert!(
                    !no_common_ll.contains(" common global "),
                    "{name}: clang -fno-common still emitted a common global"
                );
                (no_common_ll, "clang", &["-fno-common"])
            }
            Err(error) => panic!("{name}: import of the clang -O0 IR failed: {error}"),
        }
    } else {
        eprintln!(
            "{test}: no clang on PATH; importing the committed clang 18.1.3 -O0 IR \
             (tests/fixtures/{name_stem}_clang_o0.ll) and running the host cc's binary as \
             the reference",
            name_stem = name.trim_end_matches("_o2")
        );
        (committed_ll.to_owned(), "cc", &[])
    };
    let mut reference_args = vec!["-O0"];
    reference_args.extend_from_slice(c_flags);
    reference_args.extend([
        c_arg,
        "-o",
        reference_bin.to_str().expect("reference bin path utf8"),
    ]);
    run_c_compiler(reference_compiler, &reference_args);

    let reference_stdout = run_binary(&reference_bin);
    assert_eq!(
        String::from_utf8_lossy(&reference_stdout),
        expected_stdout,
        "{name}: the {reference_compiler} -O0 reference binary disagrees with the pinned output"
    );
    let object = compile_for_host(&ll_src, name, OptLevel::O2);
    fs::write(&trust_cg_obj, object).expect("write object");
    link_with_cc(&trust_cg_obj, &trust_cg_bin);
    let trust_cg_stdout = run_binary(&trust_cg_bin);

    assert!(
        trust_cg_stdout == reference_stdout,
        "Trust Codegen O2 stdout should match {reference_compiler} for {name}\n{reference_compiler}:\n{}\ntrust-cg:\n{}",
        String::from_utf8_lossy(&reference_stdout),
        String::from_utf8_lossy(&trust_cg_stdout)
    );
}

#[test]
fn intmm_initmatrix_o2_linked_binary_matches_clang_stdout() {
    assert_o2_linked_binary_matches_clang_stdout(
        "intmm_initmatrix_o2_linked_binary_matches_clang_stdout",
        INTMM_INITMATRIX_C,
        INTMM_INITMATRIX_CLANG_O0_LL,
        INTMM_INITMATRIX_STDOUT,
        "intmm_initmatrix_o2",
    );
}

#[test]
fn intmm_main_loop_o2_linked_binary_matches_clang_stdout() {
    assert_o2_linked_binary_matches_clang_stdout(
        "intmm_main_loop_o2_linked_binary_matches_clang_stdout",
        INTMM_MAIN_LOOP_C,
        INTMM_MAIN_LOOP_CLANG_O0_LL,
        INTMM_MAIN_LOOP_STDOUT,
        "intmm_main_loop_o2",
    );
}
