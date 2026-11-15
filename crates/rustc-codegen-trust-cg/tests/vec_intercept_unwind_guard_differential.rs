// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
//
// Native differential: intercepted `Vec` / iterator methods whose user closure
// (or index check) unwinds part-way through must leave exactly the state std's
// own body leaves.
//
// The bridge replaces `Vec::retain` / `retain_mut` / `dedup_by` (which std's
// own `dedup_by_key` body calls) / `resize_with` / `insert`, `collect` into a
// `Vec`, and the by-value drives over an owning `vec::IntoIter` with loops of
// its own. Those loops keep state the caller's MIR cannot see: cursors over a
// partly compacted buffer, the collected Vec's buffer, the moved-in element or
// iterator. std keeps the same state in drop guards (`PanicGuard`,
// `FillGapOnDrop`, `SetLenOnDrop`, its by-value parameters and locals) and
// unwinding runs them. Before those loops had unwind pads, an unwind left the
// Vec's original `len` over a compacted buffer (kept elements twice, removed
// ones back; a `Box` owned by two slots and freed twice), lost the elements a
// `resize_with` generator had already produced, never dropped the element an
// out-of-bounds `insert` owned, and leaked the collected or consumed buffer.
//
// The compactions also drop the elements they remove, and a removed element's
// `Drop` can panic too: std moves its read cursor past the element before
// dropping it, so the element whose drop panicked stays out of the Vec when
// the guard closes the gap (`drop_*`). A drop before the cursor moves puts
// that element back into the Vec and drops it a second time. (`resize_with`'s
// shrink, whose slice drop the bridge refuses in a library under
// `panic=unwind`, is a whole program in `vec_element_semantics_differential`.)
//
// Since the merge of origin/main `7c60cee46` that state is restored by main's
// own mechanisms, which fixed the same clusters: the compaction models' landing
// pad (`emit_vec_compaction_guard_pad`, std's `PanicGuard` / `FillGapOnDrop`),
// `resize_with`'s per-element length store (`SetLenOnDrop`), the out-of-bounds
// `insert`'s element drop (`insert_fail_target_dropping_element`) and the
// by-value terminal's consumed-owner pad (`begin_consumed_owner_drive`); the
// intercept guard is gone. This test keeps measuring the behaviour.
//
// THE GATE. Each fixture library is compiled by LLVM (the oracle) and by the
// bridge at -O0..-O3 under `-Cpanic=unwind`, linked into the same LLVM-built
// driver, and every case runs in its own process: exit status and stdout must
// equal the oracle's. A refusal of a fixture library fails the test. Frontend
// verification and proof certificates are off on both sides.
//
// FALSIFIED (2026-10-05, aarch64-apple-darwin, against the landing's former
// intercept guard, before main's pads replaced it; not repeated on them).
// While a needs-drop element was refused under `panic=unwind`, the bridge
// refused the `drop_*` library by name (then `[TCG-VEC-ELEMENT-DROP]`). With
// each compaction's drop moved back before its cursor advance, and the drop
// still unwinding into the guard, the library COMPILES, and each of the 11
// cases whose removed element's drop panics DIVERGES at -O0..-O3: the element
// is back in the Vec and is dropped twice.
#![cfg(unix)]

#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

const OPT_LEVELS: &[&str] = &["0", "1", "2", "3"];
const RUN_LIMIT: Duration = Duration::from_secs(60);

struct Fixture {
    name: &'static str,
    klib: &'static str,
    kmain: &'static str,
}

#[derive(Debug, PartialEq, Eq)]
struct Outcome {
    code: Option<i32>,
    signal: Option<i32>,
    stdout: String,
}

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!(
        "tcg_vec_unwind_guard_{stem}_{}",
        std::process::id()
    ));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

/// A compiler command for one side, with every backend control variable kept
/// out of the compiler's environment (trustc refuses them).
fn compiler(opt: &str) -> Command {
    let mut cmd = toolchain_support::rustc_command();
    cmd.args(["-Cpanic=unwind", "-Ccodegen-units=1"])
        .arg(format!("-Copt-level={opt}"));
    for (key, _) in std::env::vars_os() {
        let name = key.to_string_lossy();
        if name.starts_with("TCG_") || name.starts_with("TRUST_CG_") {
            cmd.env_remove(key);
        }
    }
    cmd
}

/// Compile `klib.rs` into `lib_dir/libklib.rlib`, with the bridge when
/// `backend` is `Some`; `Err` carries the compiler's stderr.
fn compile_lib(
    dir: &Path,
    lib_dir: &Path,
    opt: &str,
    backend: Option<&Path>,
) -> Result<PathBuf, String> {
    std::fs::create_dir_all(lib_dir).expect("create lib dir");
    let rlib = lib_dir.join("libklib.rlib");
    let mut cmd = compiler(opt);
    cmd.args(["--crate-type=rlib", "--crate-name=klib"]);
    if let Some(dylib) = backend {
        let mut backend_arg = std::ffi::OsString::from("-Zcodegen-backend=");
        backend_arg.push(dylib);
        cmd.arg(backend_arg)
            .arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]));
        cmd.env("XDG_CACHE_HOME", lib_dir.join("cache"));
    }
    let output = cmd
        .arg("-o")
        .arg(&rlib)
        .arg(dir.join("klib.rs"))
        .output()
        .expect("spawn the compiler for klib");
    if output.status.success() {
        Ok(rlib)
    } else {
        Err(String::from_utf8_lossy(&output.stderr).into_owned())
    }
}

/// Link the LLVM-built driver against `rlib`.
fn compile_main(dir: &Path, rlib: &Path, opt: &str) -> PathBuf {
    let bin = rlib.with_file_name("kmain");
    let output = compiler(opt)
        .args(["--crate-name=kmain", "--extern"])
        .arg(format!("klib={}", rlib.display()))
        .arg("-o")
        .arg(&bin)
        .arg(dir.join("kmain.rs"))
        .output()
        .expect("spawn the compiler for kmain");
    assert!(
        output.status.success(),
        "the LLVM-built driver failed to compile: <<<{}>>>",
        String::from_utf8_lossy(&output.stderr)
    );
    bin
}

fn run(bin: &Path, case: &str) -> Outcome {
    let out_path = bin.with_file_name(format!("{case}.stdout"));
    let stdout = std::fs::File::create(&out_path).expect("create stdout capture");
    let mut child = Command::new(bin)
        .arg(case)
        .env_remove("RUST_BACKTRACE")
        .stdin(Stdio::null())
        .stdout(stdout)
        .stderr(Stdio::null())
        .spawn()
        .expect("run compiled driver");
    let started = Instant::now();
    let status = loop {
        if let Some(status) = child.try_wait().expect("poll compiled driver") {
            break Some(status);
        }
        if started.elapsed() > RUN_LIMIT {
            let _ = child.kill();
            let _ = child.wait();
            break None;
        }
        std::thread::sleep(Duration::from_millis(10));
    };
    let stdout = std::fs::read_to_string(&out_path).expect("read stdout capture");
    let Some(status) = status else {
        return Outcome {
            code: None,
            signal: None,
            stdout: format!("{stdout}timed out after {RUN_LIMIT:?}"),
        };
    };
    Outcome {
        code: status.code(),
        signal: std::os::unix::process::ExitStatusExt::signal(&status),
        stdout,
    }
}

/// Run `fixture` at every opt level; returns the number of cases compared.
fn assert_fixture(test: &str, fixture: &Fixture) -> usize {
    let dylib = backend_artifact_support::current_test_backend();
    let mut compared = 0;
    let mut failures = Vec::new();
    for &opt in OPT_LEVELS {
        let dir = workdir(&format!("{}_O{opt}", fixture.name));
        std::fs::write(dir.join("klib.rs"), fixture.klib).expect("write klib");
        std::fs::write(dir.join("kmain.rs"), fixture.kmain).expect("write kmain");
        let oracle_lib = compile_lib(&dir, &dir.join("llvm"), opt, None)
            .unwrap_or_else(|e| panic!("{test} -O{opt}: the LLVM oracle failed: <<<{e}>>>"));
        let oracle = compile_main(&dir, &oracle_lib, opt);
        let bridge_lib = match compile_lib(&dir, &dir.join("bridge"), opt, Some(&dylib)) {
            Ok(rlib) => rlib,
            Err(stderr) => {
                failures.push(format!(
                    "-O{opt}: the bridge refused the library, so no case ran: <<<{}>>>",
                    stderr.lines().take(8).collect::<Vec<_>>().join(" | ")
                ));
                continue;
            }
        };
        let bridge = compile_main(&dir, &bridge_lib, opt);
        let listing = run(&oracle, "--list");
        assert_eq!(
            listing.code,
            Some(0),
            "{test}: the oracle could not list its cases"
        );
        for case in listing.stdout.lines().filter(|line| !line.is_empty()) {
            let want = run(&oracle, case);
            assert!(
                want.code == Some(0) && want.stdout.contains("panicked="),
                "{test} -O{opt} {case}: the LLVM oracle did not finish the case: {want:?}"
            );
            let got = run(&bridge, case);
            compared += 1;
            if got != want {
                failures.push(format!("-O{opt} {case}: LLVM {want:?} vs bridge {got:?}"));
            }
        }
        let _ = std::fs::remove_dir_all(&dir);
    }
    assert!(
        failures.is_empty(),
        "{test}: {} failure(s). A Vec that kept its original length over a compacted \
         buffer, lost the elements a generator produced, a missing element drop, a \
         nonzero net heap block count or a crash where LLVM exits 0 is unwind state the \
         intercept did not restore the way std's guard does: {failures:#?}",
        failures.len()
    );
    eprintln!("{test}: {compared} case run(s) matched LLVM");
    compared
}

#[test]
fn copy_element_intercepts_unwind_like_std() {
    const TEST: &str = "copy_element_intercepts_unwind_like_std";
    if toolchain_support::skip_without_backend_knobs(TEST) {
        return;
    }
    let compared = assert_fixture(
        TEST,
        &Fixture {
            name: "copy",
            klib: include_str!("support/vec_intercept_unwind/copy_klib.rs"),
            kmain: include_str!("support/vec_intercept_unwind/copy_kmain.rs"),
        },
    );
    assert_eq!(
        compared,
        14 * OPT_LEVELS.len(),
        "{TEST}: the case denominator changed"
    );
}

#[test]
fn insert_past_the_end_drops_its_element_like_std() {
    const TEST: &str = "insert_past_the_end_drops_its_element_like_std";
    if toolchain_support::skip_without_backend_knobs(TEST) {
        return;
    }
    let compared = assert_fixture(
        TEST,
        &Fixture {
            name: "insert",
            klib: include_str!("support/vec_intercept_unwind/insert_klib.rs"),
            kmain: include_str!("support/vec_intercept_unwind/insert_kmain.rs"),
        },
    );
    assert_eq!(
        compared,
        6 * OPT_LEVELS.len(),
        "{TEST}: the case denominator changed"
    );
}

#[test]
fn box_compactions_leave_each_box_in_one_slot() {
    const TEST: &str = "box_compactions_leave_each_box_in_one_slot";
    if toolchain_support::skip_without_backend_knobs(TEST) {
        return;
    }
    let compared = assert_fixture(
        TEST,
        &Fixture {
            name: "box",
            klib: include_str!("support/vec_intercept_unwind/box_klib.rs"),
            kmain: include_str!("support/vec_intercept_unwind/box_kmain.rs"),
        },
    );
    assert_eq!(
        compared,
        2 * OPT_LEVELS.len(),
        "{TEST}: the case denominator changed"
    );
}

#[test]
fn removed_element_drops_unwind_like_std() {
    const TEST: &str = "removed_element_drops_unwind_like_std";
    if toolchain_support::skip_without_backend_knobs(TEST) {
        return;
    }
    let compared = assert_fixture(
        TEST,
        &Fixture {
            name: "drop",
            klib: include_str!("support/vec_intercept_unwind/drop_klib.rs"),
            kmain: include_str!("support/vec_intercept_unwind/drop_kmain.rs"),
        },
    );
    assert_eq!(
        compared,
        17 * OPT_LEVELS.len(),
        "{TEST}: the case denominator changed"
    );
}
