#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/host_target.rs"]
mod host_target_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// Integration test: BOUNDED `.flat_map(f)` — `(0..n).flat_map(|x| a..x).sum()` /
// `.count()` / `.fold(init, g)` over a `Range<T>` outer AND a `Range<T>` inner
// (same scalar `T`, non-capturing `f`) — compiled for x86_64 via the
// rustc_codegen_trust_cg bridge, COMPILED, LINKED, and RUN, with exit codes
// checked against the default LLVM backend.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// See `lower_flatmap_bounded_ctor` / `lower_flatmap_bounded_consumer` in
// `src/lib.rs` for the driver this exercises: a DEDICATED two-level nested loop
// that bypasses `emit_chain_next`/`AdapterKind` entirely (their "≤1 item out
// per ≤1 item pulled" contract cannot express flat_map's "0..N items out per 1
// outer pull"). The ctor writes std's own `FlatMap::new` value (`Fuse` =
// `Some(Map { range, f })`, `frontiter`/`backiter` = `None`) into the real
// (rustc-sized) slot, and the driver folds `frontiter`, the outer range and
// `backiter` in std's order, so a value std code built or advanced is driven
// exactly as std drives it. `flatmap_bare_for_loop_still_fails_closed_after_backend_load`
// below pins that the real `FlattenCompat::next` body still does not lower (a
// coverage boundary; a change there is a reviewed edit).

use std::path::{Path, PathBuf};
use std::process::{Command, ExitStatus};
use std::sync::OnceLock;

const TARGET: &str = host_target_support::X86_64_TARGET;

/// `(0..3).flat_map(|x| 0..x).sum()`: x=0 -> {} ; x=1 -> {0} ; x=2 -> {0,1}.
/// Sum = 0 + 0 + (0+1) = 1. A shape the bounded driver admits: the x86-64
/// differential's first case and the canaries' positive control.
const SUM_BASIC_SRC: &str = "fn main() { let s: i64 = (0..std::hint::black_box(3i64)).flat_map(|x| 0..x).sum(); \
                             std::process::exit(s as i32); }";
const SUM_BASIC_EXIT: i32 = 1;

fn ensure_dylib_built() -> PathBuf {
    backend_artifact_support::current_test_backend()
}

fn x86_64_std_available() -> bool {
    toolchain_support::target_std_available(TARGET)
}

fn host_is_x86_64() -> bool {
    cfg!(target_arch = "x86_64")
}

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("rcl2_flatmap_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

fn backend_arg(dylib: &Path) -> std::ffi::OsString {
    let mut s = std::ffi::OsString::from("-Zcodegen-backend=");
    s.push(dylib);
    s
}

fn compile(
    dir: &Path,
    name: &str,
    src: &str,
    backend: Option<&Path>,
    panic: &str,
) -> Result<PathBuf, String> {
    let src_path = dir.join(format!("{name}.rs"));
    std::fs::write(&src_path, src).expect("write source");
    let bin = dir.join(name);

    let mut cmd = toolchain_support::rustc_command();
    cmd.args(["--crate-type", "bin"]);
    if let Some(dylib) = backend {
        cmd.arg(backend_arg(dylib));
        // The `unwind` leg is an execution differential: certified compiles
        // refuse objects with exception tables ([TCG-EH-UNPROVED]), and every
        // x86-64 object compiled under panic=unwind carries them, so that leg
        // compiles without proof certificates. The `abort` leg keeps them.
        if panic == "unwind" {
            cmd.arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]));
        }
    }
    cmd.args(["--target", TARGET])
        .arg(format!("-Cpanic={panic}"))
        .arg("-o")
        .arg(&bin)
        .arg(&src_path);
    let output = cmd.output().expect("spawn rustc");
    if !output.status.success() {
        return Err(String::from_utf8_lossy(&output.stderr).into_owned());
    }
    Ok(bin)
}

fn run_exit_code(bin: &Path) -> i32 {
    Command::new(bin)
        .output()
        .expect("run binary")
        .status
        .code()
        .expect("process exited via signal, not exit code")
}

/// The positive-shape differential: BOUNDED `.flat_map(f)` programs (`Range<T>`
/// outer AND inner, non-capturing `f`) compiled by trust-cg AND LLVM, run, and
/// the exit codes must match each other and the expected value.
#[test]
fn flatmap_bounded_programs_run_and_match_llvm() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("run");

    // (name, source, expected exit code).
    let shapes: &[(&str, &str, i32)] = &[
        ("sum_basic", SUM_BASIC_SRC, SUM_BASIC_EXIT),
        // EMPTY-only: every inner range is empty (`0..0`) regardless of `x` — must
        // never touch the accumulate step.
        (
            "sum_empty_inner",
            "fn main() { let s: i64 = (0..std::hint::black_box(1i64)).flat_map(|x| 0..x).sum(); \
             std::process::exit(s as i32); }",
            0,
        ),
        // EMPTY outer: zero outer pulls at all — `outer_header`'s condition is
        // false on the very first evaluation.
        (
            "sum_empty_outer",
            "fn main() { let s: i64 = (0..std::hint::black_box(0i64)).flat_map(|x| 0..x).sum(); \
             std::process::exit(s as i32); }",
            0,
        ),
        // COUNT: total items across all inner ranges (0 + 1 + 2 = 3) — exercises
        // the item-independent accumulate path.
        (
            "count_basic",
            "fn main() { let c: usize = (0..std::hint::black_box(3i64)).flat_map(|x| 0..x).count(); \
             std::process::exit(c as i32); }",
            3,
        ),
        // ORDER-SENSITIVE fold: `(1..4).flat_map(|x| x*10..x*10+2)` yields, in
        // order, [10,11, 20,21, 30,31]. `fold(0, |a,y| a*7+y)` is order-sensitive —
        // any nested-order bug (outer-reversed, inner-before-full-drain, or
        // acc/outer_next swapped) changes the result. Masked to a byte so the exit
        // code is representable; the differential (vs a genuine LLVM run of the
        // SAME source) is what actually catches a wrong order, not this constant.
        (
            "fold_order_sensitive",
            "fn main() { let r: i64 = (1..std::hint::black_box(4i64)).flat_map(|x| x * 10..x * 10 + 2) \
             .fold(0i64, |a, y| a * 7 + y); std::process::exit(((((r % 256) + 256) % 256) as i32)); }",
            115,
        ),
        // A single outer element with a non-trivial (3-item) inner range: the
        // minimal case that actually enters `inner_body` more than once. Outer
        // `5..6` = {5}; inner `0..(5-2)` = {0,1,2}; sum = 0+1+2 = 3.
        (
            "sum_single_outer_multi_inner",
            "fn main() { let s: i64 = (5..std::hint::black_box(6i64)).flat_map(|x| 0..(x - 2)) \
             .sum(); std::process::exit(s as i32); }",
            3,
        ),
    ];

    for (name, src, expected) in shapes {
        for panic in ["abort", "unwind"] {
            let llvm_bin = compile(&dir, &format!("{name}_{panic}_llvm"), src, None, panic)
                .unwrap_or_else(|e| panic!("LLVM compile of `{name}` ({panic}) failed: {e}"));
            let tcg_bin = compile(
                &dir,
                &format!("{name}_{panic}_tcg"),
                src,
                Some(&dylib),
                panic,
            )
            .unwrap_or_else(|e| panic!("trust-cg compile of `{name}` ({panic}) failed: {e}"));
            let llvm_exit = run_exit_code(&llvm_bin);
            let tcg_exit = run_exit_code(&tcg_bin);
            assert_eq!(
                llvm_exit, *expected,
                "LLVM backend exit code for `{name}` ({panic}) is {llvm_exit}, expected {expected}"
            );
            assert_eq!(
                tcg_exit, llvm_exit,
                "trust-cg exit code for `{name}` ({panic}) is {tcg_exit}, LLVM is {llvm_exit} (must match)"
            );
        }
    }

    let _ = std::fs::remove_dir_all(&dir);
}

fn write_temp_source(stem: &str, contents: &str) -> PathBuf {
    let mut path = std::env::temp_dir();
    path.push(format!(
        "rcl2_flatmap_neg_{}_{}.rs",
        stem,
        std::process::id()
    ));
    std::fs::write(&path, contents).expect("failed to write temp source file");
    path
}

struct BackendRun {
    status: ExitStatus,
    stderr: String,
    /// The canary crate's name (its source file's stem), which the refused
    /// symbols carry.
    crate_name: String,
}

/// The canaries' compile: the host target, the default `panic=unwind`, and
/// no proof certificates. The canaries check that the backend's LOWERING
/// refuses their shapes. Certificates are irrelevant to that and, with them
/// on, the default `panic=unwind` build would be refused anyway on an x86-64
/// host ([TCG-EH-UNPROVED]: every such object carries exception tables), so
/// a canary could pass for the wrong reason.
fn host_backend_command(dylib: &Path, src_path: &Path, out_bin: &Path) -> Command {
    let mut cmd = toolchain_support::rustc_command();
    cmd.arg(backend_arg(dylib))
        .arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]))
        .arg("-o")
        .arg(out_bin)
        .arg(src_path);
    cmd
}

fn run_backend_on_source(stem: &str, src: &str) -> BackendRun {
    let src_path = write_temp_source(stem, src);
    let crate_name = src_path
        .file_stem()
        .and_then(|stem| stem.to_str())
        .expect("UTF-8 source stem")
        .to_string();
    let out_bin = std::env::temp_dir().join(format!(
        "rcl2_flatmap_neg_out_{stem}_{}",
        std::process::id()
    ));
    let dylib = ensure_dylib_built();

    let output = host_backend_command(&dylib, &src_path, &out_bin)
        .output()
        .expect("failed to spawn trustc");

    let _ = std::fs::remove_file(&src_path);
    let _ = std::fs::remove_file(&out_bin);

    BackendRun {
        status: output.status,
        stderr: String::from_utf8_lossy(&output.stderr).into_owned(),
        crate_name,
    }
}

/// The canaries' positive control: `sum_basic`, a shape the bounded driver
/// admits, compiled in the canaries' configuration for the same host and run.
/// A canary's refusal says something about the flat_map gate only when this
/// host compiles the shape the gate admits. `Err` is the reason to skip (the
/// control does not compile here); a control that compiles but computes the
/// wrong value is a miscompile and panics.
fn positive_control() -> Result<(), String> {
    static CONTROL: OnceLock<Result<Result<(), String>, String>> = OnceLock::new();
    let outcome = CONTROL.get_or_init(|| {
        let dylib = ensure_dylib_built();
        let dir = workdir("control");
        let src_path = dir.join("sum_basic_control.rs");
        std::fs::write(&src_path, SUM_BASIC_SRC).expect("write control source");
        let bin = dir.join("sum_basic_control");
        let output = host_backend_command(&dylib, &src_path, &bin)
            .output()
            .expect("failed to spawn trustc");
        let outcome = if output.status.success() {
            let exit = run_exit_code(&bin);
            if exit == SUM_BASIC_EXIT {
                Ok(Ok(()))
            } else {
                Err(format!(
                    "the positive control `sum_basic` compiled for this host and exited \
                     {exit}, expected {SUM_BASIC_EXIT}: a miscompile"
                ))
            }
        } else {
            let stderr = String::from_utf8_lossy(&output.stderr);
            let refusal = stderr
                .lines()
                .find(|line| line.contains("[TCG-") && !line.starts_with("error:"))
                .or_else(|| stderr.lines().find(|line| line.starts_with("error")))
                .unwrap_or("(no diagnostic)")
                .trim()
                .to_string();
            Ok(Err(refusal))
        };
        let _ = std::fs::remove_dir_all(&dir);
        outcome
    });
    match outcome {
        Ok(control) => control.clone(),
        Err(miscompile) => panic!("{miscompile}"),
    }
}

/// `true` when the canary runs; otherwise it prints why it is skipped.
fn canary_runs(canary: &str) -> bool {
    match positive_control() {
        Ok(()) => true,
        Err(refusal) => {
            eprintln!(
                "skipping {canary}: the positive control `sum_basic` does not compile for this \
                 host, so a refusal here would say nothing about the flat_map gate. Control \
                 refusal: {refusal}"
            );
            false
        }
    }
}

/// The canaries' refusal must come from lowering, not from proof
/// promotion: with certificates off neither the exception-table refusal nor
/// any other certificate refusal can fire.
fn assert_not_a_certificate_refusal(stderr: &str) {
    for marker in [
        "TCG-EH-UNPROVED",
        "TCG-PROOF-465",
        "proof promotion rejected",
    ] {
        assert!(
            !stderr.contains(marker),
            "the canary failed for a certificate reason ({marker:?}), not the lowering refusal \
             it guards. stderr: <<<{stderr}>>>"
        );
    }
}

/// A crash or a link failure is not the refusal a canary guards.
fn assert_not_an_incidental_failure(stderr: &str) {
    for marker in ["internal compiler error", "panicked at", "linking with"] {
        assert!(
            !stderr.contains(marker),
            "the canary failed incidentally ({marker:?}), not with the lowering refusal it \
             guards. stderr: <<<{stderr}>>>"
        );
    }
}

/// A terminal canary (`.sum()` over a flat_map shape the bounded driver does
/// not admit): the bridge refuses the canary crate's own `main` because the
/// terminal's chain is unmodeled.
fn assert_terminal_refused_as_unmodeled(run: &BackendRun) {
    let stderr = run.stderr.as_str();
    assert!(
        stderr.contains("[TCG-MIR-UNSUPPORTED]"),
        "expected the [TCG-MIR-UNSUPPORTED] refusal. stderr: <<<{stderr}>>>"
    );
    let mangled_main = format!("{}4main", run.crate_name);
    let path_main = format!("{}::main", run.crate_name);
    assert!(
        stderr
            .lines()
            .any(|line| line.contains("[TCG-ITER-UNMODELED]")
                && (line.contains(&mangled_main) || line.contains(&path_main))),
        "expected [TCG-ITER-UNMODELED] naming `{}::main`. stderr: <<<{stderr}>>>",
        run.crate_name
    );
    assert_common_canary_refusal(stderr);
}

fn assert_common_canary_refusal(stderr: &str) {
    assert_no_backend_load_failure(stderr);
    assert_not_a_certificate_refusal(stderr);
    assert_not_an_incidental_failure(stderr);
}

fn assert_no_backend_load_failure(stderr: &str) {
    let load_failure_markers = [
        "failed to load",
        "could not load",
        "couldn't load",
        "dlopen",
        "image not found",
        "Library not loaded",
    ];
    for marker in &load_failure_markers {
        assert!(
            !stderr.contains(marker),
            "rustc failed to load our backend dylib (matched marker: {marker:?}). stderr: <<<{stderr}>>>"
        );
    }
}

/// COVERAGE CANARY. A bare `for` loop over a `flat_map` reaches the real
/// `<FlattenCompat<Map<Range,F>,Range> as Iterator>::next` body directly (NO
/// `.sum()`/`.fold()`/`.count()` terminal to intercept), and that body does not
/// lower today, so the program fails closed. The bounded ctor writes std's own
/// `FlatMap` layout, so a future change that makes the body lower reads the
/// value std's `FlatMap::new` would have written; this canary still pins the
/// boundary so such a change is a reviewed edit (with its own differential).
#[test]
fn flatmap_bare_for_loop_still_fails_closed_after_backend_load() {
    if !canary_runs("flatmap_bare_for_loop_still_fails_closed_after_backend_load") {
        return;
    }
    let src = r#"
fn main() {
    let mut acc: i64 = 0;
    for y in (0..std::hint::black_box(3i64)).flat_map(|x| 0..x) {
        acc += y;
    }
    std::process::exit(acc as i32);
}
"#;
    let output = run_backend_on_source("bare_for_loop", src);
    let stderr = output.stderr.as_str();
    eprintln!("rustc stderr:\n{stderr}");
    eprintln!("rustc exit: {:?}", output.status);
    assert!(
        !output.status.success(),
        "COVERAGE BOUNDARY MOVED: a bare `for` loop over `.flat_map(..)` (no \
         sum/fold/count terminal) unexpectedly COMPILED, so the real \
         `FlattenCompat::next` body now lowers; review it against std with a \
         differential before updating this canary. stderr: <<<{stderr}>>>"
    );
    assert!(
        stderr.contains("[TCG-MIR-UNSUPPORTED]"),
        "expected the [TCG-MIR-UNSUPPORTED] refusal. stderr: <<<{stderr}>>>"
    );
    // The refused function is the real `FlattenCompat` step the loop reaches:
    // `<Fuse<Map<Range<i64>, main::{closure}>> as FuseImpl<_>>::next`, v0-mangled
    // or demangled, both carrying the canary crate's name.
    assert!(
        stderr.lines().any(|line| {
            ["Fuse", "Map", "Range", "FuseImpl", "next"]
                .iter()
                .all(|part| line.contains(part))
                && line.contains(&output.crate_name)
        }),
        "expected the refusal to name `FuseImpl::next` over `Fuse<Map<Range<_>, {}::main::{{closure}}>>`. \
         stderr: <<<{stderr}>>>",
        output.crate_name
    );
    assert_common_canary_refusal(stderr);
}

/// Composed-adapter canary: `.flat_map(..)` UNDER an outer `.map(..)` — the
/// terminal's self type is `Map<FlatMap<...>, G>`, not itself a bare `FlatMap`,
/// so `resolve_flatmap_bounded` cannot see it — must fail closed (never a wrong
/// sum), whichever stage (the `.map()` ctor over a `FlatMap` inner, or the
/// terminal finding no modeled chain) actually rejects it first.
#[test]
fn flatmap_under_map_fails_closed_after_backend_load() {
    if !canary_runs("flatmap_under_map_fails_closed_after_backend_load") {
        return;
    }
    let src = r#"
fn main() {
    let s: i64 = (0..std::hint::black_box(3i64)).flat_map(|x| 0..x).map(|y| y * 2).sum();
    std::process::exit(s as i32);
}
"#;
    let output = run_backend_on_source("flatmap_under_map", src);
    let stderr = output.stderr.as_str();
    eprintln!("rustc stderr:\n{stderr}");
    eprintln!("rustc exit: {:?}", output.status);
    assert!(
        !output.status.success(),
        "`.flat_map(..).map(..).sum()` unexpectedly compiled — this composed shape is \
         outside `resolve_flatmap_bounded`'s scope and must fail closed, not silently \
         drop the outer `.map()`. stderr: <<<{stderr}>>>"
    );
    assert_terminal_refused_as_unmodeled(&output);
}

/// `.rev()` composed over a bounded flat_map: the terminal's self type is
/// `Rev<FlatMap<...>>`, not itself a bare `FlatMap` — must fail closed, never
/// silently ignore the `.rev()`.
#[test]
fn flatmap_then_rev_fails_closed_after_backend_load() {
    if !canary_runs("flatmap_then_rev_fails_closed_after_backend_load") {
        return;
    }
    let src = r#"
fn main() {
    let s: i64 = (0..std::hint::black_box(3i64)).flat_map(|x| 0..x).rev().sum();
    std::process::exit(s as i32);
}
"#;
    let output = run_backend_on_source("flatmap_then_rev", src);
    let stderr = output.stderr.as_str();
    eprintln!("rustc stderr:\n{stderr}");
    eprintln!("rustc exit: {:?}", output.status);
    assert!(
        !output.status.success(),
        "`.flat_map(..).rev().sum()` unexpectedly compiled — must fail closed, never \
         silently ignore the `.rev()`. stderr: <<<{stderr}>>>"
    );
    assert_terminal_refused_as_unmodeled(&output);
}

/// A CAPTURING closure (`f` closes over a runtime local `k`): `resolve_flatmap_
/// bounded`'s `is_zero_sized_ty(F)` gate must reject it — must fail closed, never
/// silently compute over garbage upvar bytes.
#[test]
fn flatmap_capturing_closure_fails_closed_after_backend_load() {
    if !canary_runs("flatmap_capturing_closure_fails_closed_after_backend_load") {
        return;
    }
    let src = r#"
fn main() {
    let k: i64 = std::hint::black_box(1i64);
    let s: i64 = (0..std::hint::black_box(3i64)).flat_map(move |x| k..x).sum();
    std::process::exit(s as i32);
}
"#;
    let output = run_backend_on_source("flatmap_capturing", src);
    let stderr = output.stderr.as_str();
    eprintln!("rustc stderr:\n{stderr}");
    eprintln!("rustc exit: {:?}", output.status);
    assert!(
        !output.status.success(),
        "a CAPTURING flat_map closure unexpectedly compiled — must fail closed. \
         stderr: <<<{stderr}>>>"
    );
    assert_terminal_refused_as_unmodeled(&output);
}

/// A non-Range inner (`Vec<T>` via `vec![x, x]`): `range_index_ty(U)` must
/// reject it — must fail closed.
#[test]
fn flatmap_non_range_inner_fails_closed_after_backend_load() {
    if !canary_runs("flatmap_non_range_inner_fails_closed_after_backend_load") {
        return;
    }
    let src = r#"
fn main() {
    let s: i64 = (0..std::hint::black_box(3i64)).flat_map(|x| vec![x, x]).sum();
    std::process::exit(s as i32);
}
"#;
    let output = run_backend_on_source("flatmap_non_range_inner", src);
    let stderr = output.stderr.as_str();
    eprintln!("rustc stderr:\n{stderr}");
    eprintln!("rustc exit: {:?}", output.status);
    assert!(
        !output.status.success(),
        "a non-Range flat_map inner (`Vec`) unexpectedly compiled — must fail closed. \
         stderr: <<<{stderr}>>>"
    );
    assert_terminal_refused_as_unmodeled(&output);
}
