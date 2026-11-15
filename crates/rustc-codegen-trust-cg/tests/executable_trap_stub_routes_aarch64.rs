#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[path = "support/darwin_native_prerequisites.rs"]
mod darwin_native_prerequisites;
#[path = "support/host_target.rs"]
mod host_target_support;
#[path = "support/positive_evidence.rs"]
mod positive_evidence;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// Integration test: in an EXECUTABLE crate the bridge never replaces a body it
// had to lower with a trapping stub. Both trap-stub routes of `failure_route`
// (`is_dead_std_iterator_reduction_body`, `is_dead_intercepted_heap_alloc_glue`)
// assume the body is dead because its call sites were intercepted; an
// executable lowers on demand, so a body that reaches the failure route there
// has a live reference, and a stub under it is a runtime trap instead of a
// compile-time refusal. The fix (`crate_is_executable_only` in
// `failure_route`) gives such a body the deferred verdict, which refuses the
// compile naming it. Library crate types keep the stubs.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// One test per arm, each a measured live instance (aarch64-apple-darwin,
// 2026-09-30, the same backend with the gate removed; the current
// dead-iterator rows aarch64-unknown-linux-gnu, 2026-10-03), plus guards for
// instances that now lower. Every row accepts
// either a fail-closed refusal or a binary that matches LLVM, since lowering
// the body for real is a correct way to pass it; a binary that disagrees (the
// trap stub's SIGTRAP, exit 133) is the defect.
//
// * `dead_std_iterator_body_fails_closed_aarch64` — the dead-iterator arm
//   (`is_dead_std_iterator_reduction_body`). `std::iter::repeat_n(v, 7)
//   .take(n).sum()` (and `slice.iter().cycle().take(n).sum()`) at -O2/-O3:
//   `Take::sum` inlines to a surviving call of `<Take<I> as
//   SpecTake>::spec_fold`, which the bridge's `spec_fold` route steps aside
//   from (`RepeatN` / `Cycle` is neither a source `resolve_iter_chain` models
//   nor one `is_std_generator_source_ty` sends to core's real bodies), so the
//   general path lowers its caller and references the `spec_fold` body:
//   unlowerable, and on the dead-iterator list (`ends_with("spec_fold")`).
//   With the gate it is refused naming that body; MUTATION RESULTS below
//   records the run without it.
//
// * `generator_source_take_reductions_never_trap_aarch64` — this arm's
//   original rows, `std::iter::repeat(v).take(n).sum()` and
//   `successors(..).take(n).sum()` at -O2/-O3. Since f09e5fa9c (wasm32 round
//   7) `is_std_generator_source_ty` sends `Repeat` / `Successors` chains to
//   core's real bodies, which lower, so these rows build and match LLVM and no
//   longer reach the failure route (bisected on Linux AArch64, 2026-10-03:
//   refused at its parent 3af946d8f, built and matched at f09e5fa9c). They stay
//   as a guard that the shape never traps again, as the reversed-range rows
//   do; the two rows above replaced them as the gate's live witnesses.
//
// * `range_inclusive_rev_reductions_never_trap_aarch64` — the instance that
//   found this gate: `(1..=n).rev().sum()` / `.product()` at -O2/-O3 inlined
//   to a surviving `RangeInclusiveIteratorImpl::spec_try_rfold` call whose
//   body did not lower (`[TCG-RET-UNBOUND]`) and matched the `try_rfold` arm;
//   without the gate it linked and died with SIGTRAP where LLVM prints 55 /
//   3628800. The bridge now drives the reversed inclusive walk itself (std's
//   `spec_next_back`), so these rows build and match and no longer reach the
//   failure route; they stay as a guard that the shape never traps again.
//   `rev_range_inclusive_fold_differential.rs` is the strict (must-match)
//   differential for the reversed walk. A plain `(1..n).rev().sum()`
//   control must build and match LLVM.
//
// * `dyn_heap_glue_drop_fails_closed_aarch64` — the heap-glue arm. A
//   `Box<dyn Trait>` owning a `Vec<u8>` / `String`, dropped at -O0. The drop
//   goes through the vtable's `drop_in_place` slot, which no bridge
//   interception sees, into `drop_glue::<Vec<u8>>` / `drop_glue::<String>`:
//   unlowerable, and on the dead-heap-glue list. Without the gate both linked
//   and died with SIGTRAP (exit 133) at the drop where LLVM prints 3. That
//   glue now LOWERS, so this row no longer reaches the gate: on this base
//   both `normalize_real_collection_drop_glue` (Vec/String at rustc's real
//   header layout) and `heap_image_glue` admit it — measured on d42238c92
//   and again on 16a86a97b without `heap_image_glue`, all four rows already
//   built and matched, so this row does not witness `heap_image_glue`
//   specifically (`dyn_heap_glue_differential_aarch64.rs` does, with a heap
//   ledger). At -O0 it must build and match LLVM (a refusal there is the
//   capability regressing — the one exception to the refuse-or-match rule
//   above); at -O2 a fail-closed refusal is still accepted (measured: both
//   -O2 rows build and match too). A binary that disagrees is the defect at
//   either level.
//   The dead-iterator rows are the ones that keep the gate's SIGTRAP mutation
//   check.
//
// Executes on an AArch64 host (Apple or Linux). The bridge side passes
// `no-proof-certs`: with per-compile proof certificates on, AArch64 refuses
// every program with `[TCG-PROOF-465]`, unrelated to these routes.

use std::ffi::OsString;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

const TARGET: &str = host_target_support::AARCH64_TARGET;

fn host_is_aarch64() -> bool {
    cfg!(target_arch = "aarch64") && host_target_support::HOST_OS_SUPPORTED
}

/// The shared guard returns: `true` when the caller must return (reason printed).
fn skip(test: &str) -> bool {
    if !host_is_aarch64() {
        eprintln!("{test}: skipping: the AArch64 run requires an AArch64 Linux or macOS host");
        return true;
    }
    #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
    darwin_native_prerequisites::require(test, &[]);
    #[cfg(not(all(target_os = "macos", target_arch = "aarch64")))]
    if toolchain_support::skip_without_backend_knobs(test) {
        return true;
    }
    if !toolchain_support::target_std_available(TARGET) {
        eprintln!("{test}: skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return true;
    }
    false
}

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("tcg_exe_trap_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

fn backend_arg(dylib: &Path) -> OsString {
    let mut s = OsString::from("-Zcodegen-backend=");
    s.push(dylib);
    s
}

fn try_compile(
    dir: &Path,
    name: &str,
    src: &str,
    backend: Option<&Path>,
    opt: &str,
) -> (Output, PathBuf) {
    let src_path = dir.join(format!("{name}.rs"));
    std::fs::write(&src_path, src).expect("write source");
    let bin = dir.join(name);
    let mut cmd = toolchain_support::rustc_command();
    cmd.args(["--crate-type", "bin"]);
    if let Some(dylib) = backend {
        cmd.arg(backend_arg(dylib));
        cmd.arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]));
    }
    cmd.args(["--target", TARGET, "-Cpanic=abort", "-Coverflow-checks=off"])
        .arg(format!("-Copt-level={opt}"))
        .arg("-o")
        .arg(&bin)
        .arg(&src_path);
    let output = cmd.output().expect("spawn rustc");
    (output, bin)
}

/// Run `bin`: its stdout, or why it did not exit 0 (a signal is named, so a
/// reachable trap stub reads as `signal 5` rather than a bare failure).
fn run(bin: &Path) -> Result<String, String> {
    let out = Command::new(bin).output().expect("run binary");
    if out.status.success() {
        return Ok(String::from_utf8_lossy(&out.stdout).trim().to_owned());
    }
    #[cfg(unix)]
    {
        use std::os::unix::process::ExitStatusExt;
        if let Some(signal) = out.status.signal() {
            return Err(format!("killed by signal {signal}"));
        }
    }
    Err(format!("{:?}", out.status))
}

/// Compile `src` with LLVM at `opt`, run it, and assert it prints `expected`,
/// so a corrupted oracle cannot make a wrong value agree.
fn assert_oracle(dir: &Path, name: &str, src: &str, opt: &str, expected: &str) {
    let (out, bin) = try_compile(dir, &format!("{name}_o{opt}_llvm"), src, None, opt);
    assert!(
        out.status.success(),
        "LLVM compile of `{name}` failed at -O{opt}: <<<{}>>>",
        String::from_utf8_lossy(&out.stderr)
    );
    assert_eq!(
        run(&bin).as_deref(),
        Ok(expected),
        "LLVM oracle for `{name}` at -O{opt}"
    );
}

fn stderr_tail(output: &Output) -> String {
    String::from_utf8_lossy(&output.stderr)
        .lines()
        .rev()
        .take(8)
        .collect::<Vec<_>>()
        .join(" | ")
}

/// The trust-cg compile of `src` at `opt`: `Ok(None)` for a fail-closed
/// refusal, `Ok(Some(run))` for a binary (with how it ran), `Err` for a
/// refusal that is not a fail-closed verdict.
fn bridge_verdict(
    dir: &Path,
    dylib: &Path,
    name: &str,
    src: &str,
    opt: &str,
) -> Result<Option<Result<String, String>>, String> {
    let (output, bin) = try_compile(dir, &format!("{name}_o{opt}_tcg"), src, Some(dylib), opt);
    if output.status.success() || bin.exists() {
        return Ok(Some(if bin.exists() {
            run(&bin)
        } else {
            Err("compile reported success but wrote no binary".to_owned())
        }));
    }
    if String::from_utf8_lossy(&output.stderr).contains("failing closed") {
        Ok(None)
    } else {
        Err(stderr_tail(&output))
    }
}

/// `(name, source, LLVM's stdout)`. The `#[inline(never)]` callee and the
/// `black_box` argument keep the reduction a real call over a runtime bound.
const REV_INCLUSIVE: [(&str, &str, &str); 2] = [
    (
        "rev_incl_sum",
        "use std::hint::black_box;\n\
         #[inline(never)] fn f(n: u64) -> u64 { (1..=n).rev().sum() }\n\
         fn main() { println!(\"{}\", f(black_box(10))); }\n",
        "55",
    ),
    (
        "rev_incl_product",
        "use std::hint::black_box;\n\
         #[inline(never)] fn f(n: u64) -> u64 { (1..=n).rev().product() }\n\
         fn main() { println!(\"{}\", f(black_box(10))); }\n",
        "3628800",
    ),
];

const REV_CONTROL: (&str, &str, &str) = (
    "rev_excl_sum",
    "use std::hint::black_box;\n\
     #[inline(never)] fn f(n: u64) -> u64 { (1..n).rev().sum() }\n\
     fn main() { println!(\"{}\", f(black_box(10))); }\n",
    "45",
);

/// What `refuse_or_match` saw: the failures, and how every row closed.
#[derive(Default)]
struct Outcomes {
    failures: Vec<String>,
    /// LLVM oracle binaries built, run and checked.
    llvm_native: usize,
    /// trust-cg binaries built, run, and matching LLVM.
    cg_native: usize,
    /// trust-cg fail-closed refusals.
    cg_refused: usize,
}

/// Compile and run every row of `rows` at each of `opts`; a row passes when
/// the bridge refuses it fail-closed or builds a binary that prints what LLVM
/// prints. Returns the failures and the per-row outcome counts.
fn refuse_or_match(
    dir: &Path,
    dylib: &Path,
    rows: &[(&str, &str, &str)],
    opts: &[&str],
    what: &str,
) -> Outcomes {
    let mut outcomes = Outcomes::default();
    for opt in opts {
        for (name, src, expected) in rows {
            assert_oracle(dir, name, src, opt, expected);
            outcomes.llvm_native += 1;
            match bridge_verdict(dir, dylib, name, src, opt) {
                Ok(None) => outcomes.cg_refused += 1,
                Ok(Some(Ok(out))) if out == *expected => outcomes.cg_native += 1,
                Ok(Some(ran)) => outcomes.failures.push(format!(
                    "-O{opt} `{name}`: trust-cg produced a binary that disagrees with LLVM \
                     (run: {ran:?}; LLVM prints {expected}) — {what}"
                )),
                Err(tail) => outcomes.failures.push(format!(
                    "-O{opt} `{name}`: trust-cg refused, but not with a fail-closed verdict: \
                     <<<{tail}>>>"
                )),
            }
        }
    }
    outcomes
}

#[test]
fn range_inclusive_rev_reductions_never_trap_aarch64() {
    if skip("range_inclusive_rev_reductions_never_trap_aarch64") {
        return;
    }
    let dylib = backend_artifact_support::current_test_backend();
    let dir = workdir("rev");
    let Outcomes {
        mut failures,
        mut llvm_native,
        mut cg_native,
        cg_refused,
    } = refuse_or_match(
        &dir,
        &dylib,
        &REV_INCLUSIVE,
        &["2", "3"],
        "a reversed inclusive reduction reached a body the bridge could not lower",
    );

    for opt in ["2", "3"] {
        let (name, src, expected) = REV_CONTROL;
        assert_oracle(&dir, name, src, opt, expected);
        llvm_native += 1;
        match bridge_verdict(&dir, &dylib, name, src, opt) {
            Ok(Some(Ok(out))) if out == expected => cg_native += 1,
            other => failures.push(format!(
                "-O{opt} control `{name}`: a plain reversed Range reduction must build and \
                 print {expected}; got {other:?}"
            )),
        }
    }

    let _ = std::fs::remove_dir_all(&dir);
    assert!(
        failures.is_empty(),
        "{} reversed-range row(s) failed:\n  {}",
        failures.len(),
        failures.join("\n  ")
    );
    // Every row closed: the four reversed-inclusive cells refused or matched,
    // and the two controls matched.
    assert_eq!(
        cg_native + cg_refused,
        6,
        "every reversed-range row must close"
    );
    eprintln!(
        "EXECUTABLE_TRAP_STUB_RANGE refusals={cg_refused} llvm_native={llvm_native} \
         cg_native={cg_native}"
    );
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}

/// `(name, source, LLVM's stdout)`: a `take(n)` reduction over a source or
/// adapter the bridge does not model, whose O2/O3 `SpecTake::spec_fold` call
/// survives. Without the executable gate both rows link a trap stub for that
/// body and die with SIGTRAP (MUTATION RESULTS below).
const DEAD_ITER_BODY: [(&str, &str, &str); 2] = [
    (
        "repeat_n_take_sum",
        "use std::hint::black_box;\n\
         #[inline(never)] fn f(v: u64, n: usize) -> u64 { std::iter::repeat_n(v, 7).take(n).sum() }\n\
         fn main() { println!(\"{}\", f(black_box(3), black_box(4))); }\n",
        "12",
    ),
    (
        "cycle_take_sum",
        "use std::hint::black_box;\n\
         #[inline(never)] fn f(v: &[u64], n: usize) -> u64 { v.iter().cycle().take(n).sum() }\n\
         fn main() { println!(\"{}\", f(black_box(&[1, 2, 3]), black_box(7))); }\n",
        "13",
    ),
];

/// `(name, source, LLVM's stdout)`: a `take(n)` reduction over one of core's
/// generator sources. These were the dead-iterator rows until
/// `is_std_generator_source_ty` sent such chains to core's real bodies; they
/// now build and match LLVM.
const GENERATOR_TAKE: [(&str, &str, &str); 2] = [
    (
        "repeat_take_sum",
        "use std::hint::black_box;\n\
         #[inline(never)] fn f(v: u64, n: usize) -> u64 { std::iter::repeat(v).take(n).sum() }\n\
         fn main() { println!(\"{}\", f(black_box(3), black_box(4))); }\n",
        "12",
    ),
    (
        "successors_take_sum",
        "use std::hint::black_box;\n\
         #[inline(never)] fn f(n: usize) -> u64 { \
         std::iter::successors(Some(1u64), |x| Some(x * 2)).take(n).sum() }\n\
         fn main() { println!(\"{}\", f(black_box(5))); }\n",
        "31",
    ),
];

#[test]
fn dead_std_iterator_body_fails_closed_aarch64() {
    if skip("dead_std_iterator_body_fails_closed_aarch64") {
        return;
    }
    let dylib = backend_artifact_support::current_test_backend();
    let dir = workdir("dead_iter");
    let Outcomes {
        failures,
        llvm_native,
        cg_native,
        cg_refused,
    } = refuse_or_match(
        &dir,
        &dylib,
        &DEAD_ITER_BODY,
        &["2", "3"],
        "a reduction reached a dead-classified iterator body the bridge could not lower",
    );
    let _ = std::fs::remove_dir_all(&dir);
    assert!(
        failures.is_empty(),
        "{} dead-iterator-body row(s) failed:\n  {}",
        failures.len(),
        failures.join("\n  ")
    );
    assert_eq!(
        cg_native + cg_refused,
        4,
        "every dead-iterator-body row must close"
    );
    eprintln!(
        "EXECUTABLE_TRAP_STUB_DEAD_ITER rows=4 llvm_native={llvm_native} cg_native={cg_native} \
         cg_refused={cg_refused}"
    );
    positive_evidence::record(
        if cg_native == 0 {
            positive_evidence::Evidence::ExpectedRefusal
        } else {
            positive_evidence::Evidence::NativeRun
        },
        positive_evidence::Certs::Off,
    );
}

#[test]
fn generator_source_take_reductions_never_trap_aarch64() {
    if skip("generator_source_take_reductions_never_trap_aarch64") {
        return;
    }
    let dylib = backend_artifact_support::current_test_backend();
    let dir = workdir("generator_take");
    let Outcomes {
        failures,
        llvm_native,
        cg_native,
        cg_refused,
    } = refuse_or_match(
        &dir,
        &dylib,
        &GENERATOR_TAKE,
        &["2", "3"],
        "a generator-source take reduction reached a body the bridge could not lower",
    );
    let _ = std::fs::remove_dir_all(&dir);
    assert!(
        failures.is_empty(),
        "{} generator-source take row(s) failed:\n  {}",
        failures.len(),
        failures.join("\n  ")
    );
    assert_eq!(
        cg_native + cg_refused,
        4,
        "every generator-source take row must close"
    );
    eprintln!(
        "EXECUTABLE_TRAP_STUB_GENERATOR_TAKE rows=4 llvm_native={llvm_native} \
         cg_native={cg_native} cg_refused={cg_refused}"
    );
    positive_evidence::record(
        if cg_native == 0 {
            positive_evidence::Evidence::ExpectedRefusal
        } else {
            positive_evidence::Evidence::NativeRun
        },
        positive_evidence::Certs::Off,
    );
}

/// `(name, source, LLVM's stdout)`: a heap-owning value behind `Box<dyn Trait>`,
/// dropped through the vtable.
const DYN_HEAP_DROP: [(&str, &str, &str); 2] = [
    (
        "dyn_vec_drop",
        "use std::hint::black_box;\n\
         trait Len { fn len_of(&self) -> usize; }\n\
         impl Len for Vec<u8> { fn len_of(&self) -> usize { self.len() } }\n\
         fn main() { let b: Box<dyn Len> = Box::new(vec![1u8, 2, black_box(3)]); \
         let n = b.len_of(); drop(b); println!(\"{n}\"); }\n",
        "3",
    ),
    (
        "dyn_string_drop",
        "use std::hint::black_box;\n\
         trait Len { fn len_of(&self) -> usize; }\n\
         impl Len for String { fn len_of(&self) -> usize { self.len() } }\n\
         fn main() { let b: Box<dyn Len> = Box::new(String::from(black_box(\"abc\"))); \
         println!(\"{}\", b.len_of()); }\n",
        "3",
    ),
];

#[test]
fn dyn_heap_glue_drop_fails_closed_aarch64() {
    if skip("dyn_heap_glue_drop_fails_closed_aarch64") {
        return;
    }
    let dylib = backend_artifact_support::current_test_backend();
    let dir = workdir("dyn_heap");
    // -O0: the vtable's drop glue lowers (heap_image_glue), so a refusal there
    // is the capability regressing; -O2 may still refuse in the trait method.
    let o0 = refuse_or_match(
        &dir,
        &dylib,
        &DYN_HEAP_DROP,
        &["0"],
        "a vtable drop reached heap glue the bridge could not lower",
    );
    let o2 = refuse_or_match(
        &dir,
        &dylib,
        &DYN_HEAP_DROP,
        &["2"],
        "a vtable drop reached heap glue the bridge could not lower",
    );
    let mut failures = o0.failures;
    if o0.cg_refused != 0 {
        failures.push(format!(
            "-O0: trust-cg refused {} of {} row(s), but the vtable's drop glue lowers at -O0 \
             (heap_image_glue) and every -O0 row must build and print what LLVM prints",
            o0.cg_refused,
            DYN_HEAP_DROP.len()
        ));
    }
    failures.extend(o2.failures);
    let llvm_native = o0.llvm_native + o2.llvm_native;
    let native = o0.cg_native + o2.cg_native;
    let refused = o0.cg_refused + o2.cg_refused;
    let _ = std::fs::remove_dir_all(&dir);
    assert!(
        failures.is_empty(),
        "{} dyn heap-drop row(s) failed:\n  {}",
        failures.len(),
        failures.join("\n  ")
    );
    assert_eq!(
        native + refused,
        4,
        "every guarded heap-drop row must close"
    );
    assert_eq!(
        llvm_native, 4,
        "every guarded heap-drop row must run its LLVM oracle"
    );
    eprintln!(
        "EXECUTABLE_TRAP_STUB_DYN rows=4 llvm_native={llvm_native} cg_native={native} \
         cg_refused={refused}"
    );
    positive_evidence::record(
        if native == 0 {
            positive_evidence::Evidence::ExpectedRefusal
        } else {
            positive_evidence::Evidence::NativeRun
        },
        positive_evidence::Certs::Off,
    );
}

/// Compile `src` as a STATICLIB (the crate type that keeps the trap stubs)
/// through the bridge at `opt`: `Ok(())` when it compiled, `Err(stderr)`
/// otherwise.
fn compile_library(
    dir: &Path,
    dylib: &Path,
    name: &str,
    src: &str,
    opt: &str,
) -> Result<(), String> {
    let src_path = dir.join(format!("{name}.rs"));
    std::fs::write(&src_path, src).expect("write source");
    let lib = dir.join(format!("lib{name}_o{opt}.a"));
    let output = toolchain_support::rustc_command()
        .args(["--crate-type", "staticlib"])
        .arg(backend_arg(dylib))
        .arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]))
        .args(["--target", TARGET, "-Cpanic=abort"])
        .arg(format!("-Copt-level={opt}"))
        .arg("-o")
        .arg(&lib)
        .arg(&src_path)
        .output()
        .expect("spawn rustc");
    let _ = std::fs::remove_file(&lib);
    if output.status.success() {
        Ok(())
    } else {
        Err(String::from_utf8_lossy(&output.stderr).into_owned())
    }
}

/// `(name, source, opt levels, refusal)`: a library function that reaches a
/// reversed `RangeInclusive` fold the bridge does not drive (a `&mut` range,
/// `by_ref()`, a `char` range), and the controls it does drive.
const LIBRARY_STUB_ROWS: [(&str, &str, &[&str], Option<&str>); 5] = [
    (
        "rfold_mut_ref",
        "#[no_mangle] pub extern \"C\" fn f(a: u32, b: u32) -> u64 { \
         let mut r = a..=b; (&mut r).rfold(5u64, |c, x| c.wrapping_mul(9) ^ x as u64) }\n",
        &["2", "3"],
        Some("[TCG-ITER-STUB-REACHABLE]"),
    ),
    (
        "by_ref_rev_sum",
        "#[no_mangle] pub extern \"C\" fn f(a: u32, b: u32) -> u32 { \
         let mut r = a..=b; r.next(); r.by_ref().rev().sum::<u32>() ^ r.is_empty() as u32 }\n",
        &["2"],
        Some("[TCG-ITER-STUB-REACHABLE]"),
    ),
    (
        "char_range_fold",
        "#[no_mangle] pub extern \"C\" fn f(a: u32, b: u32) -> u64 { \
         let lo = char::from_u32(0xD7F0 + a % 32).unwrap_or('a'); \
         let hi = char::from_u32(0xE000 + b % 20).unwrap_or('z'); \
         (lo..=hi).rev().fold(3u64, |c, x| c.wrapping_mul(131).wrapping_add(x as u64)) }\n",
        &["2"],
        Some("[TCG-ITER-STUB-REACHABLE]"),
    ),
    (
        "rev_fold_control",
        "#[no_mangle] pub extern \"C\" fn f(a: u64, b: u64) -> u64 { \
         (a..=b).rev().fold(0u64, |c, x| c.wrapping_mul(10).wrapping_add(x)) }\n",
        &["0", "2", "3"],
        None,
    ),
    (
        "rev_sum_control",
        "#[no_mangle] pub extern \"C\" fn f(a: u64, b: u64) -> u64 { (a..=b).rev().sum() }\n",
        &["0", "2"],
        None,
    ),
];

/// A LIBRARY keeps the dead-iterator trap stubs (`failure_route`), on the
/// premise that every caller of the stubbed body was intercepted. When this
/// crate's own code reaches the stub through emitted calls the premise is
/// false: the reversed `RangeInclusive` folds below inline (`-O2`/`-O3`) to a
/// live `spec_try_rfold` into a `NeverShortCircuit`, whose std body does not
/// lower (`[TCG-RET-UNBOUND]`), and every call trapped where LLVM computes a
/// value (measured 1024/1024 traps in a C-driven staticlib, aarch64-apple-
/// darwin, 2026-10-01). The reference-graph gate refuses them by name
/// (`[TCG-ITER-STUB-REACHABLE]`); the controls, which the bridge drives (or
/// whose stubbed body only a dead std body names), still compile.
#[test]
fn library_trap_stub_reached_by_local_code_fails_closed_aarch64() {
    if skip("library_trap_stub_reached_by_local_code_fails_closed_aarch64") {
        return;
    }
    let dylib = backend_artifact_support::current_test_backend();
    let dir = workdir("lib_stub");
    let mut failures = Vec::new();
    let (mut refused, mut compiled) = (0usize, 0usize);
    for (name, src, opts, refusal) in LIBRARY_STUB_ROWS {
        for opt in opts {
            match (refusal, compile_library(&dir, &dylib, name, src, opt)) {
                (None, Ok(())) => compiled += 1,
                (None, Err(stderr)) => failures.push(format!(
                    "-O{opt} `{name}`: the control must compile: <<<{stderr}>>>"
                )),
                (Some(code), Ok(())) => failures.push(format!(
                    "-O{opt} `{name}`: expected a {code} refusal, but it compiled (its call \
                     binds a trapping stub)"
                )),
                (Some(code), Err(stderr)) if stderr.contains(code) => refused += 1,
                (Some(code), Err(stderr)) => failures.push(format!(
                    "-O{opt} `{name}`: expected a {code} refusal: <<<{stderr}>>>"
                )),
            }
        }
    }
    let _ = std::fs::remove_dir_all(&dir);
    assert!(
        failures.is_empty(),
        "{} library trap-stub row(s) failed:\n  {}",
        failures.len(),
        failures.join("\n  ")
    );
    assert_eq!((refused, compiled), (4, 5), "every library row must close");
    eprintln!("LIBRARY_TRAP_STUB_REACHED refused={refused} compiled={compiled}");
    positive_evidence::record(
        positive_evidence::Evidence::ExpectedRefusal,
        positive_evidence::Certs::Off,
    );
}

// MUTATION RESULTS (2026-09-30, aarch64-apple-darwin, this file and the
// heap_image_glue change on d42238c92, re-run 2026-10-01 on 16a86a97b with the
// same outcome; backend built by `targo --unverified test --release` with the
// atpkg Trust pack 9192):
//
//   * this tree: 3/3 tests pass (RANGE refusals=0 llvm_native=6 cg_native=6;
//     DEAD_ITER cg_native=0 cg_refused=4; DYN cg_native=4 cg_refused=0).
//   * both `!crate_is_executable_only(tcx)` conjuncts of `failure_route`
//     replaced by `true` (the trap stubs restored in an executable): 2/3.
//     `dead_std_iterator_body_fails_closed_aarch64` fails on all four rows —
//     `repeat_take_sum` / `successors_take_sum` at -O2 and -O3 are killed by
//     signal 5 (SIGTRAP) where LLVM prints 12 / 31.
//     `range_inclusive_rev_reductions_never_trap_aarch64` and
//     `dyn_heap_glue_drop_fails_closed_aarch64` pass: their rows lower, so
//     they no longer reach the failure route at all.
//
// MUTATION RESULTS (2026-10-03, aarch64-unknown-linux-gnu, d2be11234 plus this
// file's current rows; backends built by `targo --unverified build --release`
// with the Trust ae9c2c1d pack; the test executable run beside each backend):
//
//   * this tree: 5/5 tests pass (RANGE refusals=0 llvm_native=6 cg_native=6;
//     DEAD_ITER cg_native=0 cg_refused=4; GENERATOR_TAKE cg_native=4
//     cg_refused=0; DYN cg_native=4 cg_refused=0; LIBRARY refused=4
//     compiled=5).
//   * the same two conjuncts replaced by `true`: 4/5.
//     `dead_std_iterator_body_fails_closed_aarch64` fails on all four rows —
//     `repeat_n_take_sum` / `cycle_take_sum` at -O2 and -O3 are killed by
//     signal 5 (SIGTRAP) where LLVM prints 12 / 13. The generator-take rows
//     build and match under the mutation as well: they no longer reach the
//     failure route, which is why they stopped being the gate's witnesses.
