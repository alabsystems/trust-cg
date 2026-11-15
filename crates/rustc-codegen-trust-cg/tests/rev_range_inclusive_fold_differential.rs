#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// Integration test: a REVERSED `RangeInclusive` (`(a..=b).rev()`, `.rfold`,
// `.rfind`, `.try_rfold`) folds exactly as LLVM does — same values, same
// overflow panics, same effect order, same leftover state.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// WHY THIS FILE EXISTS. The bridge drives std iterator chains itself
// (`resolve_iter_chain` + `emit_chain_next`) and modeled a `RangeInclusive`
// source FORWARD only. A reversed walk of one failed closed at -O0/-O1 in
// every shape (the `.rev()` constructor refused: `rev() over a RangeInclusive
// is not modeled`). At -O2/-O3 `Rev::sum` / `product` / `fold` / `count` and
// `.rfold` inline to `<RangeInclusive<T> as DoubleEndedIterator>::rfold`,
// whose std body is `self.try_rfold(init, NeverShortCircuit::wrap_mut_2(f)).0`
// and reaches `RangeInclusiveIteratorImpl::spec_try_rfold` into
// `NeverShortCircuit<B>`; for a scalar accumulator `B` the general path does
// not lower that body (`[TCG-RET-UNBOUND]`: the return local has no value at
// `return`), so the executable refused it and a library trapped it as a dead
// `try_rfold` body. Measured on aarch64-apple-darwin before the fix:
// `(1..=n).rev().sum()` / `.product()` refused at every opt level, where LLVM
// prints 55 / 3628800.
//
// THE FIX. `emit_source_next` drives a reversed inclusive source as std's
// `spec_next_back` (yield `end`, step `end` down while `start < end`, set
// `exhausted` on the `start == end` element) — the sequence and leftover state
// `spec_try_rfold` produces too — and `lower_iterator_call` routes a std
// `RangeInclusive::rfold` into a primitive scalar accumulator to that
// back-to-front drive instead of the unlowerable std body. No order-blindness
// argument is used: the items are visited in rfold's own order. Shapes whose
// std body the general path already lowered at -O2/-O3 (a unit or aggregate
// `rfold` accumulator: `for_each`, `last`; the `ControlFlow`-returning
// `spec_try_rfold` of `find` / `any` / `rfind` / `try_rfold`) stay on it.
//
// THE GATE. One fixture (`bridge_corpus/fix_rev_range_inclusive_folds.rs`)
// holds every shape as a `CASE`; it is compiled once per CONFIG by both
// backends — opt level 0..3 x `-Coverflow-checks` on/off x `-Cpanic`
// unwind/abort — and every case is run against both binaries and compared on
// exit code, killing signal, stdout, and whether (and on which operation) the
// run panicked. The floor is EVERY row: a bridge refusal of a config fails the
// test, because the regression this file pins is "the reversed inclusive walk
// does not lower".
// Rows cover: empty (`5..=4`), single (`n..=n`), the type's top and bottom
// (`u64::MAX`, `i64::MIN`, `u8 0..=255`, `i8 -128..=127`), u64/i32/usize/u8/i8,
// a product that overflows only BACK TO FRONT (`(0..=255u8).rev().product()`:
// LLVM multiplies 255 * 254 first and panics under overflow checks, where a
// front-to-back walk would hit the 0 first and never overflow), sums that
// overflow on their first add, order-sensitive folds, `for_each`, a range
// partly consumed by `next` / `next_back` first (the `exhausted` flag and both
// endpoints carry over), the other consumers a reversed inclusive chain reaches
// (`count`/`last`/`any`/`all`/`nth`/`max`/`min`/`find`/`position`/`rfind`/
// `rfold`/`map`/`filter`/`take`/`skip`/double `rev`/`collect`/`for` loop),
// a `map` closure with a print effect (effects in back-to-front order), and
// the leftover state of a short-circuited `rfind` over a BORROWED range (what
// `next` / `next_back` yield from it afterwards, `exhausted` included).
//
// The oracle's own behaviour is pinned too (`ORACLE_PANICS`): each overflow
// case must panic under LLVM with overflow checks on and exit 0 with them off,
// so a fixture edit cannot silently stop exercising the panic path.
//
// NOT COVERED, AND WHY (measured, and not introduced by this change): the panic
// LINE itself — its Location and message text — is reduced to which operation
// overflowed (`stderr_verdict`), because two deviations shared with the
// FORWARD reductions would fail every overflow row. Measured on the base
// backend (be8e35c2a) for `(a..=n).sum()` and `(a..n).rev().sum()`: at
// -O0/-O1 the intercepted sum/product loop raises with the CALLER's Location
// where LLVM reports core's `iter/traits/accum.rs:206:1`; at -O2/-O3 the
// general `Assert` lowering says ``attempt to compute `Add` with overflow``
// where LLVM says `attempt to add with overflow` (`assert_kind_panic_message`,
// documented there as an accepted cosmetic deviation). Both are outside this
// file's scope. Not covered either, because the bridge refuses them at
// -O0/-O1 for reasons outside this lowering (the shared `try_fold` engine; the
// same shapes refuse over a forward walk): a `find` / `rfind` / `try_rfold`
// whose closure captures by value, and a `.rev()` over a `&mut RangeInclusive`
// (an unmodeled `by_ref` chain). At -O2/-O3 those lower on the general path.
//
// HOST-NATIVE: no `--target` is passed, so this runs wherever the crate builds.
// Measured on aarch64-apple-darwin only; the lowering is target-independent,
// but no x86_64 run of this file has been observed. The bridge side passes
// `no-proof-certs` (with certificates on, AArch64 refuses essentially every
// object at proof promotion, `[TCG-PROOF-465]`, unrelated to this lowering).
//
// FALSIFIED: see `MUTATION RESULTS` at the bottom of this file.

use std::os::unix::process::ExitStatusExt;
use std::path::{Path, PathBuf};
use std::process::Command;

const FIXTURE: &str = include_str!("bridge_corpus/fix_rev_range_inclusive_folds.rs");

const CASES: &[&str] = &[
    "sum_u64",
    "sum_u64_ovf",
    "prod_u64",
    "prod_u64_ovf",
    "sum_i32",
    "sum_i32_ovf",
    "prod_i32",
    "prod_i32_ovf",
    "sum_usize",
    "sum_u8",
    "sum_u8_full",
    "prod_u8",
    "prod_u8_full",
    "sum_i8",
    "sum_i8_full",
    "digest",
    "digest_i8",
    "for_each",
    "exhausted",
    "consumers",
    "map_effect",
    "state_after",
];

/// The cases whose LLVM run must PANIC under `-Coverflow-checks=on` (and exit 0
/// with them off): the fixture's overflow witnesses.
const ORACLE_PANICS: &[&str] = &[
    "sum_u64_ovf",
    "prod_u64_ovf",
    "sum_i32_ovf",
    "prod_i32_ovf",
    "sum_u8_full",
    "prod_u8_full",
    "sum_i8_full",
];

const OPT_LEVELS: &[&str] = &["0", "1", "2", "3"];
const OVERFLOW_CHECKS: &[&str] = &["on", "off"];
const PANIC_STRATEGIES: &[&str] = &["unwind", "abort"];

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("tcg_rev_incl_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

/// Compile the fixture with `flags`, through the bridge when `backend` is
/// `Some`. `Err` carries the compiler's stderr.
fn compile(
    dir: &Path,
    lane: &str,
    flags: &[String],
    backend: Option<&Path>,
) -> Result<PathBuf, String> {
    let src_path = dir.join("fix_rev_range_inclusive_folds.rs");
    if !src_path.exists() {
        std::fs::write(&src_path, FIXTURE).expect("write fixture");
    }
    let bin = dir.join(format!("rev_incl_{lane}"));
    let mut cmd = toolchain_support::rustc_command();
    cmd.args(["--crate-type", "bin", "-Ccodegen-units=1"]);
    cmd.args(flags);
    if let Some(dylib) = backend {
        let mut backend_arg = std::ffi::OsString::from("-Zcodegen-backend=");
        backend_arg.push(dylib);
        cmd.arg(backend_arg);
        // Bridge side ONLY: see the module doc's `no-proof-certs` paragraph.
        cmd.arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]));
    }
    cmd.arg("-o").arg(&bin).arg(&src_path);
    let output = cmd.output().expect("spawn the compiler");
    if !output.status.success() {
        return Err(String::from_utf8_lossy(&output.stderr).into_owned());
    }
    Ok(bin)
}

#[derive(Debug, PartialEq, Eq)]
struct Ending {
    code: Option<i32>,
    signal: Option<i32>,
    stdout: String,
    /// stderr reduced by `stderr_verdict`.
    stderr: String,
}

/// A run's stderr as this test compares it: verbatim when the program did not
/// panic (both sides must then print nothing), otherwise only WHICH operation
/// overflowed. See the module doc's NOT COVERED paragraph for why the panic
/// line itself is not compared.
fn stderr_verdict(stderr: &str) -> String {
    if !stderr.contains("panicked at") {
        return stderr.to_owned();
    }
    let line = stderr
        .lines()
        .find(|line| line.contains("with overflow"))
        .unwrap_or("<a panic that is not an overflow>");
    let op = if line.contains("attempt to add") || line.contains("`Add`") {
        "add"
    } else if line.contains("attempt to multiply") || line.contains("`Mul`") {
        "multiply"
    } else {
        line
    };
    format!("panicked: {op} with overflow")
}

fn run(bin: &Path, case: &str) -> Ending {
    let out = Command::new(bin)
        .env("CASE", case)
        .output()
        .expect("run compiled binary");
    Ending {
        code: out.status.code(),
        signal: out.status.signal(),
        stdout: String::from_utf8_lossy(&out.stdout).into_owned(),
        stderr: stderr_verdict(&String::from_utf8_lossy(&out.stderr)),
    }
}

fn stderr_tail(stderr: &str) -> String {
    stderr.lines().rev().take(6).collect::<Vec<_>>().join(" | ")
}

#[test]
fn rev_range_inclusive_folds_match_llvm() {
    if toolchain_support::skip_without_backend_knobs("rev_range_inclusive_folds_match_llvm") {
        return;
    }
    let dylib = backend_artifact_support::current_test_backend();
    let mut matched = 0usize;
    let mut total = 0usize;
    let mut failures: Vec<String> = Vec::new();
    for opt in OPT_LEVELS {
        for checks in OVERFLOW_CHECKS {
            for strategy in PANIC_STRATEGIES {
                let config = format!("-O{opt} overflow-checks={checks} panic={strategy}");
                let flags = vec![
                    format!("-Copt-level={opt}"),
                    format!("-Coverflow-checks={checks}"),
                    format!("-Cpanic={strategy}"),
                ];
                total += CASES.len();
                let dir = workdir(&format!("O{opt}_{checks}_{strategy}"));
                let oracle = compile(&dir, "llvm", &flags, None).unwrap_or_else(|e| {
                    panic!("{config}: the LLVM oracle failed to compile: <<<{e}>>>")
                });
                let bridge = match compile(&dir, "bridge", &flags, Some(&dylib)) {
                    Ok(bin) => bin,
                    Err(stderr) => {
                        failures.push(format!(
                            "{config}: the bridge REFUSED the fixture, so {} case(s) never \
                             ran: <<<{}>>>",
                            CASES.len(),
                            stderr_tail(&stderr)
                        ));
                        let _ = std::fs::remove_dir_all(&dir);
                        continue;
                    }
                };
                for case in CASES {
                    let want = run(&oracle, case);
                    // The oracle must exercise what the case claims.
                    let panics = ORACLE_PANICS.contains(case) && *checks == "on";
                    let oracle_panicked = match *strategy {
                        "unwind" => want.code == Some(101),
                        _ => want.signal == Some(6),
                    };
                    assert_eq!(
                        oracle_panicked, panics,
                        "{config} CASE={case}: the LLVM oracle's panic behaviour changed \
                         ({want:?}); the fixture no longer exercises this case"
                    );
                    if !panics {
                        assert_eq!(
                            want.code,
                            Some(0),
                            "{config} CASE={case}: the LLVM oracle did not exit 0: {want:?}"
                        );
                    }
                    let got = run(&bridge, case);
                    if got == want {
                        matched += 1;
                    } else {
                        failures.push(format!(
                            "{config} CASE={case}: LLVM {want:?} vs trust-cg {got:?}"
                        ));
                    }
                }
                let _ = std::fs::remove_dir_all(&dir);
            }
        }
    }
    eprintln!("reversed RangeInclusive rows: {matched}/{total} matched LLVM");
    for failure in &failures {
        eprintln!("  FAILED {failure}");
    }
    assert!(
        failures.is_empty() && matched == total,
        "{} of {total} reversed RangeInclusive rows diverged from LLVM or never ran: \
         {failures:#?}",
        total - matched
    );
}

// MUTATION RESULTS (2026-09-30, aarch64-apple-darwin, backend built by
// `targo --unverified test --release` with the atpkg Trust pack 9192):
//
//   * this tree: 352/352 rows match LLVM.
//   * the base backend (be8e35c2a, before the fix): every one of the 16 configs
//     is REFUSED — at -O0/-O1 `rev() over a RangeInclusive is not modeled`, at
//     -O2/-O3 `[TCG-RET-UNBOUND]` in `RangeInclusiveIteratorImpl::
//     spec_try_rfold` (measured with the stage1 `trustc` driver).
//   * `emit_source_next`'s reversed inclusive step made to walk FORWARD (`if
//     false && reversed` in the endpoint selection; every route left intact):
//     264/352 — 88 rows diverge at every opt level, e.g. `-O3
//     overflow-checks=on panic=unwind CASE=digest: LLVM "192979864414942 7 220
//     6432837 3889589120 4996773" vs trust-cg "185988053221342 7 220 6342537
//     3460427904 4905267"`; the failing cases are the order-sensitive ones
//     (`digest`, `digest_i8`, `map_effect`, `consumers`, `prod_u8_full` under
//     overflow checks — the forward walk multiplies by 0 first and never
//     panics — and, where the walk is the bridge's at -O0/-O1, `for_each` and
//     `state_after`). The order-blind sums and products keep matching under
//     that mutation, which is why the order-sensitive cases are in the fixture.
