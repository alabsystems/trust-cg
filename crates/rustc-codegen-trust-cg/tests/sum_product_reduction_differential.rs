#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// Integration test: the `.sum()` / `.product()` reduction lane — the rows that
// `unsized_value_measurement_differential`'s `sum_product_reduction_pins_hold`
// (the checked, saturating-product and reversed-order pins) does not cover.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// Three families (the fixtures' own headers carry the measurements):
//
//   * IMPL IDENTITY (`std_sum_product_arith`). The bridge replaces a modeled
//     `sum`/`product` with its own loop, whose operator used to come from the
//     accumulator's trust-ir scalar type. That type map collapses `Saturating<T>`,
//     `Wrapping<T>` and every single-scalar user newtype to `T`, so a
//     `Saturating` SUM wrapped, and a user `impl Sum` — or `impl Sum<Local> for
//     u64` — had its body replaced by an add. A `Saturating<u128>` sum is past
//     the modeled 64-bit width and must not be computed by the loop at all.
//   * EFFECT ORDER over a source the back-to-front drive does not model (`zip`,
//     `chain`, `RangeInclusive`): a reversed `map` with an effect must refuse by
//     name, never compile front to back.
//   * CONTROL (`closure_body_is_effect_free`): reversed WRAPPING reductions whose
//     closures have no effect keep the forward drive. The `zip` row's closure
//     inlines core's `#[rustc_inherit_overflow_checks]` `Mul`, whose MIR keeps an
//     overflow `Assert` that this crate's codegen elides; counting that assert
//     as an effect refused a program the forward drive compiled and matched.
//
// THE GATE. Each row is compiled BY THE BRIDGE (`no-proof-certs`, isolating MIR
// lowering from this host's opcode-proof inventory) and BY LLVM with the same
// flags, run, and compared on STDOUT, EXIT CODE and KILLING SIGNAL.
//
//   * `Must`: the bridge must COMPILE and MATCH. Every such row either diverged
//     before the impl-identity change or is a CONTROL that compiled and matched
//     there and must keep doing so (a new refusal of it is a coverage
//     regression).
//   * `MatchOrRefuse`: the bridge may refuse with a NAMED `[TCG-...]` diagnostic;
//     if it compiles, it must match. These rows diverged before the change.

use std::os::unix::process::ExitStatusExt;
use std::path::{Path, PathBuf};
use std::process::Command;

#[derive(Clone, Copy, PartialEq, Eq)]
enum Policy {
    Must,
    MatchOrRefuse,
}

struct Row {
    fixture: &'static str,
    src: &'static str,
    flags: &'static [&'static str],
    policy: Policy,
}

macro_rules! fixture {
    ($name:literal) => {
        ($name, include_str!(concat!("bridge_corpus/", $name, ".rs")))
    };
}

fn row(
    fixture: (&'static str, &'static str),
    flags: &'static [&'static str],
    policy: Policy,
) -> Row {
    Row {
        fixture: fixture.0,
        src: fixture.1,
        flags,
        policy,
    }
}

fn rows() -> Vec<Row> {
    use Policy::{MatchOrRefuse, Must};
    const O0: &[&str] = &["-Copt-level=0"];
    const O2: &[&str] = &["-Copt-level=2"];
    const O3: &[&str] = &["-Copt-level=3"];
    vec![
        // IMPL IDENTITY
        row(fixture!("fix_std_sum_impl_identity"), O0, Must),
        row(fixture!("fix_std_sum_impl_identity"), O3, Must),
        row(fixture!("fix_sum_user_impl_not_replaced"), O0, Must),
        row(fixture!("fix_sum_user_impl_not_replaced"), O3, Must),
        row(fixture!("fix_sum_foreign_item_impl_not_replaced"), O0, Must),
        row(fixture!("fix_sum_foreign_item_impl_not_replaced"), O3, Must),
        row(fixture!("fix_saturating_product_std_impl"), O3, Must),
        row(
            fixture!("fix_saturating_u128_sum_not_modeled"),
            O0,
            MatchOrRefuse,
        ),
        // EFFECT ORDER over an unmodeled back-to-front source
        row(
            fixture!("fix_rfold_effect_order_unmodeled_source"),
            O2,
            MatchOrRefuse,
        ),
        row(
            fixture!("fix_rfold_effect_order_unmodeled_source"),
            O3,
            MatchOrRefuse,
        ),
        // CONTROL: order-blind reversed reductions keep compiling.
        row(fixture!("fix_rfold_pure_chains_forward_drive"), O2, Must),
        row(fixture!("fix_rfold_pure_chains_forward_drive"), O3, Must),
    ]
}

#[derive(Debug, PartialEq, Eq)]
struct Ending {
    code: Option<i32>,
    signal: Option<i32>,
    stdout: String,
}

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("tcg_reduction_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

fn compile_and_run(
    dir: &Path,
    name: &str,
    src: &str,
    flags: &[&str],
    backend: Option<&Path>,
) -> Result<Ending, String> {
    let src_path = dir.join(format!("{name}.rs"));
    std::fs::write(&src_path, src).expect("write source");
    let bin = dir.join(if backend.is_some() {
        format!("{name}_bridge")
    } else {
        format!("{name}_llvm")
    });
    let mut cmd = toolchain_support::rustc_command();
    cmd.args(["--crate-type", "bin", "-Cpanic=abort", "-Ccodegen-units=1"]);
    cmd.args(flags);
    if let Some(dylib) = backend {
        let mut backend_arg = std::ffi::OsString::from("-Zcodegen-backend=");
        backend_arg.push(dylib);
        cmd.arg(backend_arg);
        cmd.arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]));
    }
    cmd.arg("-o").arg(&bin).arg(&src_path);
    let output = cmd.output().expect("spawn the compiler");
    if !output.status.success() {
        return Err(String::from_utf8_lossy(&output.stderr).into_owned());
    }
    let run = Command::new(&bin).output().expect("run compiled binary");
    Ok(Ending {
        code: run.status.code(),
        signal: run.status.signal(),
        stdout: String::from_utf8_lossy(&run.stdout).into_owned(),
    })
}

/// The bridge's own named refusal tag, if this stderr is a fail-closed refusal
/// rather than a crash.
fn named_refusal(stderr: &str) -> Option<String> {
    if stderr.contains("internal compiler error") || stderr.contains("panicked at") {
        return None;
    }
    let start = stderr.find("[TCG-")?;
    let end = stderr[start..].find(']')? + start + 1;
    Some(stderr[start..end].to_owned())
}

#[test]
fn reductions_use_the_selected_impl_and_keep_rustcs_order() {
    if toolchain_support::skip_without_backend_knobs(
        "reductions_use_the_selected_impl_and_keep_rustcs_order",
    ) {
        return;
    }
    let dylib = backend_artifact_support::current_test_backend();
    let mut failures: Vec<String> = Vec::new();
    for (index, row) in rows().iter().enumerate() {
        let dir = workdir(&format!("{}_{index}", row.fixture));
        let oracle =
            compile_and_run(&dir, row.fixture, row.src, row.flags, None).unwrap_or_else(|e| {
                panic!(
                    "{} {:?}: the LLVM oracle failed to compile: <<<{e}>>>",
                    row.fixture, row.flags
                )
            });
        match compile_and_run(&dir, row.fixture, row.src, row.flags, Some(&dylib)) {
            Ok(bridge) if bridge == oracle => {
                eprintln!("{} {:?}: MATCH {oracle:?}", row.fixture, row.flags);
            }
            Ok(bridge) => failures.push(format!(
                "{} {:?}: compiled and DIVERGES — LLVM {oracle:?}, trust-cg {bridge:?}",
                row.fixture, row.flags
            )),
            Err(stderr) => match (row.policy, named_refusal(&stderr)) {
                (Policy::MatchOrRefuse, Some(tag)) => {
                    eprintln!(
                        "{} {:?}: REFUSED {tag} (fail-closed)",
                        row.fixture, row.flags
                    );
                }
                (Policy::Must, Some(tag)) => failures.push(format!(
                    "{} {:?}: refused ({tag}) a row that must compile",
                    row.fixture, row.flags
                )),
                (_, None) => failures.push(format!(
                    "{} {:?}: failed WITHOUT a named [TCG-...] refusal: <<<{stderr}>>>",
                    row.fixture, row.flags
                )),
            },
        }
        let _ = std::fs::remove_dir_all(&dir);
    }
    assert!(
        failures.is_empty(),
        "{} reduction row(s) failed:\n  {}",
        failures.len(),
        failures.join("\n  ")
    );
}
