//! Native Linux ELF twin of `coroutine_generator_aarch64.rs`: real
//! `#[coroutine]` state machines compiled through the rustc bridge for
//! `aarch64-unknown-linux-gnu`, linked with GNU `cc` against C drivers and
//! run, with an LLVM twin of every lane.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates
//! License: Apache-2.0
//!
//! This target is mandatory on its named host, not a portable skip; the shared
//! harness (`support/linux_runtime_twin.rs`) fails it by name when a
//! prerequisite is missing and binds the backend the runner supplies.
//!
//! FIXTURES. The Darwin twin's `GEN_CRATE` (`yield 10; yield 20; return 30`
//! driven by `Pin::new(&mut g).resume(())`) and `DRIVER_C` are kept
//! byte-identical (the script test
//! `test_runtime_twins_keep_the_darwin_crates_and_drivers` pins them). A
//! Linux crate adds the `ResumedAfterReturn` check: a coroutine resumed after
//! it completed must take the coroutine-resumed panic edge after the values it
//! yielded and returned: the run dies on `SIGABRT` in the aborting stub of
//! `core::panicking::panic_const::panic_const_coroutine_resumed`, which names
//! itself on stderr, and CG and LLVM must fire the same stub. Another adds
//! more shapes: a `move` coroutine with a captured upvar, a resume-argument
//! one and a branchy one.
//!
//! The Darwin generator and the upvar and branchy shapes have five or six
//! states, so their resume loops dispatch through a jump table bounded by
//! `CMP state, #4` (or `#5`). Until 2026-10-24 the bridge refused them at O2
//! and O3, failing closed: `const-trip-guard-normalize` (trust-cg-opt
//! `scalar_unroll`) read that bound as a constant loop-trip guard and hoisted
//! it into the preheader, and the per-compile switch binder refuses a bound
//! produced outside its dispatch block (`[TCG-A64-SWITCH-BIND] ... no producer
//! in the block`). The normalizer now declines a jump-table dispatch header
//! (regression: trust-cg-codegen `aarch64_jump_table_loop_header_bound.rs`),
//! and these lanes are the bridge-level regression.
//!
//! WHAT IS CHECKED, AT O0-O3, FOR CG AND LLVM ALIKE. As on Darwin, the O0 MIR
//! must carry rustc's post-`StateTransform` state machine (a coroutine frame
//! aggregate and a `SetDiscriminant` on it, no `Yield` terminator). Each
//! crate is compiled by both compilers (`--emit=obj`, one codegen unit,
//! `-Cpanic=abort`); the objects other than the allocator shim are linked
//! with the driver (undefined core panic entries get aborting stubs) and run
//! three times; every run must print exactly the model and end as modelled,
//! so the CG and LLVM executables agree byte for byte. The bridge's objects
//! must define `ay_gen_seq` and keep a call of the coroutine-resumed panic
//! entry. A bridge compile that refuses a required lane by name does not stop
//! the others: every lane runs, the marker lists the refusal, and the test
//! then fails.
//!
//! CONTROLS (bridge refusal by name, LLVM twin run, every level). Three
//! coroutines outside the bridge's lowering: a stateful generator (`a`, `b`
//! and `i` live across `yield`), whose drop glue is refused
//! (`StatementKind::Nop`); one holding a user-`Drop` guard across a `yield`
//! and dropped while suspended (`Ty::Coroutine`); and one whose closure
//! borrows a captured scalar ("borrowed scalar reference used without
//! deref"). The bridge must refuse each by its exact row and leave no object
//! defining the latter two; LLVM compiles the same valid Rust and its run
//! prints the crate's model (values, order and the guards' drop order).
//!
//! EVIDENCE BOUNDARY. Native TESTING evidence without certificates: the
//! frontend runs with `-Ztrust-verify=off` and every bridge compile with the
//! `no-proof-certs` knob. GNU cc/ld, binutils and glibc are trusted.
//!
//! The artifacts directory is removed when the test passes; setting
//! `COROUTINE_GENERATOR_LINUX_KEEP_ARTIFACTS=1` retains it.

#![cfg(all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"))]

#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;
#[path = "support/linux_runtime_twin.rs"]
mod twin;

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::Command;
use twin::{Bridge, Ending, LaneRow, ObjectFacts};

const MARKER: &str = "TCG_BRIDGE_COROUTINE_EXECUTION";
const KEEP_ARTIFACTS: &str = "COROUTINE_GENERATOR_LINUX_KEEP_ARTIFACTS";
/// Native executions of each linked executable.
const RUNS_PER_LANE: usize = 3;
const SIGABRT: i32 = twin::SIGABRT;
const RESUMED_PANIC: &str = "panic_const_coroutine_resumed";

/// Byte-identical to `GEN_CRATE` in `coroutine_generator_aarch64.rs`.
const GEN_CRATE: &str = "\
#![crate_type = \"staticlib\"]\n\
#![feature(coroutines, coroutine_trait, stmt_expr_attributes)]\n\
\n\
use std::ops::{Coroutine, CoroutineState};\n\
use std::pin::Pin;\n\
\n\
#[no_mangle]\n\
pub extern \"C\" fn ay_gen_seq() -> i64 {\n\
    let mut g = #[coroutine] || {\n\
        yield 10i64;\n\
        yield 20i64;\n\
        30i64\n\
    };\n\
    let mut packed: i64 = 0;\n\
    let mut step: i64 = 0;\n\
    loop {\n\
        match Pin::new(&mut g).resume(()) {\n\
            CoroutineState::Yielded(v) => {\n\
                if step == 0 { packed += v * 1_000_000; } else { packed += v * 1_000; }\n\
                step += 1;\n\
            }\n\
            CoroutineState::Complete(r) => { packed += r; break; }\n\
        }\n\
    }\n\
    packed\n\
}\n";

/// Byte-identical to `DRIVER_C` in `coroutine_generator_aarch64.rs`.
const DRIVER_C: &str = "\
#include <stdio.h>\n\
extern long ay_gen_seq(void);\n\
int main(void) {\n\
    long packed = ay_gen_seq();\n\
    printf(\"packed=%ld\\n\", packed);\n\
    if (packed != 10020030L) return 1;\n\
    return 0;\n\
}\n";

const SEQUENCE_MODEL: &str = "packed=10020030\n";

/// The Linux crates' shared header.
const PRELUDE: &str = r#"#![feature(coroutines, coroutine_trait, stmt_expr_attributes)]
use std::ops::{Coroutine, CoroutineState};
use std::pin::Pin;
extern "C" {
    fn ay_record(event: i64);
}
"#;

/// Resuming a completed coroutine panics (`ResumedAfterReturn`).
const RESUMED_CRATE: &str = r#"
#[no_mangle]
pub extern "C" fn ay_gen_resume_after_complete() -> i64 {
    let mut g = #[coroutine] || {
        yield 1i64;
        2i64
    };
    let mut seen = 0;
    let mut step = 0;
    while step < 3 {
        match Pin::new(&mut g).resume(()) {
            CoroutineState::Yielded(v) => { unsafe { ay_record(v) }; seen += v; }
            CoroutineState::Complete(r) => { unsafe { ay_record(r) }; seen += r; }
        }
        step += 1;
    }
    seen
}
"#;

const RESUMED_DRIVER: &str = r#"#include <stdio.h>
extern long ay_gen_resume_after_complete(void);
void ay_record(long event) { printf(" %ld", event); fflush(stdout); }
int main(void) {
    printf("resume_after_complete:");
    fflush(stdout);
    long r = ay_gen_resume_after_complete();
    printf(" returned %ld\n", r);
    return 0;
}
"#;

/// The yielded 1, the returned 2, then the third resume's panic.
const RESUMED_MODEL: &str = "resume_after_complete: 1 2";

/// More state-machine shapes (after [`PRELUDE`]): a `move` coroutine with a
/// captured upvar and five states (two yields), a resume-argument coroutine
/// with four (one yield), and a branchy one with six (three yield points).
/// The five- and six-state resume loops dispatch through a jump table whose
/// bound the bridge used to hoist out of the dispatch block at O2/O3 and then
/// refuse (`[TCG-A64-SWITCH-BIND]`, like [`GEN_CRATE`]); the four-state one
/// stayed below that rewrite and always compiled.
const SHAPES_CRATE: &str = r#"
#[no_mangle]
pub extern "C" fn xc_upvar(x: i64) -> i64 {
    let mut g = #[coroutine] move || {
        yield x;
        yield x * 2;
        x + 1
    };
    let mut acc = 0i64;
    loop {
        match Pin::new(&mut g).resume(()) {
            CoroutineState::Yielded(v) => acc = acc * 100 + v,
            CoroutineState::Complete(r) => return acc * 100 + r,
        }
    }
}

#[no_mangle]
pub extern "C" fn xc_resume_arg(a: i64, b: i64) -> i64 {
    let mut g = #[coroutine] |first: i64| {
        let second = yield first + 1;
        second * 3
    };
    let one = match Pin::new(&mut g).resume(a) {
        CoroutineState::Yielded(v) => v,
        CoroutineState::Complete(_) => -1,
    };
    let two = match Pin::new(&mut g).resume(b) {
        CoroutineState::Yielded(_) => -2,
        CoroutineState::Complete(r) => r,
    };
    one * 1000 + two
}

#[no_mangle]
pub extern "C" fn xc_branchy(flag: i64) -> i64 {
    let mut g = #[coroutine] move || {
        if flag > 0 {
            yield 1i64;
        } else {
            yield 2i64;
            yield 3i64;
        }
        4i64
    };
    let mut acc = 0;
    loop {
        match Pin::new(&mut g).resume(()) {
            CoroutineState::Yielded(v) => acc = acc * 10 + v,
            CoroutineState::Complete(r) => return acc * 10 + r,
        }
    }
}
"#;

const SHAPES_DRIVER: &str = r#"#include <stdio.h>
extern long xc_upvar(long);
extern long xc_resume_arg(long, long);
extern long xc_branchy(long);
int main(void) {
    printf("upvar=%ld,%ld\n", xc_upvar(7), xc_upvar(-3));
    printf("resume_arg=%ld,%ld\n", xc_resume_arg(5, 9), xc_resume_arg(-4, 2));
    printf("branchy=%ld,%ld\n", xc_branchy(1), xc_branchy(0));
    return 0;
}
"#;

/// `xc_upvar(7)` yields 7, 14 and returns 8; `xc_upvar(-3)` yields -3, -6 and
/// returns -2; `xc_resume_arg` yields `a + 1` and returns `3 * b`;
/// `xc_branchy` yields 1 (flag > 0) or 2, 3, and returns 4.
const SHAPES_MODEL: &str = "\
upvar=71408,-30602
resume_arg=6027,-2994
branchy=14,234
";

/// The refusal controls' crate (after [`PRELUDE`]).
const REFUSED_CRATE: &str = r#"
/// A generator whose state (`a`, `b`, `i`) lives across its `yield`.
#[no_mangle]
pub extern "C" fn ay_gen_fib(n: i64) -> i64 {
    let limit = n;
    let mut g = #[coroutine] move || {
        let (mut a, mut b) = (0i64, 1i64);
        let mut i = 0;
        while i < limit {
            yield a;
            let c = a + b;
            a = b;
            b = c;
            i += 1;
        }
        -1i64
    };
    let mut sum = 0i64;
    loop {
        match Pin::new(&mut g).resume(()) {
            CoroutineState::Yielded(v) => { unsafe { ay_record(v) }; sum += v; }
            CoroutineState::Complete(r) => { unsafe { ay_record(r) }; break; }
        }
    }
    sum
}

pub struct Guard(pub i64);
impl Drop for Guard {
    fn drop(&mut self) {
        unsafe { ay_record(1000 + self.0) }
    }
}

/// User-`Drop` guards live across `yield`s; dropping the suspended
/// coroutine drops the live ones, the later first.
#[no_mangle]
pub extern "C" fn ay_gen_drop_suspended(steps: i64) -> i64 {
    let mut g = #[coroutine] || {
        let a = Guard(1);
        yield 1i64;
        let b = Guard(2);
        yield 2i64;
        drop(a);
        yield 3i64;
        drop(b);
        4i64
    };
    let mut last = 0;
    let mut step = 0;
    while step < steps {
        match Pin::new(&mut g).resume(()) {
            CoroutineState::Yielded(v) => { unsafe { ay_record(v) }; last = v; }
            CoroutineState::Complete(r) => { unsafe { ay_record(r) }; last = r; break; }
        }
        step += 1;
    }
    drop(g);
    unsafe { ay_record(-1) };
    last
}

/// Resume arguments flow in; the closure borrows the captured `seed`.
#[no_mangle]
pub extern "C" fn ay_gen_resume_args(seed: i64) -> i64 {
    let mut g = #[coroutine] |mut x: i64| {
        let mut total = seed;
        loop {
            total += x;
            if x < 0 {
                return total;
            }
            x = yield total * 2;
        }
    };
    let mut input = 3i64;
    loop {
        match Pin::new(&mut g).resume(input) {
            CoroutineState::Yielded(v) => unsafe { ay_record(v) },
            CoroutineState::Complete(r) => return r,
        }
        input = if input >= 5 { -1 } else { input + 1 };
    }
}
"#;

const REFUSED_DRIVER: &str = r#"#include <stdio.h>
extern long ay_gen_resume_args(long seed);
extern long ay_gen_fib(long n);
extern long ay_gen_drop_suspended(long steps);
void ay_record(long event) { printf(" %ld", event); }
int main(void) {
    printf("resume_args:");
    long r = ay_gen_resume_args(100);
    printf(" -> %ld\n", r);
    printf("fib:");
    r = ay_gen_fib(10);
    printf(" -> %ld\n", r);
    for (long steps = 0; steps <= 5; steps++) {
        printf("drop_suspended(%ld):", steps);
        r = ay_gen_drop_suspended(steps);
        printf(" -> %ld\n", r);
    }
    return 0;
}
"#;

/// The resume arguments 3, 4, 5, -1 against the seed 100; the first ten
/// Fibonacci numbers and the completion -1; and each drop count's guard drops
/// (1001, 1002) in the order Rust specifies for a suspended coroutine.
const REFUSED_MODEL: &str = "\
resume_args: 206 214 224 -> 111
fib: 0 1 1 2 3 5 8 13 21 34 -1 -> 88
drop_suspended(0): -1 -> 0
drop_suspended(1): 1 1001 -1 -> 1
drop_suspended(2): 1 2 1002 1001 -1 -> 2
drop_suspended(3): 1 2 1001 3 1002 -1 -> 3
drop_suspended(4): 1 2 1001 3 1002 4 -1 -> 4
drop_suspended(5): 1 2 1001 3 1002 4 -1 -> 4
";

/// (row prefix, fragments, row suffix) of each refusal the bridge must print
/// for [`REFUSED_CRATE`], exactly once at every level. Symbols are matched on
/// their path components, not on crate hashes or `DefId` numbers.
const REFUSALS: [(&str, &[&str], &str); 3] = [
    (
        "- _R",
        &["9drop_glue", "10ay_gen_fib0"],
        " (reachable Rust-internal monomorphization, not a std-internal shim): \
         StatementKind::Nop",
    ),
    (
        "- ay_gen_drop_suspended: Ty::Coroutine(DefId(",
        &["::ay_gen_drop_suspended::{closure#0}), ["],
        "])",
    ),
    (
        "- ay_gen_resume_args: ",
        &[],
        "borrowed scalar reference used without deref",
    ),
];
/// The refused functions no object may define.
const UNDEFINED_AFTER_REFUSAL: [&str; 2] = ["ay_gen_drop_suspended", "ay_gen_resume_args"];

fn compile(
    lane: &Path,
    name: &str,
    source: &str,
    opt: u32,
    bridge: Option<Bridge<'_>>,
) -> (std::process::Output, String, PathBuf) {
    let path = lane.join(format!("{name}.rs"));
    std::fs::write(&path, source).unwrap();
    let object_dir = lane.join(format!("{name}-objects"));
    std::fs::create_dir(&object_dir).unwrap();
    let mut command = twin::rustc_command();
    command.args(["--crate-type", "staticlib"]);
    twin::select_backend(&mut command, bridge);
    command
        .args([
            "-Ccodegen-units=1",
            "-Cpanic=abort",
            "--target",
            twin::TARGET,
        ])
        .arg(format!("-Copt-level={opt}"))
        .arg("--emit=obj")
        .arg("--out-dir")
        .arg(&object_dir)
        .arg(&path);
    let (output, transcript) =
        twin::run_bounded(&mut command, 180, &lane.join(format!("{name}-compile.log")));
    (output, transcript, object_dir)
}

/// The objects to link: everything but the allocator shim (nothing here
/// allocates, and the driver brings no `__rdl_*` entries).
fn link_and_run(
    lane: &Path,
    objects: &[ObjectFacts],
    driver: &str,
    fixture: &'static str,
    compiler: &'static str,
    opt: u32,
    ending: Ending,
    model: &str,
) -> LaneRow {
    let linked: Vec<&ObjectFacts> = objects.iter().filter(|o| !o.is_allocator_shim()).collect();
    assert!(
        objects.len() - linked.len() <= 1,
        "{fixture} {compiler} O{opt}: more than one allocator shim"
    );
    let source = lane.join(format!("{fixture}.c"));
    std::fs::write(&source, driver).unwrap();
    let executable = lane.join(format!("{fixture}.elf"));
    let mut command = Command::new("cc");
    command.arg("-o").arg(&executable).arg(&source);
    if let (Some(stubs), _) = twin::abort_stubs(lane, &linked) {
        command.arg(stubs);
    }
    for facts in &linked {
        command.arg(&facts.path);
    }
    twin::checked(&mut command, 60, &lane.join(format!("{fixture}-link.log")));
    twin::model_runs(
        lane,
        &executable,
        fixture,
        compiler,
        opt,
        RUNS_PER_LANE,
        ending,
        model,
    )
}

/// A positive lane: `Ok(row)`, or `Err(the refusal rows)` when the bridge
/// refused a required function by name. Any other failure panics.
fn positive_lane(
    artifacts: &Path,
    fixture: &'static str,
    source: &str,
    driver: &str,
    opt: u32,
    bridge: Option<Bridge<'_>>,
    ending: Ending,
    model: &str,
) -> Result<LaneRow, String> {
    let compiler = twin::compiler_name(bridge);
    let lane = artifacts.join(format!("{fixture}_{compiler}_O{opt}"));
    std::fs::create_dir(&lane).unwrap();
    let (output, transcript, dir) = compile(&lane, fixture, source, opt, bridge);
    let stderr = String::from_utf8_lossy(&output.stderr);
    if bridge.is_some()
        && output.status.code() == Some(1)
        && stderr.contains("[TCG-MIR-UNSUPPORTED]")
    {
        let rows: Vec<&str> = stderr
            .lines()
            .map(str::trim)
            .filter(|line| line.starts_with("- "))
            .collect();
        assert!(
            !rows.is_empty(),
            "refusal without a named row: {transcript}"
        );
        eprintln!(
            "{fixture} cg O{opt}: REFUSED by the bridge: {}",
            rows.join(" | ")
        );
        return Err(rows.join(" | "));
    }
    assert!(
        output.status.success(),
        "{fixture} {compiler} O{opt} compile failed: {transcript}"
    );
    let objects = twin::inspect_objects(&dir);
    if bridge.is_some() {
        let calls = objects
            .iter()
            .flat_map(|facts| {
                facts.relocations.iter().filter(move |row| {
                    row.kind == "R_AARCH64_CALL26"
                        && facts.symbol(row.symbol_index).name.ends_with(RESUMED_PANIC)
                })
            })
            .count();
        assert!(
            calls >= 1,
            "{fixture} cg O{opt}: no call of the coroutine-resumed panic entry survives"
        );
        if fixture == "sequence" {
            let refs: Vec<&ObjectFacts> = objects.iter().collect();
            let entry = twin::definer(&refs, "ay_gen_seq")
                .defined("ay_gen_seq")
                .unwrap();
            assert_eq!(
                (entry.kind.as_str(), entry.bind.as_str()),
                ("FUNC", "GLOBAL"),
                "cg O{opt}: ay_gen_seq"
            );
        }
    }
    Ok(link_and_run(
        &lane, &objects, driver, fixture, compiler, opt, ending, model,
    ))
}

/// The refusal controls at one level.
fn refusal_control(artifacts: &Path, opt: u32, bridge: Bridge<'_>) -> (serde_json::Value, LaneRow) {
    let lane = artifacts.join(format!("refused_O{opt}"));
    std::fs::create_dir(&lane).unwrap();
    let source = format!("{PRELUDE}{REFUSED_CRATE}");
    let (output, transcript, dir) = compile(&lane, "refused", &source, opt, Some(bridge));
    assert_eq!(
        output.status.code(),
        Some(1),
        "refused O{opt}: expected a compiler refusal, not success, timeout or crash: {transcript}"
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("[TCG-MIR-UNSUPPORTED]"),
        "wrong refusal boundary: {transcript}"
    );
    let rows: Vec<&str> = stderr.lines().map(str::trim).collect();
    for (prefix, fragments, suffix) in REFUSALS {
        assert_eq!(
            rows.iter()
                .filter(|row| {
                    row.starts_with(prefix)
                        && fragments.iter().all(|fragment| row.contains(fragment))
                        && row.ends_with(suffix)
                })
                .count(),
            1,
            "refused O{opt}: the refusal `{prefix}..{suffix}` must appear exactly once: {transcript}"
        );
    }
    let leftover = twin::inspect_objects(&dir);
    let definitions = leftover
        .iter()
        .filter(|facts| {
            UNDEFINED_AFTER_REFUSAL
                .iter()
                .any(|name| facts.defined(name).is_some())
        })
        .count();
    assert_eq!(
        definitions, 0,
        "refused O{opt}: an object defines a refused function"
    );
    let llvm_lane = artifacts.join(format!("refused_llvm_O{opt}"));
    std::fs::create_dir(&llvm_lane).unwrap();
    let (output, transcript, dir) = compile(&llvm_lane, "refused", &source, opt, None);
    assert!(
        output.status.success(),
        "refused LLVM O{opt}: valid Rust failed: {transcript}"
    );
    let objects = twin::inspect_objects(&dir);
    let row = link_and_run(
        &llvm_lane,
        &objects,
        REFUSED_DRIVER,
        "refused",
        "llvm",
        opt,
        Ending::Exit(0),
        REFUSED_MODEL,
    );
    let control = serde_json::json!({
        "name": "refused_coroutines",
        "opt_level": opt,
        "cg_refusals": 1,
        "refusal_rows": REFUSALS.len(),
        "cg_definitions": definitions,
        "llvm_runs": RUNS_PER_LANE,
    });
    (control, row)
}

/// The Darwin MIR check: rustc's post-`StateTransform` state machine.
fn check_mir(artifacts: &Path) -> serde_json::Value {
    let source = artifacts.join("gen_seq.rs");
    std::fs::write(&source, GEN_CRATE).unwrap();
    let mir = artifacts.join("gen_seq.mir");
    twin::checked(
        twin::rustc_command()
            .args([
                "--crate-type",
                "staticlib",
                "-Copt-level=0",
                "-Zmir-opt-level=0",
            ])
            .args(["--target", twin::TARGET])
            .args(["--emit=mir", "-o"])
            .arg(&mir)
            .arg(&source),
        180,
        &artifacts.join("mir.log"),
    );
    let mir_text = std::fs::read_to_string(&mir).expect("read MIR");
    assert!(
        mir_text.contains("{coroutine@") && mir_text.contains("(#0)}"),
        "generator MIR did not contain an `AggregateKind::Coroutine` frame construct"
    );
    assert!(
        mir_text.contains("discriminant((*_") && mir_text.contains(") = "),
        "generator MIR did not contain a `SetDiscriminant` on the coroutine frame"
    );
    assert!(
        !mir_text.contains("yield ") && !mir_text.contains("-> [resume:"),
        "generator MIR still contained a raw `Yield` terminator (not post-StateTransform)"
    );
    serde_json::json!({"coroutine_frame": true, "set_discriminant": true, "yield_terminators": 0})
}

#[test]
fn coroutines_match_llvm_and_the_model_linux() {
    twin::require_knobs("coroutine_generator_linux");
    let artifacts = twin::Artifacts::new("trust-cg-coroutine-linux", KEEP_ARTIFACTS);
    let root = artifacts.root.clone();
    twin::require_host(&root);
    let (backend, digest) = twin::backend();
    let bridge = Bridge {
        path: &backend,
        knobs: twin::NO_PROOF_CERTS,
    };
    let mir = check_mir(&root);
    let resumed = format!("{PRELUDE}{RESUMED_CRATE}");
    let shapes = format!("{PRELUDE}{SHAPES_CRATE}");
    let positives: [(&'static str, &str, &str, Ending, &str); 3] = [
        (
            "sequence",
            GEN_CRATE,
            DRIVER_C,
            Ending::Exit(0),
            SEQUENCE_MODEL,
        ),
        (
            "resume_after_complete",
            &resumed,
            RESUMED_DRIVER,
            Ending::Signal(SIGABRT),
            RESUMED_MODEL,
        ),
        (
            "shapes",
            &shapes,
            SHAPES_DRIVER,
            Ending::Exit(0),
            SHAPES_MODEL,
        ),
    ];
    let mut lanes = Vec::new();
    let mut refused = Vec::new();
    let mut controls = Vec::new();
    for opt in twin::OPT_LEVELS {
        for (fixture, source, driver, ending, model) in positives {
            for lane_bridge in [Some(bridge), None] {
                match positive_lane(
                    &root,
                    fixture,
                    source,
                    driver,
                    opt,
                    lane_bridge,
                    ending,
                    model,
                ) {
                    Ok(row) => {
                        // The third resume of a completed coroutine panics
                        // through rustc's coroutine-resumed entry, nothing else.
                        if ending == Ending::Signal(SIGABRT) {
                            row.assert_aborted_through(RESUMED_PANIC);
                        }
                        lanes.push(row);
                    }
                    Err(rows) => refused.push(serde_json::json!({
                        "fixture": fixture, "compiler": "cg", "opt_level": opt, "rows": rows,
                    })),
                }
            }
        }
        let (control, row) = refusal_control(&root, opt, bridge);
        controls.push(control);
        lanes.push(row);
        assert_eq!(
            twin::sha256(&backend),
            digest,
            "backend changed during O{opt}"
        );
    }
    let compared: Vec<&str> = positives
        .iter()
        .map(|(fixture, ..)| *fixture)
        .filter(|fixture| {
            refused
                .iter()
                .all(|row| row["fixture"].as_str() != Some(fixture))
        })
        .collect();
    twin::assert_twins_agree(&lanes, &compared);
    let models: BTreeMap<&str, String> = [
        ("sequence", SEQUENCE_MODEL),
        ("resume_after_complete", RESUMED_MODEL),
        ("shapes", SHAPES_MODEL),
        ("refused", REFUSED_MODEL),
    ]
    .into_iter()
    .map(|(name, model)| {
        (
            name,
            twin::sha256_of(model.as_bytes(), &root.join("model.txt")),
        )
    })
    .collect();
    twin::print_marker(
        MARKER,
        serde_json::json!({
            "runs_per_lane": RUNS_PER_LANE,
            "mir": mir,
            "lanes": lanes.iter().map(LaneRow::json).collect::<Vec<_>>(),
            "refused_lanes": refused,
            "refusal_controls": controls,
            "model_sha256": models,
        }),
        &digest,
    );
    assert!(
        refused.is_empty(),
        "the bridge refused required coroutine lanes (the marker lists them; this is a fail-closed \
         refusal, not a CG/LLVM difference, and the target stays red until it is lowered): {refused:?}"
    );
    artifacts.finish();
}

#[test]
fn coroutine_models_are_the_documented_sequences() {
    // 10 then 20 then 30, packed as on Darwin.
    assert_eq!(
        SEQUENCE_MODEL,
        format!("packed={}\n", 10 * 1_000_000 + 20 * 1_000 + 30)
    );
    // Fibonacci below the tenth term and its sum.
    let (mut a, mut b, mut sum, mut seen) = (0i64, 1i64, 0i64, Vec::new());
    for _ in 0..10 {
        seen.push(a.to_string());
        sum += a;
        (a, b) = (b, a + b);
    }
    assert!(REFUSED_MODEL.contains(&format!("fib: {} -1 -> {sum}\n", seen.join(" "))));
    assert_eq!(REFUSALS.len(), 3);
    // The shapes, packed as their callers pack them.
    let upvar = |x: i64| (x * 100 + 2 * x) * 100 + (x + 1);
    let resume_arg = |a: i64, b: i64| (a + 1) * 1000 + 3 * b;
    let branchy = |flag: i64| {
        let yields: &[i64] = if flag > 0 { &[1] } else { &[2, 3] };
        yields.iter().fold(0, |acc, v| acc * 10 + v) * 10 + 4
    };
    assert_eq!(
        SHAPES_MODEL,
        format!(
            "upvar={},{}\nresume_arg={},{}\nbranchy={},{}\n",
            upvar(7),
            upvar(-3),
            resume_arg(5, 9),
            resume_arg(-4, 2),
            branchy(1),
            branchy(0)
        )
    );
    assert!(RESUMED_MODEL.ends_with(" 1 2") && !RESUMED_MODEL.ends_with('\n'));
}
