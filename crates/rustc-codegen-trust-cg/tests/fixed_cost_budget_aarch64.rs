// Fixed-cost budget of a trivial compile (aarch64-apple-darwin; ledger L14-P5).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// Some of a compile's work does not depend on the crate: the `clean` processes
// that probe the independent checker with its control proof, and the
// whole-file SHA-256 digests of executables (the admitted AY, its private
// copy, the selected checker, the vendored drat-trim). The backend counts both
// (`trust_cg_verify::process_cost`) and prints the counts under its `time`
// knob. This fixture compiles a one-function certificates-on library twice,
// first with a fresh private cache root (what `run.py --cold` measures), then
// again on the same root (warm), and bounds the counts each compile printed.
//
// Measured on Trust 9192 (2026-09-28, M4 Max) before the bound: FOUR
// control-proof processes and FIVE digests per warm compile. The authority
// capture re-probed both default candidates the scheduling hint had probed at
// backend `init`, and digested the Trust toolchain's `clean` (108 MB), which
// the control proof had already found unusable (built without
// `carcara-verify`): about 60 ms on the critical path and 190 M instructions.
//
// Each count is an upper bound. A background identity warm can still add to
// the counts after the backend prints them, so the printed values can be
// lower, never higher, than the work the compile did by then.
//
// Testing evidence only: it bounds work, it proves nothing about the code.
// The legacy `solver_starts` counter counts revalidated command constructions,
// not confirmed child processes. Checker probes likewise count requests that
// may fail before spawn. These budgets are not process-execution evidence.

#![cfg(all(target_os = "macos", target_arch = "aarch64"))]

#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/darwin_native_prerequisites.rs"]
mod darwin_native;
#[path = "support/positive_evidence.rs"]
mod positive_evidence;
#[path = "support/toolchain.rs"]
mod toolchain_support;

use std::os::unix::fs::{DirBuilderExt, PermissionsExt};
use std::path::PathBuf;
use std::process::Output;

/// One `clean` control-proof process per default checker candidate: the Trust
/// toolchain's own `clean` and aterm's managed package.
const MAX_CHECKER_PROBES: u64 = 2;
/// Warm: the admitted AY, its private copy, the selected checker and the
/// vendored drat-trim.
const MAX_WARM_DIGESTS: u64 = 4;
/// Cold: the same four. The copy this compile writes is streamed from the
/// admitted AY, and that one read is also the AY's admission digest (L14-P5;
/// it was a separate fifth read before).
const MAX_COLD_DIGESTS: u64 = 4;
/// The crate has nothing for the solver to discharge; the one start a cold
/// compile may make is the first start of the copy it published.
const MAX_COLD_SOLVER_STARTS: u64 = 1;
const MAX_WARM_SOLVER_STARTS: u64 = 0;
/// A cold compile begins the host's first-start assessment of the copy it
/// published with one suspended, never-run spawn; a warm one publishes
/// nothing.
const MAX_COLD_ASSESSMENT_SPAWNS: u64 = 1;
const MAX_WARM_ASSESSMENT_SPAWNS: u64 = 0;

const SOURCE: &str = "#![no_std]\n#[no_mangle]\npub extern \"C\" fn id32(x: u32) -> u32 { x }\n";

#[derive(Debug, Default, PartialEq, Eq)]
struct Cost {
    checker_probes: u64,
    executable_digests: u64,
    solver_starts: u64,
    assessment_spawns: u64,
}

fn parse_cost(stderr: &str) -> Cost {
    let line = stderr
        .lines()
        .find_map(|line| line.strip_prefix("TCG_TIME process_cost "))
        .unwrap_or_else(|| panic!("the backend printed no process_cost line:\n{stderr}"));
    let field = |key: &str| -> u64 {
        line.split_whitespace()
            .find_map(|pair| pair.strip_prefix(key)?.strip_prefix('='))
            .unwrap_or_else(|| panic!("no `{key}` in `{line}`"))
            .parse()
            .unwrap_or_else(|error| panic!("`{key}` in `{line}`: {error}"))
    };
    Cost {
        checker_probes: field("checker_probes"),
        executable_digests: field("executable_digests"),
        solver_starts: field("solver_starts"),
        assessment_spawns: field("assessment_spawns"),
    }
}

struct Workdir(PathBuf);

impl Workdir {
    fn new() -> Self {
        let unique = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .expect("system clock after epoch")
            .as_nanos();
        let path = std::env::temp_dir().join(format!(
            "trust-cg-fixed-cost-{}-{unique}",
            std::process::id()
        ));
        // The workdir and the cache root inside it are ancestors of AY's
        // private copy, which the identity rule refuses beneath a directory
        // others may write: both are 0700 whatever the umask. A workdir made
        // with the umask's mode (0775 under umask 0002) refused AY here, and
        // the upper-bound budgets then held without the copy or its digests
        // ever being measured (X-HOST-P13 second audit).
        for directory in [path.clone(), path.join("cache")] {
            std::fs::DirBuilder::new()
                .mode(0o700)
                .create(&directory)
                .expect("create a private directory");
            std::fs::set_permissions(&directory, std::fs::Permissions::from_mode(0o700))
                .expect("make the directory 0700");
        }
        std::fs::write(path.join("input.rs"), SOURCE).expect("write fixture source");
        Self(path)
    }

    fn compile(&self) -> Output {
        let mut backend = std::ffi::OsString::from("-Zcodegen-backend=");
        backend.push(backend_artifact_support::current_test_backend());
        toolchain_support::rustc_command()
            .arg(backend)
            .arg(toolchain_support::backend_knobs_arg(&["time"]))
            .args([
                "--crate-type=lib",
                "--target=aarch64-apple-darwin",
                "-Copt-level=3",
            ])
            .arg(self.0.join("input.rs"))
            .arg("-o")
            .arg(self.0.join("libinput.rlib"))
            .env("XDG_CACHE_HOME", self.0.join("cache"))
            .output()
            .expect("invoke the pinned compiler with the bridge")
    }
}

impl Drop for Workdir {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

fn compile_and_measure(workdir: &Workdir, lane: &str) -> Cost {
    let output = workdir.compile();
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "{lane} compile of the one-function certificates-on library failed:\n{stderr}"
    );
    let cost = parse_cost(&stderr);
    println!("fixed-cost {lane}: {cost:?}");
    cost
}

#[test]
fn a_trivial_compile_stays_within_its_fixed_cost_budget() {
    // The `time` knob needs the backend knob option; a missing prerequisite
    // fails by name instead of returning early.
    darwin_native::require("fixed_cost_budget_aarch64", &[]);
    let workdir = Workdir::new();
    let cold = compile_and_measure(&workdir, "cold");
    assert!(
        cold.checker_probes <= MAX_CHECKER_PROBES,
        "cold: {cold:?} probes a checker more than once per candidate"
    );
    assert!(
        cold.executable_digests <= MAX_COLD_DIGESTS,
        "cold: {cold:?} digests more executables than the admitted AY (read once, into its \
         copy), its copy, the selected checker and drat-trim"
    );
    assert!(
        cold.solver_starts <= MAX_COLD_SOLVER_STARTS,
        "cold: {cold:?}"
    );
    assert!(
        cold.assessment_spawns <= MAX_COLD_ASSESSMENT_SPAWNS,
        "cold: {cold:?}"
    );

    let warm = compile_and_measure(&workdir, "warm");
    assert!(
        warm.checker_probes <= MAX_CHECKER_PROBES,
        "warm: {warm:?} probes a checker more than once per candidate"
    );
    assert!(
        warm.executable_digests <= MAX_WARM_DIGESTS,
        "warm: {warm:?} digests more executables than the admitted AY, its copy, the \
         selected checker and drat-trim"
    );
    assert!(
        warm.solver_starts <= MAX_WARM_SOLVER_STARTS,
        "warm: {warm:?}"
    );
    assert!(
        warm.assessment_spawns <= MAX_WARM_ASSESSMENT_SPAWNS,
        "warm: {warm:?}"
    );
    println!("fixed-cost budget held: cold {cold:?}, warm {warm:?}");
    positive_evidence::record(
        positive_evidence::Evidence::FixedCost,
        positive_evidence::Certs::On,
    );
}

#[test]
fn the_process_cost_line_parses_every_bounded_field() {
    let cost = parse_cost(
        "noise\nTCG_TIME process_cost checker_probes=2 executable_digests=4 \
         executable_digest_mb=298.4 solver_starts=0 assessment_spawns=1\n",
    );
    assert_eq!(
        cost,
        Cost {
            checker_probes: 2,
            executable_digests: 4,
            solver_starts: 0,
            assessment_spawns: 1,
        }
    );
    positive_evidence::record(
        positive_evidence::Evidence::UnitCheck,
        positive_evidence::Certs::None,
    );
}
